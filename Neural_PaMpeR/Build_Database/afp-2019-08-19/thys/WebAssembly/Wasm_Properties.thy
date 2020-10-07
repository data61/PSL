section \<open>Lemmas for Soundness Proof\<close>

theory Wasm_Properties imports Wasm_Properties_Aux begin

subsection \<open>Preservation\<close>

lemma t_cvt: assumes "cvt t sx v = Some v'" shows "t = typeof v'"
  using assms
  unfolding cvt_def typeof_def
  apply (cases t)
     apply (simp add: option.case_eq_if, metis option.discI option.inject v.simps(17))
    apply (simp add: option.case_eq_if, metis option.discI option.inject v.simps(18))
   apply (simp add: option.case_eq_if, metis option.discI option.inject v.simps(19))
  apply (simp add: option.case_eq_if, metis option.discI option.inject v.simps(20))
  done

lemma store_preserved1:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
          "store_typing s \<S>"
          "\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts')"
          "\<C> = ((s_inst \<S>)!i)\<lparr>local := local ((s_inst \<S>)!i) @ (map typeof vs), label := arb_label, return := arb_return\<rparr>"
          "i < length (s_inst \<S>)"
  shows "store_typing s' \<S>"
  using assms
proof (induction arbitrary: \<C> arb_label arb_return ts ts' rule: reduce.induct)
  case (callcl_host_Some cl t1s t2s f ves vcs n m s hs s' vcs' vs i)
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> ves : (ts _> ts'')" "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : (ts'' _> ts')"
  using callcl_host_Some(8) e_type_comp
  by fastforce
  have ves_c:"const_list ves"
    using is_const_list[OF callcl_host_Some(2)]
    by simp
  then obtain tvs where tvs_def:"ts'' = ts @ tvs"
                                "length t1s = length tvs"
                                "\<S>\<bullet>\<C> \<turnstile> ves : ([] _> tvs)"
    using ts''_def(1) e_type_const_list[of ves \<S> \<C> ts ts''] callcl_host_Some
    by fastforce
  hence "ts'' = ts @ t1s"
        "ts' = ts @ t2s"
    using e_type_callcl_host[OF ts''_def(2) callcl_host_Some(1)]
    by auto
  moreover
  hence "list_all2 types_agree t1s vcs"
    using e_typing_imp_list_types_agree[where ?ts' = "[]"] callcl_host_Some(2) tvs_def(1,3)
    by fastforce
  thus ?case
    using store_extension_imp_store_typing
          host_apply_preserve_store[OF _ callcl_host_Some(6)] callcl_host_Some(7)
    by fastforce
next
  case (set_global s i j v s' vs)
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

  (* Prove that inst, tab and mem are not altered. *)
  have
  "insts = insts'"
  "fs = fs'"
  "clss = clss'"
  "bss = bss'"
    using set_global(1) s_S_defs(1,2)
    unfolding supdate_glob_def supdate_glob_s_def
    by (metis s.ext_inject s.update_convs(5))+
  hence
  "list_all2 (inst_typing \<S>) insts' \<C>s"
  "list_all2 (cl_typing \<S>) fs' tfs"
  "list_all (tab_agree \<S>) (concat clss')"
  "list_all2 (\<lambda>cls n. n \<le> length cls) clss' ns"
  "list_all2 mem_agree bss' ms"
    using set_global(2) s_S_defs
    unfolding store_typing.simps
    by auto
  moreover
  have "list_all2 glob_agree gs' tgs"
  proof -
    have gs_agree:"list_all2 glob_agree gs tgs"
      using set_global(2) s_S_defs
      unfolding store_typing.simps
      by auto
    have "length gs = length gs'"
      using s_S_defs(1,2) set_global(1)
      unfolding supdate_glob_def supdate_glob_s_def
      by (metis length_list_update s.select_convs(5) s.update_convs(5))
    moreover
    obtain k where k_def:"(sglob_ind s i j) = k"
      by blast
    hence "\<And>j'. \<lbrakk>j' \<noteq> k; j' < length gs\<rbrakk> \<Longrightarrow> gs!j' = gs'!j'"
      using s_S_defs(1,2) set_global(1)
      unfolding supdate_glob_def supdate_glob_s_def
      by auto
    hence "\<And>j'. \<lbrakk>j' \<noteq> k; j' < length gs\<rbrakk> \<Longrightarrow> glob_agree (gs'!j') (tgs!j')"
      using gs_agree
      by (metis list_all2_conv_all_nth)
    moreover
    have "glob_agree (gs'!k) (tgs!k)"
    proof -
      obtain ts'' where ts''_def:"\<C> \<turnstile> [C v] : (ts _> ts'')" "\<C> \<turnstile> [Set_global j] : (ts'' _> ts')"
        by (metis b_e_type_comp2_unlift set_global.prems(2))
      have b_es:"ts'' = ts@[typeof v]"
                "ts = ts'"
                "global \<C> ! j = \<lparr>tg_mut = T_mut, tg_t = typeof v\<rparr>"
                "j < length (global \<C>)"
        using b_e_type_value[OF ts''_def(1)] b_e_type_set_global[OF ts''_def(2)]
        by auto
      hence "j < length (global ((s_inst \<S>)!i))"
        using set_global(4)
        by fastforce
      hence globs_agree:"k < length (s_globs \<S>)"
                        "glob_agree (gs!k) (tgs!k)"
                        "(tgs!k) = (global \<C>)!j"
        using store_typing_imp_glob_agree[OF set_global(2,5)] b_es(4) s_S_defs(1,3) k_def set_global(4)
        unfolding sglob_def
        by auto
      hence "g_mut (gs!k) = T_mut"
            "typeof (g_val (gs!k)) = typeof v"
        using b_es(3)
        unfolding glob_agree_def
        by auto
      hence "g_mut (gs'!k) = T_mut"
            "typeof (g_val (gs'!k)) = typeof v"
        using set_global(1) k_def globs_agree(1) store_typing_imp_glob_length_eq[OF set_global(2)] s_S_defs(1,2)
        unfolding supdate_glob_def supdate_glob_s_def
        by auto
      thus ?thesis
        using globs_agree(3) b_es(3)
        unfolding glob_agree_def
        by fastforce 
    qed
    ultimately
    show ?thesis
      using gs_agree
      unfolding list_all2_conv_all_nth
      by fastforce
  qed
  ultimately
  show ?case
    using store_typing.intros
    by simp
next
  (* The following are all special cases of store_preserved_mem. *)
  case (store_Some t v s i j m k off mem' vs a)
  show ?case
    using store_preserved_mem[OF store_Some(5) _ _ store_Some(3)] store_size[OF store_Some(4)]
    by fastforce
next
  case (store_packed_Some t v s i j m k off tp mem' vs a)
  thus ?case
    using store_preserved_mem[OF store_packed_Some(5) _ _ store_packed_Some(3)] store_packed_size[OF store_packed_Some(4)]
    by simp
next
  case (grow_memory s i j n mem c mem' vs)
  show ?case
    using store_preserved_mem[OF grow_memory(5)_ _ grow_memory(2)] mem_grow_size[OF grow_memory(4)]
    by simp
next
  case (label s vs es i s' vs' es' k lholed les les')
  obtain \<C>' t1s t2s arb_label' arb_return' where es_def:"\<C>' = \<C>\<lparr>label := arb_label', return := arb_return'\<rparr>" "\<S>\<bullet>\<C>' \<turnstile> es : (t1s _> t2s)"
    using types_exist_lfilled_weak[OF label(2,6)]
    by fastforce
  thus ?case
    using label(4)[OF label(5) es_def(2) _ label(8)] label(7)
    by fastforce
next
  case (local s vs es i s' vs' es' v0s n j)
  obtain tls where t_local:"(\<S>\<bullet>((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i)) @ (map typeof vs), return := Some tls\<rparr> \<turnstile> es : ([] _> tls))"
                           "ts' = ts @ tls" "i < length (s_inst \<S>)"
    using e_type_local[OF local(4)]
    by blast+
  show ?case
    using local(2)[OF local(3) t_local(1) _ t_local(3), of "(Some tls)" "label ((s_inst \<S>)!i)" ]
    by fastforce
qed (simp_all)

lemma store_preserved:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
          "store_typing s \<S>"
          "\<S>\<bullet>None \<tturnstile>_i vs;es : ts"
  shows "store_typing s' \<S>"
proof -
  show ?thesis
    using store_preserved1[OF assms(1,2), of _ "[]" "ts" None "label (s_inst \<S>!i)"]
          s_type_unfold[OF assms(3)]
    by fastforce
qed

lemma typeof_unop_testop:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v, $e] : (ts _> ts')"
          "(e = (Unop_i t iop)) \<or> (e = (Unop_f t fop)) \<or> (e = (Testop t testop))"
  shows "(typeof v) = t"
        "e = (Unop_f t fop) \<Longrightarrow> is_float_t t"
proof -
  have  "\<C> \<turnstile> [C v, e] : (ts _> ts')"
    using unlift_b_e assms(1)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [C v] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[C v]"]
    by fastforce
  show "(typeof v) = t" "e = (Unop_f t fop) \<Longrightarrow> is_float_t t"
    using b_e_type_value[OF ts''_def(1)] assms(2) b_e_type_unop_testop[OF ts''_def(2)]
    by simp_all
qed

lemma typeof_cvtop:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v, $e] : (ts _> ts')"
          "e = Cvtop t1 cvtop t sx"
  shows "(typeof v) = t"
        "cvtop = Convert \<Longrightarrow> (t1 \<noteq> t) \<and> ((sx = None) = ((is_float_t t1 \<and> is_float_t t) \<or> (is_int_t t1 \<and> is_int_t t \<and> (t_length t1 < t_length t))))"
        "cvtop = Reinterpret \<Longrightarrow> (t1 \<noteq> t) \<and> t_length t1 = t_length t"
proof -
  have  "\<C> \<turnstile> [C v, e] : (ts _> ts')"
    using unlift_b_e assms(1)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [C v] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[C v]"]
    by fastforce
  show "(typeof v) = t"
       "cvtop = Convert \<Longrightarrow> (t1 \<noteq> t) \<and> (sx = None) = ((is_float_t t1 \<and> is_float_t t) \<or> (is_int_t t1 \<and> is_int_t t \<and> (t_length t1 < t_length t)))"
       "cvtop = Reinterpret \<Longrightarrow> (t1 \<noteq> t) \<and> t_length t1 = t_length t"
    using b_e_type_value[OF ts''_def(1)] b_e_type_cvtop[OF ts''_def(2) assms(2)]
    by simp_all
qed

lemma types_preserved_unop_testop_cvtop:
  assumes "\<lparr>[$C v, $e]\<rparr> \<leadsto> \<lparr>[$C v']\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [$C v, $e] : (ts _> ts')"
          "(e = (Unop_i t iop)) \<or> (e = (Unop_f t fop)) \<or> (e = (Testop t testop))  \<or> (e = (Cvtop t2 cvtop t sx))"
  shows "\<S>\<bullet>\<C> \<turnstile> [$C v'] : (ts _> ts')"
proof -
  have  "\<C> \<turnstile> [C v, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [C v] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[C v]"]
    by fastforce
  have "ts@[arity_1_result e] = ts'" "(typeof v) = t"
    using b_e_type_value[OF ts''_def(1)] assms(3) b_e_type_unop_testop(1)[OF ts''_def(2)]
          b_e_type_cvtop(1)[OF ts''_def(2)]
    by (metis butlast_snoc, metis last_snoc)
  moreover
  have "arity_1_result e = typeof (v')"
    using assms(1,3)
    apply (cases rule: reduce_simple.cases)
             apply (simp_all add: arity_1_result_def wasm_deserialise_type t_cvt)
           apply (auto simp add: typeof_def)
    done
  hence "\<C> \<turnstile> [C v'] : ([] _> [arity_1_result e])"
    using b_e_typing.const
    by metis
  ultimately
  show "\<S>\<bullet>\<C> \<turnstile> [$C v'] : (ts _> ts')"
    using e_typing_s_typing.intros(1)
          b_e_typing.weakening[of \<C> "[C v']" "[]" "[arity_1_result e]" ts]
    by fastforce
qed

lemma typeof_binop_relop:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v1, $C v2, $e] : (ts _> ts')"
          "e = Binop_i t iop \<or> e = Binop_f t fop \<or> e = Relop_i t irop \<or> e = Relop_f t frop"
  shows "typeof v1 = t"
        "typeof v2 = t"
        "e = Binop_f t fop \<Longrightarrow> is_float_t t"
        "e = Relop_f t frop \<Longrightarrow> is_float_t t"
proof -
  have "\<C> \<turnstile> [C v1, C v2, e] : (ts _> ts')"
    using unlift_b_e assms(1)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [C v1, C v2] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[C v1, C v2]"]
    by fastforce
  then obtain ts_id where ts_id_def:"ts_id@[t,t] = ts''" "ts' = ts_id @ [arity_2_result e]"
                                    "e = Binop_f t fop \<Longrightarrow> is_float_t t"
                                    "e = Relop_f t frop \<Longrightarrow> is_float_t t"
    using assms(2) b_e_type_binop_relop[of \<C> e ts'' ts' t]
    by blast
  thus "typeof v1 = t"
       "typeof v2 = t"
       "e = Binop_f t fop \<Longrightarrow> is_float_t t"
       "e = Relop_f t frop \<Longrightarrow> is_float_t t"
    using ts''_def b_e_type_comp[of \<C> "[C v1]" "C v2" ts ts''] b_e_type_value2
    by fastforce+
qed

lemma types_preserved_binop_relop:
  assumes "\<lparr>[$C v1, $C v2, $e]\<rparr> \<leadsto> \<lparr>[$C v']\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [$C v1, $C v2, $e] : (ts _> ts')"
          "e = Binop_i t iop \<or> e = Binop_f t fop \<or> e = Relop_i t irop \<or> e = Relop_f t frop"
  shows "\<S>\<bullet>\<C> \<turnstile> [$C v'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [C v1, C v2, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [C v1, C v2] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[C v1, C v2]"]
    by fastforce
  then obtain ts_id where ts_id_def:"ts_id@[t,t] = ts''" "ts' = ts_id @ [arity_2_result e]"
    using assms(3) b_e_type_binop_relop[of \<C> e ts'' ts' t]
    by blast
  hence "\<C> \<turnstile> [C v1] : (ts _> ts_id@[t])"
    using ts''_def b_e_type_comp[of \<C> "[C v1]" "C v2" ts ts''] b_e_type_value
      by fastforce
  hence "ts@[arity_2_result e] = ts'"
    using b_e_type_value ts_id_def(2)
    by fastforce
  moreover
  have "arity_2_result e = typeof (v')"
    using assms(1,3)
    by (cases rule: reduce_simple.cases) (auto simp add: arity_2_result_def typeof_def)
  hence "\<C> \<turnstile> [C v'] : ([] _> [arity_2_result e])"
    using b_e_typing.const
    by metis
  ultimately show ?thesis
    using e_typing_s_typing.intros(1)
          b_e_typing.weakening[of \<C> "[C v']" "[]" "[arity_2_result e]" ts]
    by fastforce
qed

lemma types_preserved_drop:
  assumes "\<lparr>[$C v, $e]\<rparr> \<leadsto> \<lparr>[]\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [$C v, $e] : (ts _> ts')"
          "(e = (Drop))"
  shows "\<S>\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [C v, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [C v] : (ts _> ts'')" "\<C> \<turnstile> [e] : (ts'' _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[C v]"]
    by fastforce
  hence "ts'' = ts@[typeof v]"
    using b_e_type_value
    by blast
  hence "ts = ts'"
    using ts''_def assms(3) b_e_type_drop
    by blast
  hence "\<C> \<turnstile> [] : (ts _> ts')"
    using b_e_type_empty
    by simp
  thus ?thesis
    using e_typing_s_typing.intros(1)
    by fastforce
qed

lemma types_preserved_select:
  assumes "\<lparr>[$C v1, $C v2, $C vn, $e]\<rparr> \<leadsto> \<lparr>[$C v3]\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [$C v1, $C v2, $C vn, $e] : (ts _> ts')"
          "(e = Select)"
  shows "\<S>\<bullet>\<C> \<turnstile> [$C v3] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [C v1, C v2, C vn, e] : (ts _> ts')"
    using unlift_b_e assms(2)
    by simp
  then obtain t1s where t1s_def:"\<C> \<turnstile> [C v1, C v2, C vn] : (ts _> t1s)" "\<C> \<turnstile> [e] : (t1s _> ts')"
    using b_e_type_comp[where ?e = e and ?es = "[C v1, C v2, C vn]"]
    by fastforce
  then obtain t2s t where t2s_def:"t1s = t2s @ [t, t, (T_i32)]" "ts' = t2s@[t]"
    using b_e_type_select[of \<C> e t1s] assms
    by fastforce
  hence "\<C> \<turnstile> [C v1, C v2] : (ts _> t2s@[t,t])"
    using t1s_def t2s_def b_e_type_value_list[of \<C> "[C v1, C v2]" "vn" ts "t2s@[t,t]"]
    by fastforce
  hence v2_t_def:"\<C> \<turnstile> [C v1] : (ts _> t2s@[t])" "typeof v2 = t"
    using t1s_def t2s_def b_e_type_value_list[of \<C> "[C v1]" "v2" ts "t2s@[t]"]
    by fastforce+
  hence v1_t_def:"ts = t2s" "typeof v1 = t"
    using b_e_type_value
    by fastforce+
  have "typeof v3 = t"
    using assms(1) v2_t_def(2) v1_t_def(2)
    by (cases rule: reduce_simple.cases, simp_all)
  hence "\<C> \<turnstile> [C v3] : (ts _> ts')"
    using b_e_typing.const b_e_typing.weakening t2s_def(2) v1_t_def(1)
    by fastforce
  thus ?thesis
    using e_typing_s_typing.intros(1)
    by fastforce
qed

lemma types_preserved_block:
  assumes "\<lparr>vs @ [$Block (tn _> tm) es]\<rparr> \<leadsto> \<lparr>[Label m [] (vs @ ($* es))]\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> vs @ [$Block (tn _> tm) es] : (ts _> ts')"
          "const_list vs"
          "length vs = n"
          "length tn = n"
          "length tm = m"
  shows "\<S>\<bullet>\<C> \<turnstile> [Label m [] (vs @ ($* es))] : (ts _> ts')"
proof -
  obtain \<C>' where c_def:"\<C>' = \<C>\<lparr>label := [tm] @ label \<C>\<rparr>" by blast
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> vs : (ts _> ts'')" "\<S>\<bullet>\<C> \<turnstile> [$Block (tn _> tm) es] : (ts'' _> ts')"
    using assms(2) e_type_comp[of \<S> \<C> vs "$Block (tn _> tm) es" ts ts']
    by fastforce
  hence "\<C> \<turnstile> [Block (tn _> tm) es] : (ts'' _> ts')"
    using unlift_b_e
    by auto
  then obtain ts_c tfn tfm where ts_c_def:"(tn _> tm) = (tfn _> tfm)" "ts'' = ts_c@tfn" "ts' = ts_c@tfm" " (\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> es : (tn _> tm))"
    using b_e_type_block[of \<C> "Block (tn _> tm) es" ts'' ts' "(tn _> tm)" es]
    by fastforce
  hence tfn_l:"length tfn = n"
    using assms(5)
    by simp
  obtain tvs' where tvs'_def:"ts'' = ts@tvs'" "length tvs' = n" "\<S>\<bullet>\<C>' \<turnstile> vs : ([] _> tvs')"
    using e_type_const_list assms(3,4) ts''_def(1)
    by fastforce
  hence "\<S>\<bullet>\<C>' \<turnstile> vs : ([] _> tn)" "\<S>\<bullet>\<C>' \<turnstile> $*es : (tn _> tm)"
    using ts_c_def tvs'_def tfn_l ts''_def c_def e_typing_s_typing.intros(1)
    by simp_all
  hence "\<S>\<bullet>\<C>' \<turnstile> (vs @ ($* es)) : ([] _> tm)" using e_type_comp_conc
    by simp
  moreover
  have "\<S>\<bullet>\<C> \<turnstile> [] : (tm _> tm)"
    using b_e_type_empty[of \<C> "[]" "[]"]
          e_typing_s_typing.intros(1)[where ?b_es = "[]"]
          e_typing_s_typing.intros(3)[of \<S> \<C> "[]" "[]" "[]" "tm"]
    by fastforce
  ultimately
  show ?thesis
    using e_typing_s_typing.intros(7)[of \<S> \<C> "[]" tm _ "vs @ ($* es)" m]
          ts_c_def tvs'_def assms(5,6) e_typing_s_typing.intros(3) c_def
    by fastforce
qed

lemma types_preserved_if:
  assumes "\<lparr>[$C ConstInt32 n, $If tf e1s e2s]\<rparr> \<leadsto> \<lparr>[$Block tf es']\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 n, $If tf e1s e2s] : (ts _> ts')"
  shows   "\<S>\<bullet>\<C> \<turnstile> [$Block tf es'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [C ConstInt32 n, If tf e1s e2s] : (ts _> ts')"
    using unlift_b_e assms(2)
    by fastforce
  then obtain ts_i where ts_i_def:"\<C> \<turnstile> [C ConstInt32 n] : (ts _> ts_i)" "\<C> \<turnstile> [If tf e1s e2s] : (ts_i _> ts')"
    using b_e_type_comp
    by (metis append_Cons append_Nil)
  then obtain ts'' tfn tfm where ts_def:"tf = (tfn _> tfm)"
                                        "ts_i = ts''@tfn @ [T_i32]"
                                        "ts' = ts''@tfm"
                                        "(\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> e1s : tf)"
                                        "(\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> e2s : tf)"
    using b_e_type_if[of \<C> "If tf e1s e2s"]
    by fastforce
  have "ts_i = ts @ [(T_i32)]"
    using ts_i_def(1) b_e_type_value
    unfolding typeof_def
    by fastforce
  moreover
  have "(\<C>\<lparr>label := [tfm] @ label \<C>\<rparr> \<turnstile> es' : (tfn _> tfm))"
    using assms(1) ts_def(4,5) ts_def(1)
    by (cases rule: reduce_simple.cases, simp_all)
  hence "\<C> \<turnstile> [Block tf es'] : (tfn _> tfm)"
    using ts_def(1) b_e_typing.block[of tf tfn tfm \<C> es']
    by simp
  ultimately
  show ?thesis
    using ts_def(2,3) e_typing_s_typing.intros(1,3)
    by fastforce
qed

lemma types_preserved_tee_local:
  assumes "\<lparr>[v, $Tee_local i]\<rparr> \<leadsto> \<lparr>[v, v, $Set_local i]\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [v, $Tee_local i] : (ts _> ts')"
          "is_const v"
  shows   "\<S>\<bullet>\<C> \<turnstile> [v, v, $Set_local i] : (ts _> ts')"
proof -
  obtain bv where bv_def:"v = $C bv"
    using e_type_const_unwrap assms(3)
    by fastforce
  hence "\<C> \<turnstile> [C bv, Tee_local i] : (ts _> ts')"
    using unlift_b_e assms(2)
    by fastforce
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [C bv] : (ts _> ts'')" "\<C> \<turnstile> [Tee_local i] : (ts'' _> ts')"
    using b_e_type_comp[of _ "[C bv]" "Tee_local i"]
    by fastforce
  then obtain ts_c t where ts_c_def:"ts'' = ts_c@[t]" "ts' = ts_c@[t]" "(local \<C>)!i = t" "i < length(local \<C>)"
    using b_e_type_tee_local[of \<C> "Tee_local i" ts'' ts' i]
    by fastforce
  hence t_bv:"t = typeof bv" "ts = ts_c"
    using b_e_type_value ts''_def
    by fastforce+
  have "\<C> \<turnstile> [Set_local i] : ([t,t] _> [t])"
    using ts_c_def(3,4) b_e_typing.set_local[of i \<C> t]
          b_e_typing.weakening[of \<C> "[Set_local i]" "[t]" "[]" "[t]"]
    by fastforce
  moreover
  have "\<C> \<turnstile> [C bv] : ([t] _> [t,t])"
    using t_bv b_e_typing.const[of \<C> bv]  b_e_typing.weakening[of \<C> "[C bv]" "[]" "[t]" "[t]"]
    by fastforce
  hence "\<C> \<turnstile> [C bv, C bv] : ([] _> [t,t])"
    using t_bv b_e_typing.const[of \<C> bv]  b_e_typing.composition[of \<C> "[C bv]" "[]" "[t]"]
    by fastforce
  ultimately
  have "\<C> \<turnstile> [C bv, C bv, Set_local i] : (ts _> ts@[t])"
    using b_e_typing.composition b_e_typing.weakening[of \<C> "[C bv, C bv, Set_local i]"]
    by fastforce
  thus ?thesis
    using t_bv(2) ts_c_def(2) bv_def e_typing_s_typing.intros(1)
    by fastforce
qed

lemma types_preserved_loop:
  assumes "\<lparr>vs @ [$Loop (t1s _> t2s) es]\<rparr> \<leadsto> \<lparr>[Label n [$Loop (t1s _> t2s) es] (vs @ ($* es))]\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> vs @ [$Loop (t1s _> t2s) es] : (ts _> ts')"
          "const_list vs"
          "length vs = n"
          "length t1s = n"
          "length t2s = m"
  shows "\<S>\<bullet>\<C> \<turnstile> [Label n [$Loop (t1s _> t2s) es] (vs @ ($* es))] : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> vs : (ts _> ts'')" "\<S>\<bullet>\<C> \<turnstile> [$Loop (t1s _> t2s) es] : (ts'' _> ts')"
    using assms(2) e_type_comp
    by fastforce
  then have "\<C> \<turnstile> [Loop (t1s _> t2s) es] : (ts'' _> ts')"
    using unlift_b_e assms(2)
    by fastforce
  then obtain ts_c tfn tfm \<C>' where t_loop:"(t1s _> t2s) = (tfn _> tfm)"
                                           "(ts'' = ts_c@tfn)"
                                           "(ts' = ts_c@tfm)"
                                           "\<C>' = \<C>\<lparr>label := [t1s] @ label \<C>\<rparr>"
                                           "(\<C>' \<turnstile> es : (tfn _> tfm))"
    using b_e_type_loop[of \<C> "Loop (t1s _> t2s) es" ts'' ts']
    by fastforce
  obtain tvs where tvs_def:"ts'' = ts @ tvs" "length vs = length tvs" "\<S>\<bullet>\<C>' \<turnstile> vs : ([] _> tvs)"
    using e_type_const_list assms(3) ts''_def(1)
    by fastforce
  then have tvs_eq:"tvs = t1s" "tfn = t1s"
    using assms(4,5) t_loop(1,2)
    by simp_all
  have "\<S>\<bullet>\<C> \<turnstile> [$Loop (t1s _> t2s) es] : (t1s _> t2s)"
    using t_loop b_e_typing.loop e_typing_s_typing.intros(1)
    by fastforce
  moreover
  have "\<S>\<bullet>\<C>' \<turnstile> $*es : (t1s _> t2s)"
    using t_loop e_typing_s_typing.intros(1)
    by fastforce
  then have "\<S>\<bullet>\<C>' \<turnstile> vs@($*es) : ([] _> t2s)"
    using tvs_eq tvs_def(3) e_type_comp_conc
    by blast
  ultimately
  have "\<S>\<bullet>\<C> \<turnstile> [Label n [$Loop (t1s _> t2s) es] (vs @ ($* es))] : ([] _> t2s)"
    using e_typing_s_typing.intros(7)[of \<S> \<C> "[$Loop (t1s _> t2s) es]" t1s t2s "vs @ ($* es)"]
          t_loop(4) assms(5)
    by fastforce
  then show ?thesis
    using t_loop e_typing_s_typing.intros(3) tvs_def(1) tvs_eq(1)
    by fastforce
qed

lemma types_preserved_label_value:
  assumes "\<lparr>[Label n es0 vs]\<rparr> \<leadsto> \<lparr>vs\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [Label n es0 vs] : (ts _> ts')"
          "const_list vs"
  shows "\<S>\<bullet>\<C> \<turnstile> vs : (ts _> ts')"
proof -
  obtain tls t2s where t2s_def:"(ts' = (ts@t2s))"
                           "(\<S>\<bullet>\<C> \<turnstile> es0 : (tls _> t2s))"
                           "(\<S>\<bullet>\<C>\<lparr>label := [tls] @ (label \<C>)\<rparr> \<turnstile> vs : ([] _> t2s))"
    using assms e_type_label
    by fastforce
  thus ?thesis
    using e_type_const_list[of vs \<S> "\<C>\<lparr>label := [tls] @ (label \<C>)\<rparr>" "[]" t2s]
          assms(3) e_typing_s_typing.intros(3)
    by fastforce
qed

lemma types_preserved_br_if:
  assumes "\<lparr>[$C ConstInt32 n, $Br_if i]\<rparr> \<leadsto> \<lparr>e\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 n, $Br_if i] : (ts _> ts')"
          "e = [$Br i] \<or> e = []"
  shows   "\<S>\<bullet>\<C> \<turnstile> e : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [C ConstInt32 n, Br_if i] : (ts _> ts')"
    using unlift_b_e assms(2)
    by fastforce
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [C ConstInt32 n] : (ts _> ts'')" "\<C> \<turnstile> [Br_if i] : (ts'' _> ts')"
  using b_e_type_comp[of _ "[C ConstInt32 n]" "Br_if i"]
  by fastforce
  then obtain ts_c ts_b where ts_bc_def:"i < length(label \<C>)"
                                        "ts'' = ts_c @ ts_b @ [T_i32]"
                                        "ts' = ts_c @ ts_b"
                                        "(label \<C>)!i = ts_b"
    using b_e_type_br_if[of \<C> "Br_if i" ts'' ts' i]
    by fastforce
  hence ts_def:"ts = ts_c @ ts_b"
    using ts''_def(1) b_e_type_value
    by fastforce
  show ?thesis
    using assms(3)
  proof (rule disjE)
    assume "e = [$Br i]"
    thus ?thesis
      using ts_def e_typing_s_typing.intros(1) b_e_typing.br ts_bc_def
      by fastforce
  next
    assume "e = []"
    thus ?thesis
      using ts_def b_e_type_empty ts_bc_def(3)
      e_typing_s_typing.intros(1)[of _ "[]" "(ts _> ts')"]
      by fastforce
  qed
qed

lemma types_preserved_br_table:
  assumes "\<lparr>[$C ConstInt32 c, $Br_table is i]\<rparr> \<leadsto> \<lparr>[$Br i']\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 c, $Br_table is i] : (ts _> ts')"
          "(i' = (is ! nat_of_int c) \<and> length is > nat_of_int c) \<or> i' = i"
  shows "\<S>\<bullet>\<C> \<turnstile> [$Br i'] : (ts _> ts')"
proof -
  have "\<C> \<turnstile> [C ConstInt32 c, Br_table is i] : (ts _> ts')"
    using unlift_b_e assms(2)
    by fastforce
  then obtain ts'' where ts''_def:"\<C> \<turnstile> [C ConstInt32 c] : (ts _> ts'')" "\<C> \<turnstile> [Br_table is i] : (ts'' _> ts')"
    using b_e_type_comp[of _ "[C ConstInt32 c]" "Br_table is i"]
    by fastforce
  then obtain ts_l ts_c where ts_c_def:"list_all (\<lambda>i. i < length(label \<C>) \<and> (label \<C>)!i = ts_l) (is@[i])"
                                       "ts'' = ts_c @ ts_l@[T_i32]"
    using b_e_type_br_table[of \<C> "Br_table is i" ts'' ts']
    by fastforce
  hence ts_def:"ts = ts_c @ ts_l"
    using ts''_def(1) b_e_type_value
    by fastforce
  have "\<C> \<turnstile> [Br i'] : (ts _> ts')"
    using assms(3) ts_c_def(1,2) b_e_typing.br[of i' \<C> ts_l ts_c ts'] ts_def
    unfolding list_all_length
    by (fastforce simp add: less_Suc_eq nth_append)
  thus ?thesis
    using e_typing_s_typing.intros(1)
    by fastforce
qed

lemma types_preserved_local_const:
  assumes "\<lparr>[Local n i vs es]\<rparr> \<leadsto> \<lparr>es\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [Local n i vs es] : (ts _> ts')"
          "const_list es"
  shows "\<S>\<bullet>\<C> \<turnstile> es: (ts _> ts')"
proof -
  obtain tls where "(\<S>\<bullet>((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i)) @ (map typeof vs), return := Some tls\<rparr> \<turnstile> es : ([] _> tls))"
                   "ts' = ts @ tls"
    using e_type_local[OF assms(2)]
    by blast+
  moreover
  then have "\<S>\<bullet>\<C> \<turnstile> es : ([] _> tls)"
    using assms(3) e_type_const_list
    by fastforce
  ultimately
  show ?thesis
    using e_typing_s_typing.intros(3)
    by fastforce
qed

lemma typing_map_typeof:
  assumes "ves = $$* vs"
          "\<S>\<bullet>\<C> \<turnstile> ves : ([] _> tvs)"
  shows "tvs = map typeof vs"
  using assms
proof (induction ves arbitrary: vs tvs rule: List.rev_induct)
  case Nil
  hence "\<C> \<turnstile> [] : ([] _> tvs)"
    using unlift_b_e
    by auto
  thus ?case
    using Nil
    by auto
next
  case (snoc a ves)
  obtain vs' v' where vs'_def:"ves @ [a] = $$* (vs'@[v'])" "vs = vs'@[v']"
    using snoc(2)
    by (metis Nil_is_map_conv append_is_Nil_conv list.distinct(1) rev_exhaust)
  obtain tvs' where tvs'_def:"\<S>\<bullet>\<C> \<turnstile> ves: ([] _> tvs')" "\<S>\<bullet>\<C> \<turnstile> [a] : (tvs' _> tvs)"
    using snoc(3) e_type_comp
    by fastforce
  hence "tvs' = map typeof vs'"
    using snoc(1) vs'_def
    by fastforce
  moreover
  have "is_const a"
    using vs'_def
    unfolding is_const_def
    by auto
  then obtain t where t_def:"tvs = tvs' @ [t]" "\<S>\<bullet>\<C> \<turnstile> [a] : ([] _> [t])"
    using tvs'_def(2)  e_type_const[of a \<S> \<C> tvs' tvs]
    by fastforce
  have "a = $ C v'"
    using vs'_def(1)
    by auto
  hence "t = typeof v'"
    using t_def unlift_b_e[of \<S> \<C> "[C v']" "([] _> [t])"] b_e_type_value[of \<C> "C v'" "[]" "[t]" v']
    by fastforce
  ultimately
  show ?case
    using vs'_def t_def
    by simp
qed

lemma types_preserved_call_indirect_Some:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 c, $Call_indirect j] : (ts _> ts')"
          "stab s i' (nat_of_int c) = Some cl"
          "stypes s i' j = tf"
          "cl_type cl = tf"
          "store_typing s \<S>"
          "i' < length (inst s)"
          "\<C> = (s_inst \<S> ! i') \<lparr>local := local (s_inst \<S> ! i') @ tvs, label := arb_labs, return := arb_return\<rparr>"
  shows "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : (ts _> ts')"
proof -
  obtain t1s t2s where tf_def:"tf = (t1s _> t2s)"
    using tf.exhaust by blast
  obtain ts'' where ts''_def:"\<C> \<turnstile> [C ConstInt32 c] : (ts _> ts'')"
                             "\<C> \<turnstile> [Call_indirect j] : (ts'' _> ts')"
    using e_type_comp[of \<S> \<C> "[$C ConstInt32 c]" "$Call_indirect j" ts ts']
          assms(1)
          unlift_b_e[of \<S> \<C> "[C ConstInt32 c]"]
          unlift_b_e[of \<S> \<C> "[Call_indirect j]"]
    by fastforce
  hence "ts'' = ts@[(T_i32)]"
    using b_e_type_value
    unfolding typeof_def
    by fastforce
  moreover
  have "i' < length (s_inst \<S>)"
    using assms(5,6) store_typing_imp_inst_length_eq
    by fastforce
  hence stypes_eq:"types_t (s_inst \<S> ! i') = types (inst s ! i')"
    using store_typing_imp_inst_typing[OF assms(5)] store_typing_imp_inst_length_eq[OF assms(5)]
    unfolding inst_typing.simps
    by fastforce
  obtain ts''a where ts''a_def:"j < length (types_t \<C>)"
                               "ts'' = ts''a @ t1s @ [T_i32]"
                               "ts' = ts''a @ t2s"
                               "types_t \<C> ! j = (t1s _> t2s)"
    using b_e_type_call_indirect[OF ts''_def(2), of j] tf_def assms(3,7) stypes_eq
    unfolding stypes_def
    by fastforce
  moreover
  obtain tf' where tf'_def:"cl_typing \<S> cl tf'"
    using assms(2,5,6) stab_typed_some_imp_cl_typed
    by blast
  hence "cl_typing \<S> cl tf"
    using assms(4)
    unfolding cl_typing.simps cl_type_def
    by auto
  hence "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : tf"
    using e_typing_s_typing.intros(6) assms(6,7) ts''a_def(1)
    by fastforce
  ultimately
  show "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : (ts _> ts')"
    using tf_def e_typing_s_typing.intros(3)
    by auto
qed

lemma types_preserved_call_indirect_None:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 c, $Call_indirect j] : (ts _> ts')"
  shows "\<S>\<bullet>\<C> \<turnstile> [Trap] : (ts _> ts')"
  using e_typing_s_typing.intros(4)
  by blast

lemma types_preserved_callcl_native:
  assumes "\<S>\<bullet>\<C> \<turnstile> ves @ [Callcl cl] : (ts _> ts')"
          "cl = Func_native i (t1s _> t2s) tfs es"
          "ves = $$* vs"
          "length vs = n"
          "length tfs = k"
          "length t1s = n"
          "length t2s = m"
          "n_zeros tfs = zs"
          "store_typing s \<S>"
  shows "\<S>\<bullet>\<C> \<turnstile> [Local m i (vs @ zs) [$Block ([] _> t2s) es]] : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> ves : (ts _> ts'')" "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : (ts'' _> ts')"
  using assms(1) e_type_comp
  by fastforce
  have ves_c:"const_list ves"
    using is_const_list[OF assms(3)]
    by simp
  then obtain tvs where tvs_def:"ts'' = ts @ tvs"
                                "length t1s = length tvs"
                                "\<S>\<bullet>\<C> \<turnstile> ves : ([] _> tvs)"
    using ts''_def(1) e_type_const_list[of ves \<S> \<C> ts ts''] assms
    by fastforce    
  obtain ts_c \<C>' where ts_c_def:"(ts'' = ts_c @ t1s)"
                                "(ts' = ts_c @ t2s)"
                                "i < length (s_inst \<S>)"
                                "\<C>' = ((s_inst \<S>)!i)"
                                "(\<C>'\<lparr>local := (local \<C>') @ t1s @ tfs, label := ([t2s] @ (label \<C>')), return := Some t2s\<rparr>  \<turnstile> es : ([] _> t2s))"
    using e_type_callcl_native[OF ts''_def(2) assms(2)]
    by fastforce
  have "inst_typing \<S> (inst s ! i) (s_inst \<S> ! i)"
    using store_typing_imp_inst_length_eq[OF assms(9)] store_typing_imp_inst_typing[OF assms(9)]
          ts_c_def(3)
    by simp
  obtain \<C>'' where c''_def:"\<C>'' = \<C>'\<lparr>local := (local \<C>') @ t1s @ tfs, return := Some t2s\<rparr>"
    by blast
  hence "\<C>''\<lparr>label := ([t2s] @ (label \<C>''))\<rparr>  = \<C>'\<lparr>local := (local \<C>') @ t1s @ tfs, label := ([t2s] @ (label \<C>')), return := Some t2s\<rparr>"
    by fastforce
  hence "\<S>\<bullet>\<C>'' \<turnstile> [$Block ([] _> t2s) es] : ([] _> t2s)"
    using ts_c_def b_e_typing.block[of "([] _> t2s)" "[]" "t2s" _ es] e_typing_s_typing.intros(1)[of _ "[Block ([] _> t2s) es]"]
    by fastforce
  moreover
  have t_eqs:"ts = ts_c" "t1s = tvs"
    using tvs_def(1,2) ts_c_def(1)
    by simp_all
  have 1:"tfs = map typeof zs"
    using n_zeros_typeof assms(8)
    by simp
  have "t1s = map typeof vs"
    using typing_map_typeof assms(3) tvs_def t_eqs
    by fastforce
  hence "(t1s @ tfs) = map typeof (vs @ zs)"
    using 1
    by simp
  ultimately
  have "\<S>\<bullet>Some t2s \<tturnstile>_i (vs @ zs);([$Block ([] _> t2s) es]) : t2s"
    using e_typing_s_typing.intros(8) ts_c_def c''_def
    by fastforce
  thus ?thesis
    using e_typing_s_typing.intros(3,5) ts_c_def t_eqs(1) assms(2,7)
    by fastforce
qed

lemma types_preserved_callcl_host_some:
  assumes "\<S>\<bullet>\<C> \<turnstile> ves @ [Callcl cl] : (ts _> ts')"
          "cl = Func_host (t1s _> t2s) f"
          "ves = $$* vcs"
          "length vcs = n"
          "length t1s = n"
          "length t2s = m"
          "host_apply s (t1s _> t2s) f vcs hs = Some (s', vcs')"
          "store_typing s \<S>"
  shows "\<S>\<bullet>\<C> \<turnstile> $$* vcs' : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> ves : (ts _> ts'')" "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : (ts'' _> ts')"
  using assms(1) e_type_comp
  by fastforce
  have ves_c:"const_list ves"
    using is_const_list[OF assms(3)]
    by simp
  then obtain tvs where tvs_def:"ts'' = ts @ tvs"
                                "length t1s = length tvs"
                                "\<S>\<bullet>\<C> \<turnstile> ves : ([] _> tvs)"
    using ts''_def(1) e_type_const_list[of ves \<S> \<C> ts ts''] assms
    by fastforce
  hence "ts'' = ts @ t1s"
        "ts' = ts @ t2s"
    using e_type_callcl_host[OF ts''_def(2) assms(2)]
    by auto
  moreover
  hence "list_all2 types_agree t1s vcs"
    using e_typing_imp_list_types_agree[where ?ts' = "[]"] assms(3) tvs_def(1,3)
    by fastforce
  hence "\<S>\<bullet>\<C> \<turnstile> $$* vcs' : ([] _> t2s)"
    using list_types_agree_imp_e_typing host_apply_respect_type[OF _ assms(7)]
    by fastforce
  ultimately
  show ?thesis
    using e_typing_s_typing.intros(3)
    by fastforce
qed

lemma types_imp_concat:
  assumes "\<S>\<bullet>\<C> \<turnstile> es @ [e] @ es' : (ts _> ts')"
          "\<And>tes tes'. ((\<S>\<bullet>\<C> \<turnstile> [e] : (tes _> tes')) \<Longrightarrow> (\<S>\<bullet>\<C> \<turnstile> [e'] : (tes _> tes')))"
  shows "\<S>\<bullet>\<C> \<turnstile> es @ [e'] @ es' : (ts _> ts')"
proof -
  obtain ts'' where "\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts'')"
                    "\<S>\<bullet>\<C> \<turnstile> [e] @ es' : (ts'' _> ts')"
    using e_type_comp_conc1[of _ _ es "[e] @ es'"] assms(1)
    by fastforce
  moreover
  then obtain ts''' where "\<S>\<bullet>\<C> \<turnstile> [e] : (ts'' _> ts''')" "\<S>\<bullet>\<C> \<turnstile> es' : (ts''' _> ts')"
    using e_type_comp_conc1[of _ _ "[e]" es' ts'' ts'] assms
    by fastforce
  ultimately
  show ?thesis
    using assms(2) e_type_comp_conc[of _ _ es ts ts'' "[e']" ts''']
                   e_type_comp_conc[of _ _ "es @ [e']" ts ts''']
    by fastforce
qed

lemma type_const_return:
  assumes "Lfilled i lholed (vs @ [$Return]) LI"
          "(return \<C>) = Some tcs"
          "length tcs = length vs"
          "\<S>\<bullet>\<C> \<turnstile> LI : (ts _> ts')"
          "const_list vs"
  shows "\<S>\<bullet>\<C>' \<turnstile> vs : ([] _> tcs)"
  using assms
proof (induction i arbitrary: ts ts' lholed \<C> LI \<C>')
  case 0
  obtain vs' es' where "LI = (vs' @ (vs @ [$Return]) @ es')"
    using Lfilled.simps[of 0 lholed "(vs @ [$Return])" LI] 0(1)
    by fastforce
  then obtain ts'' ts''' where "\<S>\<bullet>\<C> \<turnstile> vs' : (ts _> ts'')"
                               "\<S>\<bullet>\<C> \<turnstile> (vs @ [$Return]) : (ts'' _> ts''')"
                               "\<S>\<bullet>\<C> \<turnstile> es' : (ts''' _> ts')"
    using e_type_comp_conc2[of \<S> \<C> vs' "(vs @ [$Return])" es'] 0(4)
    by fastforce
  then obtain ts_b where ts_b_def:"\<S>\<bullet>\<C> \<turnstile> vs : (ts'' _> ts_b)" "\<S>\<bullet>\<C> \<turnstile> [$Return] : (ts_b _> ts''')"
    using e_type_comp_conc1
    by fastforce
  then obtain ts_c where ts_c_def:"ts_b = ts_c @ tcs" "(return \<C>) = Some tcs"
    using 0(2) b_e_type_return[of \<C>] unlift_b_e[of \<S> \<C> "[Return]" "ts_b _> ts'''"]
    by fastforce
  obtain tcs' where "ts_b = ts'' @ tcs'" "length vs = length tcs'" "\<S>\<bullet>\<C>' \<turnstile> vs : ([] _> tcs')"
    using ts_b_def(1) e_type_const_list 0(5)
    by fastforce
  thus ?case
    using 0(3) ts_c_def
    by simp
next
  case (Suc i)
  obtain vs' n l les les' LK where es_def:"lholed = (LRec vs' n les l les')"
                                           "Lfilled i l (vs @ [$Return]) LK"
                                           "LI = (vs' @ [Label n les LK] @ les')"
    using Lfilled.simps[of "(Suc i)" lholed "(vs @ [$Return])" LI] Suc(2)
    by fastforce
  then obtain ts'' ts''' where "\<S>\<bullet>\<C> \<turnstile> [Label n les LK] : (ts'' _> ts''')"
    using e_type_comp_conc2[of \<S> \<C> vs' "[Label n les LK]" les'] Suc(5)
    by fastforce
  then obtain tls t2s where
       "ts''' = ts'' @ t2s"
       "length tls = n"
       "\<S>\<bullet>\<C> \<turnstile> les : (tls _> t2s)"
       "\<S>\<bullet>\<C>\<lparr>label := [tls] @ label \<C>\<rparr> \<turnstile> LK : ([] _> t2s)"
       "return (\<C>\<lparr>label := [tls] @ label \<C>\<rparr>) = Some tcs"
    using e_type_label[of \<S> \<C> n les LK ts'' ts'''] Suc(3)
    by fastforce
  then show ?case
    using Suc(1)[OF es_def(2) _ assms(3) _ assms(5)]
    by fastforce
qed

lemma types_preserved_return:
  assumes "\<lparr>[Local n i vls LI]\<rparr> \<leadsto> \<lparr>ves\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [Local n i vls LI] : (ts _> ts')"
          "const_list ves"
          "length ves = n"
          "Lfilled j lholed (ves @ [$Return]) LI"
  shows "\<S>\<bullet>\<C> \<turnstile> ves : (ts _> ts')"
proof -
  obtain tls \<C>' where l_def:"i < length (s_inst \<S>)"
                        "\<C>' = ((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i)) @ (map typeof vls), return := Some tls\<rparr>"
                        "\<S>\<bullet>\<C>' \<turnstile> LI : ([] _> tls)"
                        "ts' = ts @ tls"
                        "length tls = n"
    using e_type_local[OF assms(2)]
    by blast
  hence "\<S>\<bullet>\<C> \<turnstile> ves : ([] _> tls)"
    using type_const_return[OF assms(5) _ _ l_def(3)] assms(3-5)
    by fastforce
  thus ?thesis
    using e_typing_s_typing.intros(3) l_def(4)
    by fastforce
qed

lemma type_const_br:
  assumes "Lfilled i lholed (vs @ [$Br (i+k)]) LI"
          "length (label \<C>) > k"
          "(label \<C>)!k = tcs"
          "length tcs = length vs"
          "\<S>\<bullet>\<C> \<turnstile> LI : (ts _> ts')"
          "const_list vs"
  shows "\<S>\<bullet>\<C>' \<turnstile> vs : ([] _> tcs)"
  using assms
proof (induction i arbitrary: k ts ts' lholed \<C> LI \<C>')
  case 0
  obtain vs' es' where "LI = (vs' @ (vs @ [$Br (0+k)]) @ es')"
    using Lfilled.simps[of 0 lholed "(vs @ [$Br (0 + k)])" LI] 0(1)
    by fastforce
  then obtain ts'' ts''' where "\<S>\<bullet>\<C> \<turnstile> vs' : (ts _> ts'')"
                               "\<S>\<bullet>\<C> \<turnstile> (vs @ [$Br (0+k)]) : (ts'' _> ts''')"
                               "\<S>\<bullet>\<C> \<turnstile> es' : (ts''' _> ts')"
    using e_type_comp_conc2[of \<S> \<C> vs' "(vs @ [$Br (0+k)])" es'] 0(5)
    by fastforce
  then obtain ts_b where ts_b_def:"\<S>\<bullet>\<C> \<turnstile> vs : (ts'' _> ts_b)" "\<S>\<bullet>\<C> \<turnstile> [$Br (0+k)] : (ts_b _> ts''')"
    using e_type_comp_conc1
    by fastforce
  then obtain ts_c where ts_c_def:"ts_b = ts_c @ tcs" "(label \<C>)!k = tcs"
    using 0(3) b_e_type_br[of \<C> "Br (0 + k)"] unlift_b_e[of \<S> \<C> "[Br (0 + k)]" "ts_b _> ts'''"]
    by fastforce
  obtain tcs' where "ts_b = ts'' @ tcs'" "length vs = length tcs'" "\<S>\<bullet>\<C>' \<turnstile> vs : ([] _> tcs')"
    using ts_b_def(1) e_type_const_list 0(6)
    by fastforce
  thus ?case
    using 0(4) ts_c_def
    by simp
next
  case (Suc i k ts ts' lholed \<C> LI)
  obtain vs' n l les les' LK where es_def:"lholed = (LRec vs' n les l les')"
                                           "Lfilled i l (vs @ [$Br (i + (Suc k))]) LK"
                                           "LI = (vs' @ [Label n les LK] @ les')"
    using Lfilled.simps[of "(Suc i)" lholed "(vs @ [$Br ((Suc i) + k)])" LI] Suc(2)
    by fastforce
  then obtain ts'' ts''' where "\<S>\<bullet>\<C> \<turnstile> [Label n les LK] : (ts'' _> ts''')"
    using e_type_comp_conc2[of \<S> \<C> vs' "[Label n les LK]" les'] Suc(6)
    by fastforce
  moreover
  then obtain lts \<C>'' ts'''' where "\<S>\<bullet>\<C>'' \<turnstile> LK : ([] _> ts'''')" "\<C>'' = \<C>\<lparr>label := [lts] @ (label \<C>)\<rparr>"
                             "length (label \<C>'') > (Suc k)"
                             "(label \<C>'')!(Suc k) = tcs"
    using e_type_label[of \<S> \<C> n les LK ts'' ts'''] Suc(3,4)
    by fastforce
  then show ?case
    using Suc(1) es_def(2) assms(4,6)
    by fastforce
qed

lemma types_preserved_br:
  assumes "\<lparr>[Label n es0 LI]\<rparr> \<leadsto> \<lparr>vs @ es0\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> [Label n es0 LI] : (ts _> ts')"
          "const_list vs"
          "length vs = n"
          "Lfilled i lholed (vs @ [$Br i]) LI"
  shows "\<S>\<bullet>\<C> \<turnstile> (vs @ es0) : (ts _> ts')"
proof -
  obtain tls t2s \<C>' where l_def:"(ts' = (ts@t2s))"
                            "(\<S>\<bullet>\<C> \<turnstile> es0 : (tls _> t2s))"
                            "\<C>' = \<C>\<lparr>label := [tls] @ (label \<C>)\<rparr>"
                            "length (label \<C>') > 0"
                            "(label \<C>')!0 = tls"
                            "length tls = n"
                            "(\<S>\<bullet>\<C>\<lparr>label := [tls] @ (label \<C>)\<rparr> \<turnstile> LI : ([] _> t2s))"
    using e_type_label[of \<S> \<C> n es0 LI ts ts'] assms(2)
    by fastforce
  hence "\<S>\<bullet>\<C> \<turnstile> vs : ([] _> tls)"
    using assms(3-5) type_const_br[of i lholed vs 0 LI \<C>' tls]
    by fastforce
  thus ?thesis
    using l_def(1,2) e_type_comp_conc e_typing_s_typing.intros(3)
    by fastforce
qed

lemma store_local_label_empty:
  assumes "i < length (s_inst \<S>)"
          "store_typing s \<S>"
  shows "label ((s_inst \<S>)!i) = []" "local ((s_inst \<S>)!i) = []"
proof -
  obtain insts where inst_typ:"list_all2 (inst_typing \<S>) insts (s_inst \<S>)"
    using assms(2)
    unfolding store_typing.simps
    by auto
  thus "label ((s_inst \<S>)!i) = []"
    using assms(1)
    unfolding inst_typing.simps List.list_all2_conv_all_nth
    by fastforce
  show "local ((s_inst \<S>)!i) = []"
    using assms(1) inst_typ
    unfolding inst_typing.simps List.list_all2_conv_all_nth
    by fastforce
qed

lemma types_preserved_b_e1:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
          "store_typing s \<S>"
          "\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts')"
  shows "\<S>\<bullet>\<C> \<turnstile> es' : (ts _> ts')"
  using assms(1)
proof (cases rule: reduce_simple.cases)
  case (unop_i32 c iop)
  thus ?thesis
    using assms(1,3) types_preserved_unop_testop_cvtop
    by simp
next
  case (unop_i64 c iop)
  thus ?thesis
    using assms(1, 3) types_preserved_unop_testop_cvtop
    by simp
next
  case (unop_f32 c fop)
  thus ?thesis
    using assms(1, 3) types_preserved_unop_testop_cvtop
    by simp
next
  case (unop_f64 c fop)
  thus ?thesis
    using assms(1, 3) types_preserved_unop_testop_cvtop
    by simp
next
  case (binop_i32_Some iop c1 c2 c)
  thus ?thesis
    using assms(1, 3) types_preserved_binop_relop
    by simp
next
  case (binop_i32_None iop c1 c2)
  thus ?thesis
    by (simp add: e_typing_s_typing.intros(4))
next
  case (binop_i64_Some iop c1 c2 c)
  thus ?thesis
    using assms(1, 3) types_preserved_binop_relop
    by simp
next
  case (binop_i64_None iop c1 c2)
  thus ?thesis
    by (simp add: e_typing_s_typing.intros(4))
next
  case (binop_f32_Some fop c1 c2 c)
  thus ?thesis
    using assms(1, 3) types_preserved_binop_relop
    by simp
next
  case (binop_f32_None fop c1 c2)
  thus ?thesis
    by (simp add: e_typing_s_typing.intros(4))
next
  case (binop_f64_Some fop c1 c2 c)
  then show ?thesis
    using assms(1, 3) types_preserved_binop_relop
    by simp
next
  case (binop_f64_None fop c1 c2)
  then show ?thesis
    by (simp add: e_typing_s_typing.intros(4))
next
  case (testop_i32 c testop)
  then show ?thesis
    using assms(1, 3) types_preserved_unop_testop_cvtop
    by simp
next
  case (testop_i64 c testop)
  then show ?thesis
    using assms(1, 3) types_preserved_unop_testop_cvtop
    by simp
next
  case (relop_i32 c1 c2 iop)
  then show ?thesis
    using assms(1, 3) types_preserved_binop_relop
    by simp
next
  case (relop_i64 c1 c2 iop)
  then show ?thesis
    using assms(1, 3) types_preserved_binop_relop
    by simp
next
  case (relop_f32 c1 c2 fop)
  then show ?thesis
    using assms(1, 3) types_preserved_binop_relop
    by simp
next
  case (relop_f64 c1 c2 fop)
  then show ?thesis
    using assms(1, 3) types_preserved_binop_relop
    by simp
next
  case (convert_Some t1 v t2 sx v')
  then show ?thesis
    using assms(1, 3) types_preserved_unop_testop_cvtop
    by simp
next
  case (convert_None t1 v t2 sx)
  then show ?thesis
    using e_typing_s_typing.intros(4)
    by simp
next
  case (reinterpret t1 v t2)
  then show ?thesis
    using assms(1, 3) types_preserved_unop_testop_cvtop
    by simp
next
  case unreachable
  then show ?thesis
    using e_typing_s_typing.intros(4)
    by simp
next
  case nop
  then have "\<C> \<turnstile> [Nop] : (ts _> ts')"
    using assms(3) unlift_b_e
    by simp
  then show ?thesis
    using nop b_e_typing.empty e_typing_s_typing.intros(1,3)
    apply (induction "[Nop]" "ts _> ts'" arbitrary: ts ts')
      apply simp_all
     apply (metis list.simps(8))
    apply blast
    done
next
  case (drop v)
  then show ?thesis
    using assms(1, 3) types_preserved_drop
    by simp
next
  case (select_false v1 v2)
  then show ?thesis
    using assms(1, 3) types_preserved_select
    by simp
next
  case (select_true n v1 v2)
  then show ?thesis
    using assms(1, 3) types_preserved_select
    by simp
next
  case (block vs n t1s t2s m es)
  then show ?thesis
    using assms(1, 3) types_preserved_block
    by simp
next
  case (loop vs n t1s t2s m es)
  then show ?thesis
    using assms(1, 3) types_preserved_loop
    by simp
next
  case (if_false tf e1s e2s)
  then show ?thesis
    using assms(1, 3) types_preserved_if
    by simp
next
  case (if_true n tf e1s e2s)
  then show ?thesis
    using assms(1, 3) types_preserved_if
    by simp
next
  case (label_const ts es)
  then show ?thesis
    using assms(1, 3) types_preserved_label_value
    by simp
next
  case (label_trap ts es)
  then show ?thesis
    by (simp add: e_typing_s_typing.intros(4))
next
  case (br vs n i lholed LI es)
  then show ?thesis
    using assms(1, 3) types_preserved_br
    by fastforce
next
  case (br_if_false n i)
  then show ?thesis
    using assms(1, 3) types_preserved_br_if
    by fastforce
next
  case (br_if_true n i)
  then show ?thesis
    using assms(1, 3) types_preserved_br_if
    by fastforce
next
  case (br_table is' c i')
  then show ?thesis
    using assms(1, 3) types_preserved_br_table
    by fastforce
next
  case (br_table_length is' c i')
  then show ?thesis
    using assms(1, 3) types_preserved_br_table
    by fastforce
next
  case (local_const i vs)
  then show ?thesis
    using assms(1, 3) types_preserved_local_const
    by fastforce
next
  case (local_trap i vs)
  then show ?thesis
    by (simp add: e_typing_s_typing.intros(4))
next
  case (return n j lholed es i vls)
  then show ?thesis
    using assms(1, 3) types_preserved_return
    by fastforce
next
  case (tee_local v i)
  then show ?thesis
    using assms(1, 3) types_preserved_tee_local
    by simp
next
  case (trap lholed)
  then show ?thesis
    by (simp add: e_typing_s_typing.intros(4))
qed

lemma types_preserved_b_e:
  assumes "\<lparr>es\<rparr> \<leadsto> \<lparr>es'\<rparr>"
          "store_typing s \<S>"
          "\<S>\<bullet>None \<tturnstile>_i vs;es : ts"
  shows "\<S>\<bullet>None \<tturnstile>_i vs;es' : ts"
proof -
  have "i < (length (s_inst \<S>))"
    using assms(3) s_typing.cases
    by blast
  moreover
  obtain tvs \<C> where defs: "tvs = map typeof vs" "\<C> = ((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i) @ tvs), return := None\<rparr>" "\<S>\<bullet>\<C> \<turnstile> es : ([] _> ts)"
    using assms(3)
    unfolding s_typing.simps
    by blast
  have "\<S>\<bullet>\<C> \<turnstile> es' : ([] _> ts)"
    using assms(1,2) defs(3) types_preserved_b_e1
    by simp
  ultimately show ?thesis
    using defs
    unfolding s_typing.simps
    by auto
qed

lemma types_preserved_store:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 k, $C v, $Store t tp a off] : (ts _> ts')"
  shows "\<S>\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
        "types_agree t v"
proof -
  obtain ts'' ts''' where ts_def:"\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 k] : (ts _> ts'')"
                                 "\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts'' _> ts''')"
                                 "\<S>\<bullet>\<C> \<turnstile> [$Store t tp a off] : (ts''' _> ts')"
    using assms e_type_comp_conc2[of \<S> \<C> "[$C ConstInt32 k]" "[$C v]" "[$Store t tp a off]"]
    by fastforce
  then have "ts'' = ts@[(T_i32)]"
    using b_e_type_value[of \<C> "C ConstInt32 k" "ts" ts'']
          unlift_b_e[of \<S> \<C> "[C (ConstInt32 k)]" "(ts _> ts'')"]
    unfolding typeof_def
    by fastforce
  hence "ts''' = ts@[(T_i32), (typeof v)]"
    using ts_def(2) b_e_type_value[of \<C> "C v" ts'' ts''']
          unlift_b_e[of \<S> \<C> "[C v]" "(ts'' _> ts''')"]
    by fastforce
  hence "ts = ts'" "types_agree t v"
    using ts_def(3) b_e_type_store[of \<C> "Store t tp a off" ts''' ts']
          unlift_b_e[of \<S> \<C> "[Store t tp a off]" "(ts''' _> ts')"]
    unfolding types_agree_def
    by fastforce+
  thus "\<S>\<bullet>\<C> \<turnstile> [] : (ts _> ts')" "types_agree t v"
    using b_e_type_empty[of \<C> "ts" "ts'"] e_typing_s_typing.intros(1)
    by fastforce+
qed

lemma types_preserved_current_memory:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$Current_memory] : (ts _> ts')"
  shows "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 c] : (ts _> ts')"
proof -
  have "ts' = ts@[T_i32]"
    using assms b_e_type_current_memory unlift_b_e[of \<S> \<C> "[Current_memory]"]
    by fastforce
  thus ?thesis
    using b_e_typing.const[of \<C> "ConstInt32 c"] e_typing_s_typing.intros(1,3)
    unfolding typeof_def
    by fastforce
qed

lemma types_preserved_grow_memory:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 c, $Grow_memory] : (ts _> ts')"
  shows "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 c'] : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 c] : (ts _> ts'')" 
                             "\<S>\<bullet>\<C> \<turnstile> [$Grow_memory] : (ts'' _> ts')"
    using e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last.simps list.distinct(1))
  have "ts'' = ts@[(T_i32)]"
    using b_e_type_value[of \<C> "C ConstInt32 c" ts ts'']
          unlift_b_e[of \<S> \<C> "[C ConstInt32 c]"] ts''_def(1)
    unfolding typeof_def
    by fastforce
  moreover
  hence "ts'' = ts'"
    using ts''_def b_e_type_grow_memory[of _ _ ts'' ts'] unlift_b_e[of \<S> \<C> "[Grow_memory]"]
    by fastforce
  ultimately
  show "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 c'] : (ts _> ts')"
    using e_typing_s_typing.intros(1,3)
          b_e_typing.const[of \<C> "ConstInt32 c'"]
    unfolding typeof_def
    by fastforce
qed

lemma types_preserved_set_global:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v, $Set_global j] : (ts _> ts')"
  shows "\<S>\<bullet>\<C> \<turnstile> [] : (ts _> ts')"
        "tg_t (global \<C> ! j) = typeof v"
proof -
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts'')" 
                             "\<S>\<bullet>\<C> \<turnstile> [$Set_global j] : (ts'' _> ts')"
    using e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last.simps list.distinct(1))
  hence "ts'' = ts@[typeof v]"
    using b_e_type_value unlift_b_e[of \<S> \<C> "[C v]"]
    by fastforce
  hence "ts = ts'" "tg_t (global \<C> ! j) = typeof v"
    using b_e_type_set_global ts''_def(2) unlift_b_e[of \<S> \<C> "[Set_global j]"]
    by fastforce+
  thus "\<S>\<bullet>\<C> \<turnstile> [] : (ts _> ts')" "tg_t (global \<C> ! j) = typeof v"
    using b_e_type_empty[of \<C> "ts" "ts'"] e_typing_s_typing.intros(1)
    by fastforce+
qed

lemma types_preserved_load:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 k, $Load t tp a off] : (ts _> ts')"
          "typeof v = t"
  shows "\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')"
proof -
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> [$C ConstInt32 k] : (ts _> ts'')" 
                             "\<S>\<bullet>\<C> \<turnstile> [$Load t tp a off] : (ts'' _> ts')"
    using e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last.simps list.distinct(1))
  hence "ts'' = ts@[(T_i32)]"
    using b_e_type_value unlift_b_e[of \<S> \<C> "[C ConstInt32 k]"]
    unfolding typeof_def
    by fastforce
  hence ts_def:"ts' = ts@[t]" "load_store_t_bounds a (option_projl tp) t" 
    using ts''_def(2) b_e_type_load unlift_b_e[of \<S> \<C> "[Load t tp a off]"]
    by fastforce+
  moreover
  hence "\<C> \<turnstile> [C v] : (ts _> ts@[t])"
    using assms(2) b_e_typing.const b_e_typing.weakening
    by fastforce
  ultimately
  show "\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')"
    using e_typing_s_typing.intros(1)
    by fastforce
qed

lemma types_preserved_get_local:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$Get_local i] : (ts _> ts')"
          "length vi = i"
          "(local \<C>) = map typeof (vi @ [v] @ vs)"
  shows "\<S>\<bullet>\<C> \<turnstile> [$C v] : (ts _> ts')"
proof -
  have "(local \<C>)!i = typeof v"
    using assms(2,3)
    by (metis (no_types, hide_lams) append_Cons length_map list.simps(9) map_append nth_append_length)
  hence "ts' = ts@[typeof v]"
    using assms(1) unlift_b_e[of \<S> \<C> "[Get_local i]"] b_e_type_get_local
    by fastforce
  thus ?thesis
    using b_e_typing.const e_typing_s_typing.intros(1,3)
    by fastforce
qed

lemma types_preserved_set_local:
  assumes "\<S>\<bullet>\<C> \<turnstile> [$C v', $Set_local i] : (ts _> ts')"
          "length vi = i"
          "(local \<C>) = map typeof (vi @ [v] @ vs)"
  shows "(\<S>\<bullet>\<C> \<turnstile> [] : (ts _> ts')) \<and> map typeof (vi @ [v] @ vs) = map typeof (vi @ [v'] @ vs)"
proof -
  have v_type:"(local \<C>)!i = typeof v"
    using assms(2,3)
    by (metis (no_types, hide_lams) append_Cons length_map list.simps(9) map_append nth_append_length)
  obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> [$C v'] : (ts _> ts'')" 
                             "\<S>\<bullet>\<C> \<turnstile> [$Set_local i] : (ts'' _> ts')"
    using e_type_comp assms
    by (metis append_butlast_last_id butlast.simps(2) last.simps list.distinct(1))
  hence "ts'' = ts@[typeof v']"
    using b_e_type_value unlift_b_e[of \<S> \<C> "[C v']"]
    by fastforce
  hence "typeof v = typeof v'" "ts' = ts"
    using v_type b_e_type_set_local[of \<C> "Set_local i" ts'' ts'] ts''_def(2) unlift_b_e[of \<S> \<C> "[Set_local i]"]
    by fastforce+
  thus ?thesis
    using b_e_type_empty[of \<C> "ts" "ts'"] e_typing_s_typing.intros(1)
    by fastforce
qed

lemma types_preserved_get_global:
  assumes "typeof (sglob_val s i j) = tg_t (global \<C> ! j)"
          "\<S>\<bullet>\<C> \<turnstile> [$Get_global j] : (ts _> ts')"
  shows "\<S>\<bullet>\<C> \<turnstile> [$C sglob_val s i j] : (ts _> ts')"
proof -
  have "ts' = ts@[tg_t (global \<C> ! j)]"
    using b_e_type_get_global assms(2) unlift_b_e[of _ _ "[Get_global j]"]
    by fastforce
  thus ?thesis
    using b_e_typing.const[of \<C> "sglob_val s i j"] assms(1) e_typing_s_typing.intros(1,3)
    by fastforce
qed

lemma lholed_same_type:
  assumes "Lfilled k lholed es les"
          "Lfilled k lholed es' les'"
          "\<S>\<bullet>\<C> \<turnstile> les : (ts _> ts')"
          "\<And>arb_labs ts ts'.
           \<S>\<bullet>(\<C>\<lparr>label := arb_labs@(label \<C>)\<rparr>) \<turnstile> es : (ts _> ts')
             \<Longrightarrow> \<S>\<bullet>(\<C>\<lparr>label := arb_labs@(label \<C>)\<rparr>) \<turnstile> es' : (ts _> ts')"
  shows "(\<S>\<bullet>\<C> \<turnstile> les' : (ts _> ts'))"
  using assms
proof (induction arbitrary: ts ts' es' \<C> les' rule: Lfilled.induct)
  case (L0 vs lholed es' es ts ts' es'')
  obtain ts'' ts''' where "\<S>\<bullet>\<C> \<turnstile> vs : (ts _> ts'')"
                          "\<S>\<bullet>\<C> \<turnstile> es : (ts'' _> ts''')"
                          "\<S>\<bullet>\<C> \<turnstile> es' : (ts''' _> ts')"
    using e_type_comp_conc2 L0(4)
    by blast
  moreover
  hence "(\<S>\<bullet>\<C> \<turnstile> es'' : (ts'' _> ts'''))"
    using L0(5)[of "[]" ts'' ts''']
    by fastforce
  ultimately
  have "(\<S>\<bullet>\<C> \<turnstile> vs @ es'' @ es' : (ts _> ts'))"
    using e_type_comp_conc
    by fastforce
  thus ?case
    using L0(2,3) Lfilled.simps[of 0 lholed es'' les']
    by fastforce
next
  case (LN vs lholed n es' l es'' k es lfilledk t1s t2s es''' \<C> les')
  obtain lfilledk' where l'_def:"Lfilled k l es''' lfilledk'" "les' = vs @ [Label n es' lfilledk'] @ es''"
    using LN Lfilled.simps[of "k+1" lholed es''' les']
    by fastforce
  obtain ts' ts'' where lab_def:"\<S>\<bullet>\<C> \<turnstile> vs : (t1s _> ts')"
                                "\<S>\<bullet>\<C> \<turnstile> [Label n es' lfilledk] : (ts' _> ts'')"
                                "\<S>\<bullet>\<C> \<turnstile> es'' : (ts'' _> t2s)"
  using e_type_comp_conc2[OF LN(6)]
  by blast
  obtain tls ts_c \<C>_int where int_def:" ts'' = ts' @ ts_c"
                                 "length tls = n"
                                 "\<S>\<bullet>\<C> \<turnstile> es' : (tls _> ts_c)"
                                 "\<C>_int = \<C>\<lparr>label := [tls] @ label \<C>\<rparr>"
                                 "\<S>\<bullet>\<C>_int \<turnstile> lfilledk : ([] _> ts_c)"
    using e_type_label[OF lab_def(2)]
    by blast
  have "(\<And>\<C>' arb_labs' ts ts'.
        \<C>' = \<C>_int\<lparr>label := arb_labs' @ label \<C>_int\<rparr> \<Longrightarrow>
        \<S>\<bullet>\<C>' \<turnstile> es : (ts _> ts') \<Longrightarrow>
        (\<S>\<bullet>\<C>' \<turnstile> es''' : (ts _> ts')))"
  proof -
    fix \<C>'' arb_labs'' tts tts'
    assume "\<C>'' = \<C>_int\<lparr>label := arb_labs'' @ label \<C>_int\<rparr>"
           "\<S>\<bullet>\<C>'' \<turnstile> es : (tts _> tts')"
    thus "(\<S>\<bullet>\<C>'' \<turnstile> es''' : (tts _> tts'))"
      using LN(7)[of "arb_labs'' @ [tls]" tts tts'] int_def(4)
      by fastforce
  qed
  hence "(\<S>\<bullet>\<C>_int \<turnstile> lfilledk' : ([] _> ts_c))"
    using LN(4)[OF l'_def(1) int_def(5)]
    by fastforce
  hence "(\<S>\<bullet>\<C> \<turnstile> [Label n es' lfilledk'] : (ts' _> ts''))"
    using int_def e_typing_s_typing.intros(3,7)
    by (metis append.right_neutral)
  thus ?case
    using lab_def e_type_comp_conc l'_def(2)
    by blast
qed

lemma types_preserved_e1:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
          "store_typing s \<S>"
          "tvs = map typeof vs"
          "i < length (inst s)"
          "\<C> = ((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i) @ tvs), label := arb_labs, return := arb_return\<rparr>"
          "\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts')"
  shows "(\<S>\<bullet>\<C> \<turnstile> es' : (ts _> ts')) \<and> (map typeof vs = map typeof vs')"
  using assms
proof (induction arbitrary: tvs \<C> ts ts' arb_labs arb_return rule: reduce.induct)
  case (basic e e' s vs i)
  then show ?case
    using types_preserved_b_e1[OF basic(1,2)]
    by fastforce
next
  case (call s vs j i)
  obtain  ts'' tf1 tf2 where l_func_t: "length (func_t \<C>) > j"
                                       "ts = ts''@tf1"
                                       "ts' = ts''@tf2"
                                       "((func_t \<C>)!j) = (tf1 _> tf2)"
    using b_e_type_call[of \<C> "Call j" ts ts' j] call(5)
          unlift_b_e[of _ _ "[Call j]" "(ts _> ts')"]
    by fastforce
  have "i < length (s_inst \<S>)"
    using call(3) store_typing_imp_inst_length_eq[OF call(1)]
    by simp
  moreover
  have "j < length (func_t (s_inst \<S> ! i))"
    using l_func_t(1) call(4)
    by simp
  ultimately
  have "cl_typing \<S> (sfunc s i j) (tf1 _> tf2)"
    using store_typing_imp_func_agree[OF call(1)] l_func_t(4) call(4)
    by fastforce
  thus ?case
    using e_typing_s_typing.intros(3,6) l_func_t
    by fastforce
next
  case (call_indirect_Some s i' c cl j tf vs)
  show ?case
    using types_preserved_call_indirect_Some[OF call_indirect_Some(8,1)]
          call_indirect_Some(2,3,4,6,7)
    by fastforce
next
  case (call_indirect_None s i c cl j vs)
  thus ?case
    using e_typing_s_typing.intros(4)
    by blast
next
  case (callcl_native cl j t1s t2s ts es ves vcs n k m zs s vs i)
  thus ?case
    using types_preserved_callcl_native
    by fastforce
next
  case (callcl_host_Some cl t1s t2s f ves vcs n m s hs s' vcs' vs i)
  thus ?case
    using types_preserved_callcl_host_some
      by fastforce
next
  case (callcl_host_None cl t1s t2s f ves vcs n m s hs vs i)
  thus ?case
    using e_typing_s_typing.intros(4)
    by blast
next
  case (get_local vi j s v vs i)
  hence "i < length (s_inst \<S>)"
    unfolding list_all2_conv_all_nth store_typing.simps
    by fastforce
  then have "local \<C> = tvs"
    using store_local_label_empty assms(2) get_local
    by fastforce
  then show ?case
    using types_preserved_get_local get_local
    by fastforce
next
  case (set_local vi j s v vs v' i)
  hence "i < length (s_inst \<S>)"
    unfolding list_all2_conv_all_nth store_typing.simps
    by fastforce
  hence "local \<C> = tvs"
    using store_local_label_empty assms(2) set_local
    by fastforce
  thus ?case
    using set_local types_preserved_set_local
    by simp
next
  case (get_global s vs j i)
  have "length (global \<C>) > j"
    using b_e_type_get_global get_global(5) unlift_b_e[of _ _ "[Get_global j]" "(ts _> ts')"]
    by fastforce
  hence "glob_agree (sglob s i j) ((global \<C>)!j)"
    using get_global(3,4) store_typing_imp_glob_agree[OF get_global(1)] store_typing_imp_inst_length_eq[OF get_global(1)]
    by fastforce
  hence "typeof (g_val (sglob s i j)) = tg_t (global \<C> ! j)"
    unfolding glob_agree_def
    by simp
  thus ?case
    using get_global(5) types_preserved_get_global
    unfolding glob_agree_def sglob_val_def
    by fastforce
next
  case (set_global s i j v s' vs)
  then show ?case
    using types_preserved_set_global
    by fastforce
next
  case (load_Some s i j m k off t bs vs a)
  then show ?case
    using types_preserved_load(1) wasm_deserialise_type
    by blast
next
  case (load_None s i j m k off t vs a)
  then show ?case
    using e_typing_s_typing.intros(4)
    by blast
next
  case (load_packed_Some s i j m sx k off tp bs vs t a)
  then show ?case
    using types_preserved_load(1) wasm_deserialise_type
    by blast
next
  case (load_packed_None s i j m sx k off tp vs t a)
  then show ?case
    using e_typing_s_typing.intros(4)
    by blast
next
  case (store_Some t v s i j m k off mem' vs a)
  then show ?case
    using types_preserved_store
    by blast
next
  case (store_None t v s i j m k off vs a)
  then show ?case
    using e_typing_s_typing.intros(4)
    by blast
next
  case (store_packed_Some t v s i j m k off tp mem' vs a)
  then show ?case
    using types_preserved_store
    by blast
next
  case (store_packed_None t v s i j m k off tp vs a)
  then show ?case
    using e_typing_s_typing.intros(4)
    by blast
next
  case (current_memory s i j m n vs)
  then show ?case
    using types_preserved_current_memory
    by fastforce
next
  case (grow_memory s i j m n c mem' vs)
  then show ?case
    using types_preserved_grow_memory
    by fastforce
next
  case (grow_memory_fail s i j m n vs c)
  thus ?case
    using types_preserved_grow_memory
    by blast
next
  case (label s vs es i s' vs' es' k lholed les les')
  {
    fix \<C>' arb_labs' ts ts'
    assume local_assms:"\<C>' = \<C>\<lparr>label := arb_labs'@(label \<C>), return := (return \<C>)\<rparr>"
    hence "(\<S>\<bullet>\<C>' \<turnstile> es : (ts _> ts')) \<Longrightarrow> (\<S>\<bullet>\<C>' \<turnstile> es' : (ts _> ts')) \<and> map typeof vs = map typeof vs'"
      using label(4)[OF label(5,6,7)] label(8)
      by fastforce
    hence "(\<S>\<bullet>\<C>\<lparr>label := arb_labs'@(label \<C>)\<rparr> \<turnstile> es : (ts _> ts'))
               \<Longrightarrow> (\<S>\<bullet>\<C>\<lparr>label := arb_labs'@(label \<C>)\<rparr> \<turnstile> es' : (ts _> ts')) \<and>
                     map typeof vs = map typeof vs'"
      using local_assms
      by simp
  }
  hence "\<And>arb_labs' ts ts'. \<S>\<bullet>\<C>\<lparr>label := arb_labs'@(label \<C>)\<rparr> \<turnstile> es : (ts _> ts')
                              \<Longrightarrow> (\<S>\<bullet>\<C>\<lparr>label := arb_labs'@(label \<C>)\<rparr> \<turnstile> es' : (ts _> ts'))"
       "map typeof vs = map typeof vs'"
    using types_exist_lfilled[OF label(2,9)]
    by auto
  thus ?case
    using lholed_same_type[OF label(2,3,9)]
    by fastforce
next
  case (local s vls es i s' vs' es' vs n j)
  obtain \<C>' tls where es_def:"i < length (s_inst \<S>)"
                          "length tls = n"
                          "\<C>' = (s_inst \<S> ! i) \<lparr>local := local(s_inst \<S> ! i) @ map typeof vls, label := label (s_inst \<S> ! i), return := Some tls\<rparr>"
                          "\<S>\<bullet>\<C>' \<turnstile> es : ([] _> tls)"
                          "ts' = ts @ tls"
    using e_type_local[OF local(7)]
    by fastforce
  moreover
  obtain ts'' where "ts' = ts@ts''" "(\<S>\<bullet>(Some ts'') \<tturnstile>_i vls;es : ts'')"
    using e_type_local_shallow local(7)
    by fastforce
  moreover
  have "inst_typing \<S> ((inst s)!i) ((s_inst \<S>)!i)" "i < length (inst s)"
    using local es_def(1)
    unfolding store_typing.simps list_all2_conv_all_nth
    by fastforce+
  ultimately
  have "\<S>\<bullet>\<C>' \<turnstile> es' : ([] _> tls)" "map typeof vls = map typeof vs'"
    using local(2)[OF local(3) _ _ _ es_def(4), of "map typeof vls" "Some tls" "label (s_inst \<S> ! i)"]
    by fastforce+
  hence "\<S>\<bullet>(Some tls) \<tturnstile>_ i vs';es' : tls"
    using e_typing_s_typing.intros(8) es_def(1,3)
    by fastforce
  thus ?case
    using e_typing_s_typing.intros(3,5) es_def(2,5)
    by fastforce
qed

lemma types_preserved_e:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
          "store_typing s \<S>"
          "\<S>\<bullet>None \<tturnstile>_i vs;es : ts"
  shows "\<S>\<bullet>None \<tturnstile>_i vs';es' : ts"
  using assms
proof -
  have "i < (length (s_inst \<S>))"
    using assms(3) s_typing.cases
    by blast
  moreover
  hence i_bound:"i < length (inst s)"
    using assms(2)
    unfolding list_all2_conv_all_nth store_typing.simps
    by fastforce
  obtain tvs \<C> where defs: "tvs = map typeof vs"
                           "\<C> = ((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i) @ tvs), label := (label ((s_inst \<S>)!i)), return := None\<rparr>"
                           "\<S>\<bullet>\<C> \<turnstile> es : ([] _> ts)"
    using assms(3)
    unfolding s_typing.simps
    by fastforce
  have "(\<S>\<bullet>\<C> \<turnstile> es' : ([] _> ts)) \<and> (map typeof vs = map typeof vs')"
    using types_preserved_e1[OF assms(1,2) defs(1) i_bound defs(2,3)]
    by simp
  ultimately show ?thesis
    using defs
    unfolding s_typing.simps
    by auto
qed

subsection \<open>Progress\<close>

lemma const_list_no_progress:
  assumes "const_list es"
  shows "\<not>\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
proof -
  {
    assume "\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
    hence "False"
      using assms
    proof (induction rule: reduce.induct)
      case (basic e e' s vs i)
      thus ?thesis
      proof (induction rule: reduce_simple.induct)
        case (trap es lholed)
        show ?case
          using trap(2)
        proof (cases rule: Lfilled.cases)
          case (L0 vs es')
          thus ?thesis
            using trap(3) list_all_append const_list_cons_last(2)[of vs Trap]
            unfolding const_list_def
            by (simp add: is_const_def)
        next
          case (LN vs n es' l es'' k lfilledk)
          thus ?thesis
            by (simp add: is_const_def)
        qed
      qed (fastforce simp add: const_list_cons_last(2) is_const_def const_list_def)+
    next
      case (label s vs es i s' vs' es' k lholed les les')
      show ?case
        using label(2)
      proof (cases rule: Lfilled.cases)
        case (L0 vs es')
        thus ?thesis
          using label(4,5) list_all_append
          unfolding const_list_def
          by fastforce
      next
        case (LN vs n es' l es'' k lfilledk)
        thus ?thesis
          using label(4,5)
          unfolding const_list_def
          by (simp add: is_const_def)
      qed
    qed (fastforce simp add: const_list_cons_last(2) is_const_def const_list_def)+
  }
  thus ?thesis
    by blast
qed

lemma empty_no_progress:
  assumes "es = []"
  shows "\<not>\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
proof -
  {
    assume "\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
    hence False
      using assms
    proof (induction rule: reduce.induct)
      case (basic e e' s vs i)
      thus ?thesis
      proof (induction rule: reduce_simple.induct)
        case (trap es lholed)
        thus ?case
          using Lfilled.simps[of 0 lholed "[Trap]" es]
          by auto
      qed auto
    next
      case (label s vs es i s' vs' es' k lholed les les')
      thus ?case
          using Lfilled.simps[of k lholed es "[]"]
          by auto
    qed auto
  }
  thus ?thesis
    by blast
qed
      
lemma trap_no_progress:
  assumes "es = [Trap]"
  shows "\<not>\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
proof -
  {
    assume "\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
    hence False
      using assms
    proof (induction rule: reduce.induct)
      case (basic e e' s vs i)
      thus ?case
      by (induction rule: reduce_simple.induct) auto
    next
      case (label s vs es i s' vs' es' k lholed les les')
      show ?case
        using label(2)
        proof (cases rule: Lfilled.cases)
          case (L0 vs es')
          show ?thesis
            using L0(2) label(1,4,5) empty_no_progress
            by (auto simp add: Cons_eq_append_conv)
        next
          case (LN vs n es' l es'' k' lfilledk)
          show ?thesis
            using LN(2) label(5)
            by (simp add: Cons_eq_append_conv)
        qed
    qed auto
  }
  thus ?thesis
    by blast
qed

lemma terminal_no_progress:
  assumes "const_list es \<or> es = [Trap]"
  shows "\<not>\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
  using const_list_no_progress trap_no_progress assms
  by blast

lemma progress_L0:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
          "const_list cs"
  shows "\<lparr>s;vs;cs@es@es_c\<rparr> \<leadsto>_ i \<lparr>s';vs';cs@es'@es_c\<rparr>"
proof -
  have "\<And>es. Lfilled 0 (LBase cs es_c) es (cs@es@es_c)"
    using Lfilled.intros(1)[of cs "(LBase cs es_c)" es_c] assms(2)
    unfolding const_list_def
    by fastforce
  thus ?thesis
    using reduce.intros(23) assms(1)
    by blast
qed

lemma progress_L0_left:
  assumes "\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';es'\<rparr>"
          "const_list cs"
  shows "\<lparr>s;vs;cs@es\<rparr> \<leadsto>_ i \<lparr>s';vs';cs@es'\<rparr>"
  using assms progress_L0[where ?es_c = "[]"]
  by fastforce

lemma progress_L0_trap:
  assumes "const_list cs"
          "cs \<noteq> [] \<or> es \<noteq> []"
  shows "\<exists>a. \<lparr>s;vs;cs@[Trap]@es\<rparr> \<leadsto>_ i \<lparr>s;vs;[Trap]\<rparr>"
proof -
  have "cs @ [Trap] @ es \<noteq> [Trap]"
    using assms(2)
    by (cases "cs = []") (auto simp add: append_eq_Cons_conv)
  thus ?thesis
    using reduce.intros(1) assms(2) reduce_simple.trap
          Lfilled.intros(1)[OF assms(1), of _ es "[Trap]"]
    by blast
qed

lemma progress_LN:
  assumes "(Lfilled j lholed [$Br (j+k)] es)"
          "\<S>\<bullet>\<C> \<turnstile> es : ([] _> ts)"
          "(label \<C>)!k = tvs"
  shows "\<exists>lholed' vs \<C>'. (Lfilled j lholed' (vs@[$Br (j+k)]) es)
                    \<and> (\<S>\<bullet>\<C>' \<turnstile> vs : ([] _> tvs))
                    \<and> const_list vs"
  using assms
proof (induction "[$Br (j+k)]" es arbitrary: k \<C> ts rule: Lfilled.induct)
  case (L0 vs lholed es')
  obtain ts' ts'' where ts_def:"\<S>\<bullet>\<C> \<turnstile> vs : ([] _> ts')"
                                 "\<S>\<bullet>\<C> \<turnstile> [$Br k] : (ts' _> ts'')"
                                 "\<S>\<bullet>\<C> \<turnstile> es' : (ts'' _> ts)"
    using e_type_comp_conc2[OF L0(3)]
    by fastforce
  obtain ts_c where "ts' = ts_c @ tvs"
    using b_e_type_br[of \<C> "Br k" ts' ts''] L0(3,4) ts_def(2) unlift_b_e
    by fastforce
  then obtain vs1 vs2 where vs_def:"\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts_c)"
                                   "\<S>\<bullet>\<C> \<turnstile> vs2 : (ts_c _> (ts_c@tvs))"
                                   "vs = vs1@vs2"
                                   "const_list vs1"
                                   "const_list vs2"
    using e_type_const_list_cons[OF L0(1)] ts_def(1)
    by fastforce
  hence "\<S>\<bullet>\<C> \<turnstile> vs2 : ([] _> tvs)"
    using e_type_const_list by blast
  thus ?case
    using Lfilled.intros(1)[OF vs_def(4), of _ es' "vs2@[$Br k]"] vs_def(3,5)
    by fastforce
next
  case (LN vs lholed n es' l es'' j lfilledk)
  obtain t1s t2s where ts_def:"\<S>\<bullet>\<C> \<turnstile> vs : ([] _> t1s)"
                               "\<S>\<bullet>\<C> \<turnstile> [Label n es' lfilledk] : (t1s _> t2s)"
                               "\<S>\<bullet>\<C> \<turnstile> es'' : (t2s _> ts)"
  using e_type_comp_conc2[OF LN(5)]
  by fastforce
  obtain ts' ts_l where ts_l_def:"\<S>\<bullet>\<C>\<lparr>label := [ts'] @ label \<C>\<rparr> \<turnstile> lfilledk : ([] _> ts_l)"
    using e_type_label[OF ts_def(2)]
    by fastforce
  obtain lholed' vs' \<C>' where lfilledk_def:"Lfilled j lholed' (vs' @ [$Br (j + (1 + k))]) lfilledk"
                                          "\<S>\<bullet>\<C>' \<turnstile> vs' : ([] _> tvs)"
                                          "const_list vs'"
    using LN(4)[OF _ ts_l_def, of "1 + k"] LN(5,6)
    by fastforce
  thus ?case
    using Lfilled.intros(2)[OF LN(1) _ lfilledk_def(1)]
    by fastforce
qed

lemma progress_LN_return:
  assumes "(Lfilled j lholed [$Return] es)"
          "\<S>\<bullet>\<C> \<turnstile> es : ([] _> ts)"
          "(return \<C>) = Some tvs"
  shows "\<exists>lholed' vs \<C>'. (Lfilled j lholed' (vs@[$Return]) es)
                    \<and> (\<S>\<bullet>\<C>' \<turnstile> vs : ([] _> tvs))
                    \<and> const_list vs"
  using assms
proof (induction "[$Return]" es arbitrary: k \<C> ts rule: Lfilled.induct)
  case (L0 vs lholed es')
  obtain ts' ts'' where ts_def:"\<S>\<bullet>\<C> \<turnstile> vs : ([] _> ts')"
                                 "\<S>\<bullet>\<C> \<turnstile> [$Return] : (ts' _> ts'')"
                                 "\<S>\<bullet>\<C> \<turnstile> es' : (ts'' _> ts)"
    using e_type_comp_conc2[OF L0(3)]
    by fastforce
  obtain ts_c where "ts' = ts_c @ tvs"
    using b_e_type_return[of \<C> "Return" ts' ts''] L0(3,4) ts_def(2) unlift_b_e
    by fastforce
  then obtain vs1 vs2 where vs_def:"\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts_c)"
                                   "\<S>\<bullet>\<C> \<turnstile> vs2 : (ts_c _> (ts_c@tvs))"
                                   "vs = vs1@vs2"
                                   "const_list vs1"
                                   "const_list vs2"
    using e_type_const_list_cons[OF L0(1)] ts_def(1)
    by fastforce
  hence "\<S>\<bullet>\<C> \<turnstile> vs2 : ([] _> tvs)"
    using e_type_const_list by blast
  thus ?case
    using Lfilled.intros(1)[OF vs_def(4), of _ es' "vs2@[$Return]"] vs_def(3,5)
    by fastforce
next
  case (LN vs lholed n es' l es'' j lfilledk)
  obtain t1s t2s where ts_def:"\<S>\<bullet>\<C> \<turnstile> vs : ([] _> t1s)"
                               "\<S>\<bullet>\<C> \<turnstile> [Label n es' lfilledk] : (t1s _> t2s)"
                               "\<S>\<bullet>\<C> \<turnstile> es'' : (t2s _> ts)"
  using e_type_comp_conc2[OF LN(5)]
  by fastforce
  obtain ts' ts_l where ts_l_def:"\<S>\<bullet>\<C>\<lparr>label := [ts'] @ label \<C>\<rparr> \<turnstile> lfilledk : ([] _> ts_l)"
    using e_type_label[OF ts_def(2)]
    by fastforce
  obtain lholed' vs' \<C>' where lfilledk_def:"Lfilled j lholed' (vs' @ [$Return]) lfilledk"
                                          "\<S>\<bullet>\<C>' \<turnstile> vs' : ([] _> tvs)"
                                          "const_list vs'"
    using LN(4)[OF ts_l_def] LN(6)
    by fastforce
  thus ?case
    using Lfilled.intros(2)[OF LN(1) _ lfilledk_def(1)]
    by fastforce
qed

lemma progress_LN1:
  assumes "(Lfilled j lholed [$Br (j+k)] es)"
          "\<S>\<bullet>\<C> \<turnstile> es : (ts _> ts')"
  shows "length (label \<C>) > k"
  using assms
proof (induction "[$Br (j+k)]" es arbitrary: k \<C> ts ts' rule: Lfilled.induct)
  case (L0 vs lholed es')
  obtain ts'' ts''' where ts_def:"\<S>\<bullet>\<C> \<turnstile> vs : (ts _> ts'')"
                               "\<S>\<bullet>\<C> \<turnstile> [$Br k] : (ts'' _> ts''')"
                               "\<S>\<bullet>\<C> \<turnstile> es' : (ts''' _> ts')"
    using e_type_comp_conc2[OF L0(3)]
    by fastforce
  thus ?case
    using b_e_type_br(1)[of _ "Br k" ts'' ts'''] unlift_b_e
    by fastforce
next
  case (LN vs lholed n es' l es'' k' lfilledk)
  obtain t1s t2s where ts_def:"\<S>\<bullet>\<C> \<turnstile> vs : (ts _> t1s)"
                               "\<S>\<bullet>\<C> \<turnstile> [Label n es' lfilledk] : (t1s _> t2s)"
                               "\<S>\<bullet>\<C> \<turnstile> es'' : (t2s _> ts')"
  using e_type_comp_conc2[OF LN(5)]
  by fastforce
  obtain ts'' ts_l where ts_l_def:"\<S>\<bullet>\<C>\<lparr>label := [ts''] @ label \<C>\<rparr> \<turnstile> lfilledk : ([] _> ts_l)"
    using e_type_label[OF ts_def(2)]
    by fastforce
  thus ?case
    using LN(4)[of "1+k"]
    by fastforce
qed

lemma progress_LN2:
  assumes "(Lfilled j lholed e1s lfilled)"
  shows "\<exists>lfilled'. (Lfilled j lholed e2s lfilled')"
  using assms
proof (induction rule: Lfilled.induct)
  case (L0 vs lholed es' es)
  thus ?case
    using Lfilled.intros(1)
    by fastforce
next
  case (LN vs lholed n es' l es'' k es lfilledk)
  thus ?case
    using Lfilled.intros(2)
    by fastforce
qed

lemma const_of_const_list:
  assumes "length cs = 1"
          "const_list cs"
  shows "\<exists>v. cs = [$C v]"
  using e_type_const_unwrap assms
  unfolding const_list_def list_all_length
  by (metis append_butlast_last_id append_self_conv2 gr_zeroI last_conv_nth length_butlast
            length_greater_0_conv less_numeral_extra(1,4) zero_less_diff)

lemma const_of_i32:
  assumes "const_list cs"
          "\<S>\<bullet>\<C> \<turnstile> cs : ([] _> [(T_i32)])"
  shows "\<exists>c. cs = [$C ConstInt32 c]"
proof -                    
  obtain v where "cs = [$C v]"
    using const_of_const_list assms(1) e_type_const_list[OF assms]
    by fastforce
  moreover
  hence "\<C> \<turnstile> [C v] : ([] _> [(T_i32)])"
    using assms(2) unlift_b_e
    by fastforce
  hence "\<exists>c. v = ConstInt32 c"
  proof (induction "[C v]" "([] _> [(T_i32)])" rule: b_e_typing.induct)
    case (const \<C>)
    then show ?case
      unfolding typeof_def
      by (cases v, auto)
  qed auto
  ultimately
  show ?thesis
    by fastforce
qed

lemma const_of_i64:
  assumes "const_list cs"
          "\<S>\<bullet>\<C> \<turnstile> cs : ([] _> [(T_i64)])"
  shows "\<exists>c. cs = [$C ConstInt64 c]"
proof -                    
  obtain v where "cs = [$C v]"
    using const_of_const_list assms(1) e_type_const_list[OF assms]
    by fastforce
  moreover
  hence "\<C> \<turnstile> [C v] : ([] _> [(T_i64)])"
    using assms(2) unlift_b_e
    by fastforce
  hence "\<exists>c. v = ConstInt64 c"
  proof (induction "[C v]" "([] _> [(T_i64)])" rule: b_e_typing.induct)
    case (const \<C>)
    then show ?case
      unfolding typeof_def
      by (cases v, auto)
  qed auto
  ultimately
  show ?thesis
    by fastforce
qed

lemma const_of_f32:
  assumes "const_list cs"
          "\<S>\<bullet>\<C> \<turnstile> cs : ([] _> [T_f32])"
  shows "\<exists>c. cs = [$C ConstFloat32 c]"
proof -                    
  obtain v where "cs = [$C v]"
    using const_of_const_list assms(1) e_type_const_list[OF assms]
    by fastforce
  moreover
  hence "\<C> \<turnstile> [C v] : ([] _> [T_f32])"
    using assms(2) unlift_b_e
    by fastforce
  hence "\<exists>c. v = ConstFloat32 c"
  proof (induction "[C v]" "([] _> [T_f32])" rule: b_e_typing.induct)
    case (const \<C>)
    then show ?case
      unfolding typeof_def
      by (cases v, auto)
  qed auto
  ultimately
  show ?thesis
    by fastforce
qed

lemma const_of_f64:
  assumes "const_list cs"
          "\<S>\<bullet>\<C> \<turnstile> cs : ([] _> [T_f64])"
  shows "\<exists>c. cs = [$C ConstFloat64 c]"
proof -                    
  obtain v where "cs = [$C v]"
    using const_of_const_list assms(1) e_type_const_list[OF assms]
    by fastforce
  moreover
  hence "\<C> \<turnstile> [C v] : ([] _> [T_f64])"
    using assms(2) unlift_b_e
    by fastforce
  hence "\<exists>c. v = ConstFloat64 c"
  proof (induction "[C v]" "([] _> [T_f64])" rule: b_e_typing.induct)
    case (const \<C>)
    then show ?case
      unfolding typeof_def
      by (cases v, auto)
  qed auto
  ultimately
  show ?thesis
    by fastforce
qed

lemma progress_unop_testop_i:
  assumes "\<S>\<bullet>\<C> \<turnstile> cs : ([] _> [t])"
          "is_int_t t"
          "const_list cs"
          "e = Unop_i t iop \<or> e = Testop t testop"
  shows "\<exists>a s' vs' es'. \<lparr>s;vs;cs@([$e])\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  using assms(2)
proof (cases t)
  case T_i32
  thus ?thesis
    using  const_of_i32[OF assms(3)] assms(1,4)
          reduce.intros(1)[OF reduce_simple.intros(1)] reduce.intros(1)[OF reduce_simple.intros(13)]
    by fastforce      
next
  case T_i64
  thus ?thesis
    using const_of_i64[OF assms(3)] assms(1,4)
          reduce.intros(1)[OF reduce_simple.intros(2)] reduce.intros(1)[OF reduce_simple.intros(14)]
    by fastforce
qed (simp_all add: is_int_t_def)

lemma progress_unop_f:
  assumes "\<S>\<bullet>\<C> \<turnstile> cs : ([] _> [t])"
          "is_float_t t"
          "const_list cs"
          "e = Unop_f t iop"
  shows "\<exists>a s' vs' es'. \<lparr>s;vs;cs@([$e])\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  using assms(2)
proof (cases t)
  case T_f32
  thus ?thesis
    using  const_of_f32[OF assms(3)] assms(1,4)
          reduce.intros(1)[OF reduce_simple.intros(3)] reduce.intros(1)[OF reduce_simple.intros(13)]
    by fastforce      
next
  case T_f64
  thus ?thesis
    using const_of_f64[OF assms(3)] assms(1,4)
          reduce.intros(1)[OF reduce_simple.intros(4)] reduce.intros(1)[OF reduce_simple.intros(14)]
    by fastforce
qed (simp_all add: is_float_t_def)

lemma const_list_split_2:
  assumes "const_list cs"
          "\<S>\<bullet>\<C> \<turnstile> cs : ([] _> [t1, t2])"
  shows "\<exists>c1 c2. (\<S>\<bullet>\<C> \<turnstile> [c1] : ([] _> [t1]))
                 \<and> (\<S>\<bullet>\<C> \<turnstile> [c2] : ([] _> [t2]))
                 \<and> cs = [c1, c2]
                 \<and> const_list [c1]
                 \<and> const_list [c2]"
proof -
  have l_cs:"length cs = 2"
    using assms e_type_const_list[OF assms]
    by simp
  then obtain c1 c2 where "cs!0 = c1" "cs!1 = c2"
    by fastforce
  hence "cs = [c1] @ [c2]"
    using assms e_type_const_conv_vs typing_map_typeof
    by fastforce
  thus ?thesis
    using assms e_type_comp[of \<S> \<C> "[c1]" c2] e_type_const[of c2 \<S> \<C> _ "[t1,t2]"]
    unfolding const_list_def
    by fastforce
qed

lemma const_list_split_3:
  assumes "const_list cs"
          "\<S>\<bullet>\<C> \<turnstile> cs : ([] _> [t1, t2, t3])"
  shows "\<exists>c1 c2 c3. (\<S>\<bullet>\<C> \<turnstile> [c1] : ([] _> [t1]))
                    \<and> (\<S>\<bullet>\<C> \<turnstile> [c2] : ([] _> [t2]))
                    \<and> (\<S>\<bullet>\<C> \<turnstile> [c3] : ([] _> [t3]))
                    \<and> cs = [c1, c2, c3]"
proof -
  have l_cs:"length cs = 3"
    using assms e_type_const_list[OF assms]
    by simp
  then obtain c1 c2 c3 where "cs!0 = c1" "cs!1 = c2" "cs!2 = c3"
    by fastforce
  hence "cs = [c1] @ [c2] @ [c3]"
    using assms e_type_const_conv_vs typing_map_typeof
    by fastforce
  thus ?thesis
    using assms e_type_comp_conc2[of \<S> \<C> "[c1]" "[c2]" "[c3]" "[]" "[t1,t2,t3]"]
          e_type_const[of c1] e_type_const[of c2] e_type_const[of c3]
    unfolding const_list_def
    by fastforce
qed

lemma progress_binop_relop_i:
  assumes "\<S>\<bullet>\<C> \<turnstile> cs : ([] _> [t, t])"
          "is_int_t t"
          "const_list cs"
          "e = Binop_i t iop \<or> e = Relop_i t irop"
  shows "\<exists>a s' vs' es'. \<lparr>s;vs;cs@([$e])\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  using assms(2)
proof (cases t)
  case (T_i32)
  hence cs_def:"\<exists>c1 c2. cs = [$C ConstInt32 c1,$C ConstInt32 c2]"
    using const_list_split_2[OF assms(3,1)] assms(3) const_of_i32
    unfolding const_list_def
    by blast
  show ?thesis
  proof (cases "e = Binop_i t iop")
    case True
    obtain c1 c2 where "cs = [$C ConstInt32 c1,$C ConstInt32 c2]"
      using cs_def
      by blast
    thus ?thesis
      apply (cases "app_binop_i iop c1 c2")
       apply (metis reduce_simple.intros(6) reduce.intros(1) T_i32 True append_Cons append_Nil)
      apply (metis reduce_simple.intros(5) reduce.intros(1) T_i32 True append_Cons append_Nil)
      done
  next
    case False
    thus ?thesis
    using reduce_simple.intros(15) assms(4) reduce.intros(1) cs_def T_i32
    by fastforce
  qed
next
  case (T_i64)
  hence cs_def:"\<exists>c1 c2. cs = [$C ConstInt64 c1,$C ConstInt64 c2]"
    using const_list_split_2[OF assms(3,1)] assms(3) const_of_i64
    unfolding const_list_def
    by blast
  show ?thesis
  proof (cases "e = Binop_i t iop")
    case True
    obtain c1 c2 where "cs = [$C ConstInt64 c1,$C ConstInt64 c2]"
      using cs_def
      by blast
    thus ?thesis
      apply (cases "app_binop_i iop c1 c2")
       apply (metis reduce_simple.intros(8) reduce.intros(1) T_i64 True append_Cons append_Nil)
      apply (metis reduce_simple.intros(7) reduce.intros(1) T_i64 True append_Cons append_Nil)
      done
  next
    case False
    thus ?thesis
    using reduce_simple.intros(16) assms(4) reduce.intros(1) cs_def T_i64
    by fastforce
  qed
qed (simp_all add: is_int_t_def)

lemma progress_binop_relop_f:
  assumes "\<S>\<bullet>\<C> \<turnstile> cs : ([] _> [t, t])"
          "is_float_t t"
          "const_list cs"
          "e = Binop_f t fop \<or> e = Relop_f t frop"
  shows "\<exists>a s' vs' es'. \<lparr>s;vs;cs@([$e])\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  using assms(2)
proof (cases t)
  case T_f32
  hence cs_def:"\<exists>c1 c2. cs = [$C ConstFloat32 c1,$C ConstFloat32 c2]"
    using const_list_split_2[OF assms(3,1)] assms(3) const_of_f32
    unfolding const_list_def
    by blast
  show ?thesis
  proof (cases "e = Binop_f t fop")
    case True
    obtain c1 c2 where cs_def:"cs = [$C ConstFloat32 c1,$C ConstFloat32 c2]"
      using cs_def
      by blast
    thus ?thesis
      apply (cases "app_binop_f fop c1 c2")
       apply (metis reduce_simple.intros(10) reduce.intros(1) T_f32 True append_Cons append_Nil)
      apply (metis reduce_simple.intros(9) reduce.intros(1) T_f32 True append_Cons append_Nil)
    done
  next
    case False
    thus ?thesis
    using reduce_simple.intros(17) assms(4) reduce.intros(1) cs_def T_f32
    by fastforce
  qed
next
  case T_f64
  hence cs_def:"\<exists>c1 c2. cs = [$C ConstFloat64 c1,$C ConstFloat64 c2]"
    using const_list_split_2[OF assms(3,1)] assms(3) const_of_f64
    unfolding const_list_def
    by blast
  show ?thesis
  proof (cases "e = Binop_f t fop")
    case True
    obtain c1 c2 where "cs = [$C ConstFloat64 c1,$C ConstFloat64 c2]"
      using cs_def
      by blast
    thus ?thesis
      apply (cases "app_binop_f fop c1 c2")
       apply (metis reduce_simple.intros(12) reduce.intros(1) T_f64 True append_Cons append_Nil)
      apply (metis reduce_simple.intros(11) reduce.intros(1) T_f64 True append_Cons append_Nil)
    done
  next
    case False
    thus ?thesis
      using reduce_simple.intros(18) assms(4) reduce.intros(1) cs_def T_f64
    by fastforce
  qed
qed (simp_all add: is_float_t_def)

lemma progress_b_e:
  assumes "\<C> \<turnstile> b_es : (ts _> ts')"
          "\<S>\<bullet>\<C> \<turnstile> cs : ([] _> ts)"
          "(\<And>lholed. \<not>(Lfilled 0 lholed [$Return] (cs@($*b_es))))"
          "\<And> i lholed. \<not>(Lfilled 0 lholed [$Br (i)] (cs@($*b_es)))"
          "const_list cs"
          "\<not> const_list ($* b_es)"
          "i < length (s_inst \<S>)"
          "length (local \<C>) = length (vs)"
          "Option.is_none (memory \<C>) = Option.is_none (inst.mem ((inst s)!i))"
  shows "\<exists>a s' vs' es'. \<lparr>s;vs;cs@($*b_es)\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  using assms
proof (induction b_es "(ts _> ts')" arbitrary: ts ts' cs rule: b_e_typing.induct)
  case (const \<C> v)
  then show ?case
    unfolding const_list_def is_const_def
    by simp
next
  case (unop_i t \<C> uu)
  thus ?case
    using progress_unop_testop_i[OF unop_i(2,1)]
    by fastforce
next
  case (unop_f t \<C> uv)
  thus ?case
    using progress_unop_f[OF unop_f(2,1,5)]
    by fastforce
next
  case (binop_i t \<C> uw)
  thus ?case
    using progress_binop_relop_i[OF binop_i(2,1)]
    by fastforce
next
  case (binop_f t \<C> ux)
  thus ?case
    using progress_binop_relop_f[OF binop_f(2,1,5)]
    by fastforce
next
  case (testop t \<C> uy)
  thus ?case
    using progress_unop_testop_i[OF testop(2,1)]
    by fastforce
next
  case (relop_i t \<C> uz)
  thus ?case
    using progress_binop_relop_i[OF relop_i(2,1)]
    by fastforce
next
  case (relop_f t \<C> va)
  thus ?case
    using progress_binop_relop_f[OF relop_f(2,1,5)]
    by fastforce
next
  case (convert t1 t2 sx \<C>)
  obtain v where cs_def:"cs = [$ C v]" "typeof v = t2"
    using const_typeof const_of_const_list[OF _ convert(6)] e_type_const_list[OF convert(6,3)]
    by fastforce
  thus ?case
  proof (cases "cvt t1 sx v")
    case None
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.convert_None[OF _ None]] cs_def
      unfolding types_agree_def
      by fastforce
  next
    case (Some a)
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.convert_Some[OF _ Some]] cs_def
      unfolding types_agree_def
      by fastforce
  qed
next
  case (reinterpret t1 t2 \<C>)
  obtain v where cs_def:"cs = [$ C v]" "typeof v = t2"
    using const_typeof const_of_const_list[OF _ reinterpret(6)] e_type_const_list[OF reinterpret(6,3)]
    by fastforce
  thus ?case
    using reduce.intros(1)[OF reduce_simple.reinterpret]
    unfolding types_agree_def
    by fastforce
next
  case (unreachable \<C> ts ts')
  thus ?case
    using reduce.intros(1)[OF reduce_simple.unreachable] progress_L0[OF _ unreachable(4)]
    by fastforce
next
  case (nop \<C>)
  thus ?case
    using reduce.intros(1)[OF reduce_simple.nop] progress_L0[OF _ nop(4)]
    by fastforce
next
  case (drop \<C> t)
  obtain v where "cs = [$C v]"
    using const_of_const_list drop(4) e_type_const_list[OF drop(4,1)]
    by fastforce
  thus ?case
    using reduce.intros(1)[OF reduce_simple.drop] progress_L0[OF _ drop(4)]
    by fastforce
next
  case (select \<C> t)
  obtain v1 v2 v3 where cs_def:"\<S>\<bullet>\<C> \<turnstile> [$ C v3] : ([] _> [T_i32])"
                               "cs = [$C v1, $C v2, $ C v3]"
    using const_list_split_3[OF select(4,1)] select(4)
    unfolding const_list_def
    by (metis list_all_simps(1) e_type_const_unwrap)
  obtain c3 where c_def:"v3 = ConstInt32 c3"
    using cs_def select(4) const_of_i32[OF _ cs_def(1)]
    unfolding const_list_def
    by fastforce
  have "\<exists>a s' vs' es'. \<lparr>s;vs;[$C v1, $C v2, $ C ConstInt32 c3, $Select]\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  proof (cases "int_eq c3 0")
    case True
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.select_false]
      by fastforce
  next
    case False
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.select_true]
      by fastforce
  qed
  thus ?case
    using c_def cs_def
    by fastforce
next
  case (block tf tn tm \<C> es)
  show ?case
    using reduce_simple.block[OF block(7), of _ tn tm _ es]
          e_type_const_list[OF block(7,4)] reduce.intros(1) block(1)
    by fastforce
next
  case (loop tf tn tm \<C> es)
  show ?case
    using reduce_simple.loop[OF loop(7), of _ tn tm _ es]
          e_type_const_list[OF loop(7,4)] reduce.intros(1) loop(1) 
    by fastforce
next
  case (if_wasm tf tn tm \<C> es1 es2)
  obtain c1s c2s where cs_def:"\<S>\<bullet>\<C> \<turnstile> c1s : ([] _> tn)"
                              "\<S>\<bullet>\<C> \<turnstile> c2s : ([] _> [T_i32])"
                              "const_list c1s"
                              "const_list c2s"
                              "cs = c1s @ c2s"
    using e_type_const_list_cons[OF if_wasm(9,6)] e_type_const_list
    by fastforce
  obtain c where c_def: "c2s = [$ C (ConstInt32 c)]"
    using const_of_i32 cs_def
    by fastforce
  have "\<exists>a s' vs' es'. \<lparr>s;vs;[$ C (ConstInt32 c), $ If tf es1 es2]\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  proof (cases "int_eq c 0")
    case True
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.if_false]
      by fastforce
  next
    case False
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.if_true]
      by fastforce
  qed
  thus ?case
    using c_def cs_def progress_L0
    by fastforce
next
  case (br i \<C> ts t1s t2s)
  thus ?case
    using Lfilled.intros(1)[OF br(6), of _ "[]" "[$Br i]"]
    by fastforce
next
  case (br_if j \<C> ts)
  obtain cs1 cs2 where cs_def:"\<S>\<bullet>\<C> \<turnstile> cs1 : ([] _> ts)"
                              "\<S>\<bullet>\<C> \<turnstile> cs2 : ([] _> [T_i32])"
                              "const_list cs1"
                              "const_list cs2"
                              "cs = cs1 @ cs2"
    using e_type_const_list_cons[OF br_if(6,3)] e_type_const_list
    by fastforce
  obtain c where c_def:"cs2 = [$C ConstInt32 c]"
    using const_of_i32[OF cs_def(4,2)]
    by blast
  have "\<exists>a s' vs' es'. \<lparr>s;vs;cs2@($* [Br_if j])\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  proof (cases "int_eq c 0")
    case True
    thus ?thesis
      using c_def reduce.intros(1)[OF reduce_simple.br_if_false]
      by fastforce
  next
    case False
    thus ?thesis
      using c_def reduce.intros(1)[OF reduce_simple.br_if_true]
      by fastforce
  qed
  thus ?case
    using cs_def(5) progress_L0[OF _ cs_def(3), of s vs "cs2 @ ($* [Br_if j])" _ _ _ _ "[]"]
    by fastforce
next
  case (br_table \<C> ts "is" i' t1s t2s)
  obtain cs1 cs2 where cs_def:"\<S>\<bullet>\<C> \<turnstile> cs1 : ([]_> (t1s @ ts))"
                              "\<S>\<bullet>\<C> \<turnstile> cs2 : ([] _> [T_i32])"
                              "const_list cs1"
                              "const_list cs2"
                              "cs = cs1 @ cs2"
    using e_type_const_list_cons[OF br_table(5), of \<S> \<C> "(t1s @ ts)" "[T_i32]"]
          e_type_const_list[of _ \<S> \<C> "t1s @ ts" "(t1s @ ts) @ [T_i32]"]
          br_table(2,5)
    unfolding const_list_def
    by fastforce
  obtain c where c_def:"cs2 = [$C ConstInt32 c]"
    using const_of_i32[OF cs_def(4,2)]
    by blast
  have "\<exists>a s' vs' es'. \<lparr>s;vs;[$C ConstInt32 c, $Br_table is i']\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  proof (cases "(nat_of_int c) < length is")
    case True
    show ?thesis
      using reduce.intros(1)[OF reduce_simple.br_table[OF True]]
      by fastforce
  next
    case False
    hence "length is \<le> nat_of_int c"
      by fastforce
    thus ?thesis
      using reduce.intros(1)[OF reduce_simple.br_table_length]
      by fastforce
  qed
  thus ?case
    using c_def cs_def progress_L0
    by fastforce
next
  case (return \<C> ts t1s t2s)
  thus ?case
    using Lfilled.intros(1)[OF return(5), of _ "[]" "[$Return]"]
    by fastforce
next
  case (call j \<C>)
  show ?case
    using progress_L0[OF reduce.intros(2) call(6)]
    by fastforce
next
  case (call_indirect j \<C> t1s t2s)
  obtain cs1 cs2 where cs_def:"\<S>\<bullet>\<C> \<turnstile> cs1 : ([]_> t1s)"
                              "\<S>\<bullet>\<C> \<turnstile> cs2 : ([] _> [T_i32])"
                              "const_list cs1"
                              "const_list cs2"
                              "cs = cs1 @ cs2"
    using e_type_const_list_cons[OF call_indirect(7), of \<S> \<C> t1s "[T_i32]"]
          e_type_const_list[of _ \<S> \<C> t1s "t1s @ [T_i32]"]
          call_indirect(4)
    by fastforce
  obtain c where c_def:"cs2 = [$C ConstInt32 c]"
    using cs_def(2,4) const_of_i32
    by fastforce
  consider 
    (1) "\<exists>cl tf. stab s i (nat_of_int c) = Some cl \<and> stypes s i j = tf \<and> cl_type cl = tf"
  | (2) "\<exists>cl. stab s i (nat_of_int c) = Some cl \<and> stypes s i j \<noteq> cl_type cl"
  | (3) "stab s i (nat_of_int c) = None"
    by (metis option.collapse)
  hence "\<exists>a s' vs' es'. \<lparr>s;vs;[$C ConstInt32 c, $Call_indirect j]\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  proof (cases)
    case 1
    thus ?thesis
      using reduce.intros(3)
      by blast
  next
    case 2
    thus ?thesis
      using reduce.intros(4)
      by blast
  next
    case 3
    thus ?thesis
      using reduce.intros(4)
      by blast
  qed
  then show ?case
    using c_def cs_def progress_L0
    by fastforce
next
  case (get_local j \<C> t)
  obtain v vj vj' where v_def:"v = vs ! j" "vj = (take j vs)" "vj' = (drop (j+1) vs)"
    by blast
  have j_def:"j < length vs"
    using get_local(1,9)
    by simp
  hence vj_len:"length vj = j"
    using v_def(2)
    by fastforce
  hence "vs = vj @ [v] @ vj'"
    using v_def id_take_nth_drop j_def
    by fastforce
  thus ?case
    using progress_L0[OF reduce.intros(8)[OF vj_len, of s v vj'] get_local(6)]
    by fastforce
next
  case (set_local j \<C> t)
  obtain v vj vj' where v_def:"v = vs ! j" "vj = (take j vs)" "vj' = (drop (j+1) vs)"
    by blast
  obtain v' where cs_def: "cs = [$C v']"
    using const_of_const_list set_local(3,6) e_type_const_list
    by fastforce
  have j_def:"j < length vs"
    using set_local(1,9)
    by simp
  hence vj_len:"length vj = j"
    using v_def(2)
    by fastforce
  hence "vs = vj @ [v] @ vj'"
    using v_def id_take_nth_drop j_def
    by fastforce
  thus ?case
    using reduce.intros(9)[OF vj_len, of s v vj' v' i] cs_def
    by fastforce
next
  case (tee_local i \<C> t)
  obtain v where "cs = [$C v]"
    using const_of_const_list tee_local(3,6) e_type_const_list
    by fastforce
  thus ?case
    using reduce.intros(1)[OF reduce_simple.tee_local] tee_local(6)
    unfolding const_list_def
    by fastforce
next
  case (get_global j \<C> t)
  thus ?case
    using reduce.intros(10)[of s vs j i] progress_L0
    by fastforce
next
  case (set_global j \<C> t)
  obtain v where "cs = [$C v]"
    using const_of_const_list set_global(4,7) e_type_const_list
    by fastforce
  thus ?case
    using reduce.intros(11)[of s i j v _ vs]
    by fastforce
next
  case (load \<C> n a tp_sx t off)
  obtain c where c_def: "cs = [$C ConstInt32 c]"
    using const_of_i32 load(3,6) e_type_const_unwrap
    unfolding const_list_def
    by fastforce
  obtain j where mem_some:"smem_ind s i = Some j"
    using load(1,10)
    unfolding smem_ind_def
    by fastforce
  have "\<exists>a' s' vs' es'. \<lparr>s;vs;[$C ConstInt32 c, $Load t tp_sx a off]\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  proof (cases tp_sx)
    case None
    note tp_none = None
    show ?thesis
    proof (cases "load ((mem s)!j) (nat_of_int c) off (t_length t)")
      case None
      show ?thesis
        using reduce.intros(13)[OF mem_some _ None, of vs] tp_none load(2)
        by fastforce
    next
      case (Some a)
      show ?thesis
        using reduce.intros(12)[OF mem_some _ Some, of vs] tp_none load(2)
        by fastforce
    qed
  next
    case (Some a)
    obtain tp sx where tp_some:"tp_sx = Some (tp, sx)"
      using Some
      by fastforce
    show ?thesis
    proof (cases "load_packed sx ((mem s)!j) (nat_of_int c) off (tp_length tp) (t_length t)")
      case None
      show ?thesis
        using reduce.intros(15)[OF mem_some _ None, of vs] tp_some load(2)
        by fastforce
    next
      case (Some a)
      show ?thesis
        using reduce.intros(14)[OF mem_some _ Some, of vs] tp_some load(2)
        by fastforce
    qed
  qed
  then show ?case
    using c_def progress_L0
    by fastforce
next
  case (store \<C> n a tp t off)
  obtain cs' v where cs_def:"\<S>\<bullet>\<C> \<turnstile> [cs'] : ([] _> [T_i32])"
                            "\<S>\<bullet>\<C> \<turnstile> [$ C v] : ([] _> [t])"
                            "cs = [cs',$ C v]"
    using const_list_split_2[OF store(6,3)] e_type_const_unwrap
    unfolding const_list_def
    by fastforce
  have t_def:"typeof v = t"
    using cs_def(2) b_e_type_value[OF unlift_b_e[of \<S> \<C> "[C v]" "([] _> [t])"]]
    by fastforce
  obtain j where mem_some:"smem_ind s i = Some j"
    using store(1,10)
    unfolding smem_ind_def
    by fastforce
  obtain c where c_def:"cs' = $C ConstInt32 c"
    using const_of_i32[OF _ cs_def(1)] cs_def(3) store(6)
    unfolding const_list_def
    by fastforce
  have "\<exists>a' s' vs' es'. \<lparr>s;vs;[$C ConstInt32 c, $C v, $Store t tp a off]\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  proof (cases tp)
    case None
    note tp_none = None
    show ?thesis
    proof (cases "store (s.mem s ! j) (nat_of_int c) off (bits v) (t_length t)")
      case None
      show ?thesis
        using reduce.intros(17)[OF _ mem_some _ None, of vs] t_def tp_none store(2)
        unfolding types_agree_def
        by fastforce
    next
      case (Some a)
      show ?thesis
        using reduce.intros(16)[OF _ mem_some _ Some, of vs] t_def tp_none store(2)
        unfolding types_agree_def
        by fastforce
    qed
  next
    case (Some a)
    note tp_some = Some
    show ?thesis
    proof (cases "store_packed (s.mem s ! j) (nat_of_int c) off (bits v) (tp_length a)")
      case None
      show ?thesis
        using reduce.intros(19)[OF _ mem_some _ None, of t vs] t_def tp_some store(2)
        unfolding types_agree_def
        by fastforce
    next
      case (Some a)
      show ?thesis
        using reduce.intros(18)[OF _ mem_some _ Some, of t vs] t_def tp_some store(2)
        unfolding types_agree_def
        by fastforce
    qed
  qed
  then show ?case
    using c_def cs_def progress_L0
    by fastforce
next
  case (current_memory \<C> n)
  obtain j where mem_some:"smem_ind s i = Some j"
    using current_memory(1,9)
    unfolding smem_ind_def
    by fastforce
  thus ?case
    using progress_L0[OF reduce.intros(20)[OF mem_some] current_memory(5), of _ _ vs "[]"]
    by fastforce
next
  case (grow_memory \<C> n)
  obtain c where c_def:"cs = [$C ConstInt32 c]"
    using const_of_i32 grow_memory(2,5)
    by fastforce
  obtain j where mem_some:"smem_ind s i = Some j"
    using grow_memory(1,9)
    unfolding smem_ind_def
    by fastforce
  show ?case
    using reduce.intros(22)[OF mem_some, of _] c_def
    by fastforce
next
  case (empty \<C>)
  thus ?case
    unfolding const_list_def
    by simp
next
  case (composition \<C> es t1s t2s e t3s)
  consider (1) "\<not> const_list ($* es)" | (2) "const_list ($* es)" "\<not> const_list ($*[e])"
    using composition(9)
    unfolding const_list_def
    by fastforce
  thus ?case
  proof (cases)
    case 1
    have "(\<And>lholed. \<not> Lfilled 0 lholed [$Return] (cs @ ($* es)))"
         "(\<And>i lholed. \<not> Lfilled 0 lholed [$Br i] (cs @ ($* es)))"
    proof safe
      fix lholed
      assume "Lfilled 0 lholed [$Return] (cs @ ($* es))"
      hence "\<exists>lholed'. Lfilled 0 lholed' [$Return] (cs @ ($* es @ [e]))"
      proof (cases rule: Lfilled.cases)
        case (L0 vs es')
        thus ?thesis
          using Lfilled.intros(1)[of "vs" _ "es'@ ($*[e])" "[$Return]"]
          by (metis append.assoc map_append)
      qed simp
      thus False
        using composition(6)
        by simp
    next
      fix i lholed
      assume "Lfilled 0 lholed [$Br i] (cs @ ($* es))"
      hence "\<exists>lholed'. Lfilled 0 lholed' [$Br i] (cs @ ($* es @ [e]))"
      proof (cases rule: Lfilled.cases)
        case (L0 vs es')
        thus ?thesis
          using Lfilled.intros(1)[of "vs" _ "es'@ ($*[e])" "[$Br i]"]
          by (metis append.assoc map_append)
      qed simp
      thus False
        using composition(7)
        by simp
    qed
    thus ?thesis
      using composition(2)[OF composition(5) _ _ composition(8) 1 composition(10,11,12)] progress_L0[of s vs "(cs @ ($* es))" i _ _ _ "[]" "$*[e]"]
      unfolding const_list_def
      by fastforce
  next
    case 2
    hence "const_list (cs@($* es))"
      using composition(8)
      unfolding const_list_def
      by simp
    moreover
    have "\<S>\<bullet>\<C> \<turnstile> (cs@($* es)) : ([] _> t2s)"
      using composition(5) e_typing_s_typing.intros(1)[OF composition(1)] e_type_comp_conc
      by fastforce
    ultimately
    show ?thesis
      using composition(4)[of "(cs@($* es))"] 2(2) composition(6,7) composition(10-)
      by fastforce
  qed
next
  case (weakening \<C> es t1s t2s ts)
  obtain cs1 cs2 where cs_def:"\<S>\<bullet>\<C> \<turnstile> cs1 : ([] _> ts)"
                              "\<S>\<bullet>\<C> \<turnstile> cs2 : ([] _> t1s)"
                              "cs = cs1 @ cs2"
                              "const_list cs1"
                              "const_list cs2"
    using e_type_const_list_cons[OF weakening(6,3)] e_type_const_list[of _ \<S> \<C> "ts" "ts @ t1s"]
    by fastforce
  have "(\<And>lholed. \<not> Lfilled 0 lholed [$Return] (cs2 @ ($* es)))"
       "(\<And>i lholed. \<not> Lfilled 0 lholed [$Br i] (cs2 @ ($* es)))"
  proof safe
    fix lholed
    assume "Lfilled 0 lholed [$Return] (cs2 @ ($* es))"
    hence "\<exists>lholed'. Lfilled 0 lholed' [$Return] (cs1 @ cs2 @ ($* es))"
    proof (cases rule: Lfilled.cases)
      case (L0 vs es')
      thus ?thesis
        using Lfilled.intros(1)[of "cs1 @ vs" _ "es'" "[$Return]"] cs_def(4)
        unfolding const_list_def
        by fastforce
    qed simp
    thus False
      using weakening(4) cs_def(3)
      by simp
  next
    fix i lholed
    assume "Lfilled 0 lholed [$Br i] (cs2 @ ($* es))"
    hence "\<exists>lholed'. Lfilled 0 lholed' [$Br i] (cs1 @ cs2 @ ($* es))"
    proof (cases rule: Lfilled.cases)
      case (L0 vs es')
      thus ?thesis
        using Lfilled.intros(1)[of "cs1 @ vs" _ "es'" "[$Br i]"] cs_def(4)
        unfolding const_list_def
        by fastforce
    qed simp
    thus False
      using weakening(5) cs_def(3)
      by simp
  qed
  hence "\<exists>a s' vs' es'. \<lparr>s;vs;cs2@($*es)\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
    using weakening(2)[OF cs_def(2) _ _ cs_def(5) weakening(7)] weakening(8-)
    by fastforce
  thus ?case
    using progress_L0[OF _ cs_def(4), of s vs "cs2 @ ($* es)" i _ _ _ "[]"] cs_def(3)
    by fastforce
qed

lemma progress_e:
  assumes "\<S>\<bullet>None \<tturnstile>_i vs;cs_es : ts'"
          "\<And> k lholed. \<not>(Lfilled k lholed [$Return] cs_es)"
          "\<And> i k lholed. (Lfilled k lholed [$Br (i)] cs_es) \<Longrightarrow> i < k"
          "cs_es \<noteq> [Trap]"
          "\<not> const_list (cs_es)"
          "store_typing s \<S>"
  shows "\<exists>a s' vs' es'. \<lparr>s;vs;cs_es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
proof -
  fix \<C> cs es ts_c
  have prems1:
      "\<S>\<bullet>\<C> \<turnstile> es : (ts_c _> ts') \<Longrightarrow>
       \<S>\<bullet>\<C> \<turnstile> cs_es : ([] _> ts') \<Longrightarrow>
       cs_es = cs@es \<Longrightarrow>
       const_list cs \<Longrightarrow>
       \<S>\<bullet>\<C> \<turnstile> cs : ([] _> ts_c) \<Longrightarrow>
       (\<And> k lholed. \<not>(Lfilled k lholed [$Return] cs_es)) \<Longrightarrow>
       (\<And> i k lholed. (Lfilled k lholed [$Br (i)] cs_es) \<Longrightarrow> i < k) \<Longrightarrow>
       cs_es \<noteq> [Trap] \<Longrightarrow>
       \<not> const_list (cs_es) \<Longrightarrow>
       store_typing s \<S> \<Longrightarrow>
       i < length (s_inst \<S>) \<Longrightarrow>
       length (local \<C>) = length (vs) \<Longrightarrow>
       Option.is_none (memory \<C>) = Option.is_none (inst.mem ((inst s)!i))  \<Longrightarrow>
         \<exists>a s' vs' cs_es'. \<lparr>s;vs;cs_es\<rparr> \<leadsto>_i \<lparr>s';vs';cs_es'\<rparr>"
   and prems2:
      "\<S>\<bullet>None \<tturnstile>_i vs;cs_es : ts' \<Longrightarrow>
       (\<And> k lholed. \<not>(Lfilled k lholed [$Return] cs_es)) \<Longrightarrow>
       (\<And> i k lholed. (Lfilled k lholed [$Br (i)] cs_es) \<Longrightarrow> i < k) \<Longrightarrow>
       cs_es \<noteq> [Trap] \<Longrightarrow>
       \<not> const_list (cs_es) \<Longrightarrow>
       store_typing s \<S> \<Longrightarrow>
         \<exists>a s' vs' cs_es'. \<lparr>s;vs;cs_es\<rparr> \<leadsto>_i \<lparr>s';vs';cs_es'\<rparr>"
  proof (induction arbitrary: vs ts_c ts' i cs_es cs rule: e_typing_s_typing.inducts)
    case (1 \<C> b_es tf \<S>)
    hence "\<C> \<turnstile> b_es : (ts_c _> ts')"
      using e_type_comp_conc1[of \<S> \<C> cs "($* b_es)" "[]" "ts'"] unlift_b_e
      by (metis e_type_const_conv_vs typing_map_typeof)
    then show ?case
      using progress_b_e[OF _ 1(5) _ _ 1(4)] 1(3,4,9) list_all_append 1
      unfolding const_list_def
      by fastforce
  next
    case (2 \<S> \<C> es t1s t2s e t3s)
    show ?case
    proof (cases "const_list es")
      case True
      hence "const_list (cs@es)"
        using 2(7)
        unfolding const_list_def
        by simp
      moreover
      have "\<exists>ts''. (\<S>\<bullet>\<C> \<turnstile> (cs @ es) : ([] _> ts''))"
        using 2(5,6)
        by (metis append.assoc e_type_comp_conc1)
      ultimately
      show ?thesis
        using 2(4)[OF 2(5) _ _ _ 2(9,10,11,12,13,14,15), of "(cs@es)"] 2(6,16)
        by fastforce
    next
      case False
      hence "\<not>const_list (cs@es)"
        unfolding const_list_def
        by simp
      moreover
      have "\<exists>ts''. (\<S>\<bullet>\<C> \<turnstile> (cs @ es) : ([] _> ts''))"
        using 2(5,6)
        by (metis append.assoc e_type_comp_conc1)
      moreover
      have "\<And>k lholed. \<not> Lfilled k lholed [$Return] (cs @ es)"
      proof -
        {
          assume "\<exists>k lholed. Lfilled k lholed [$Return] (cs @ es)"
          then obtain k lholed where local_assms:"Lfilled k lholed [$Return] (cs @ es)"
            by blast
          hence "\<exists>lholed'. Lfilled k lholed' [$Return] (cs @ es @ [e])"
          proof (cases rule: Lfilled.cases)
            case (L0 vs es')
            obtain lholed' where "lholed' = LBase vs (es'@[e])"
              by blast
            thus ?thesis
              using L0
              by (metis Lfilled.intros(1) append.assoc)
          next
            case (LN vs ts es' l es'' k lfilledk)
            obtain lholed' where "lholed' = LRec vs ts es' l (es''@[e])"
              by blast
            thus ?thesis
              using LN
              by (metis Lfilled.intros(2) append.assoc)
          qed
          hence False
            using 2(6,9)
            by blast
        }
        thus "\<And>k lholed. \<not> Lfilled k lholed [$Return] (cs @ es)"
          by blast
      qed
      moreover
      have "\<And>i k lholed.  Lfilled k lholed [$Br i] (cs @ es) \<Longrightarrow> i < k"
      proof -
        {
          assume "\<exists>i k lholed.  Lfilled k lholed [$Br i] (cs @ es) \<and> \<not>(i < k)"
          then obtain i k lholed where local_assms:"Lfilled k lholed [$Br i] (cs @ es)" "\<not>(i < k)"
            by blast
          hence "\<exists>lholed'.  Lfilled k lholed' [$Br i] (cs @ es @ [e]) \<and> \<not>(i < k)"
          proof (cases rule: Lfilled.cases)
            case (L0 vs es')
            obtain lholed' where "lholed' = LBase vs (es'@[e])"
              by blast
            thus ?thesis
              using L0 local_assms(2)
              by (metis Lfilled.intros(1) append.assoc)
          next
            case (LN vs ts es' l es'' k lfilledk)
            obtain lholed' where "lholed' = LRec vs ts es' l (es''@[e])"
              by blast
            thus ?thesis
              using LN local_assms(2)
              by (metis Lfilled.intros(2) append.assoc)
          qed
          hence False
            using 2(6,10)
            by blast
        }
        thus "\<And>i k lholed.  Lfilled k lholed [$Br i] (cs @ es) \<Longrightarrow> i < k"
          by blast
      qed
      moreover
      note preds = calculation
      show ?thesis
      proof (cases "cs @ es = [Trap]")
        case True
        thus ?thesis
          using reduce_simple.trap[of _ "(LBase [] [e])"]
                Lfilled.intros(1)[of "[]" "LBase [] [e]" "[e]" "cs @ es"]
                reduce.intros(1) 2(6,11)
          unfolding const_list_def
          by (metis append.assoc append_Nil list.pred_inject(1))
      next
        case False
        thus ?thesis
          using 2(3)[OF _ _ 2(7,8) _ _ _ _  2(13,14,15)] preds 2(6,16)
                progress_L0[of s vs "(cs @ es)" _ _ _ _ "[]" "[e]"]
          unfolding const_list_def
          by (metis append.assoc append_Nil list.pred_inject(1))
      qed
    qed
  next
    case (3 \<S> \<C> es t1s t2s ts)
    thus ?case
      by fastforce
  next
    case (4 \<S> \<C>)
    have cs_es_def:"Lfilled 0 (LBase cs []) [Trap] cs_es"
      using Lfilled.intros(1)[OF 4(3), of _ "[]" "[Trap]"] 4(2)
      by fastforce
    thus ?case
      using reduce_simple.trap[OF 4(7) cs_es_def] reduce.intros(1)
      by blast
  next
  case (5 \<S> ts j vls es n \<C>)
    consider (1) "(\<And>k lholed. \<not> Lfilled k lholed [$Return] es)"
                 "(\<And>k lholed i. (Lfilled k lholed [$Br i] es) \<Longrightarrow> i < k)"
                 "es \<noteq> [Trap]"
                 "\<not> const_list es"
           | (2) "\<exists>k lholed. Lfilled k lholed [$Return] es"
           | (3) "const_list es \<or> (es = [Trap])"
           | (4) "\<exists>k lholed i. (Lfilled k lholed [$Br i] es) \<and> i \<ge> k"
      using not_le_imp_less
      by blast
    thus ?case
    proof (cases)
      case 1
      obtain s' vs'' a where temp1:"\<lparr>s;vls;es\<rparr> \<leadsto>_ j \<lparr>s';vs'';a\<rparr>"
        using 5(3)[OF 1(1) _ 1(3,4) 5(12)] 1(2)
        by fastforce
      show ?thesis
        using reduce.intros(24)[OF temp1, of vs] progress_L0[where ?cs = cs, OF _ 5(6)] 5(5)
        by fastforce
    next
      case 2
      then obtain k lholed where local_assms:"(Lfilled k lholed [$Return] es)"
        by blast
      then obtain lholed' vs' \<C>' where lholed'_def:"(Lfilled k lholed' (vs'@[$Return]) es)"
                                                   "\<S>\<bullet>\<C>' \<turnstile> vs' : ([] _> ts)"
                                                   "const_list vs'"
        using progress_LN_return[OF local_assms, of \<S> _ ts ts] s_type_unfold[OF 5(1)]
        by fastforce
      hence temp1:"\<exists>a. \<lparr>[Local n j vls es]\<rparr> \<leadsto> \<lparr>vs'\<rparr>"
        using reduce_simple.return[OF lholed'_def(3)]
              e_type_const_list[OF lholed'_def(3,2)] 5(2)
        by fastforce
      show ?thesis
        using temp1 progress_L0[OF reduce.intros(1) 5(6)] 5(5)
        by fastforce
    next
      case 3
      then consider (1) "const_list es" | (2) "es = [Trap]"
        by blast
      hence temp1:"\<exists>a. \<lparr>s;vs;[Local n j vls es]\<rparr> \<leadsto>_ i \<lparr>s;vs;es\<rparr>"
      proof (cases)
        case 1
        have "length es = length ts"
          using s_type_unfold[OF 5(1)] e_type_const_list[OF 1]
          by fastforce
        thus ?thesis
          using reduce_simple.local_const[OF 1] reduce.intros(1) 5(2)
          by fastforce
      next
        case 2
        thus ?thesis
          using reduce_simple.local_trap reduce.intros(1)
          by fastforce
      qed
      thus ?thesis
        using progress_L0[where ?cs = cs, OF _ 5(6)] 5(5)
        by fastforce
    next
      case 4
      then obtain k' lholed' i' where temp1:"Lfilled k' lholed' [$Br (k'+i')] es"
        using le_Suc_ex
        by blast
      obtain \<C>' where c_def:"\<C>' = ((s_inst \<S>)!j)\<lparr>local := (local ((s_inst \<S>)!j)) @ (map typeof vls), return := Some ts\<rparr>"
        by blast
      hence  es_def:"\<S>\<bullet>\<C>' \<turnstile> es : ([] _> ts)" "j < length (s_inst \<S>)"
        using 5(1) s_type_unfold
        by fastforce+
      hence "length (label \<C>') = 0"
        using c_def store_local_label_empty 5(12)
        by fastforce
      thus ?thesis 
        using progress_LN1[OF temp1 es_def(1)]
        by linarith
    qed
  next
    case (6 \<S> cl tf \<C>)
    obtain ts'' where ts''_def:"\<S>\<bullet>\<C> \<turnstile> cs : ([] _> ts'')" "\<S>\<bullet>\<C> \<turnstile> [Callcl cl] : (ts'' _> ts')"
      using 6(2,3) e_type_comp_conc1
      by fastforce
    obtain ts_c t1s t2s where cl_def:"(ts'' = ts_c @ t1s)"
                                     "(ts' = ts_c @ t2s)"
                                     "cl_type cl = (t1s _> t2s)"
      using e_type_callcl[OF ts''_def(2)]
      by fastforce
    obtain vs1 vs2 where vs_def:"\<S>\<bullet>\<C> \<turnstile> vs1 : ([] _> ts_c)"
                                "\<S>\<bullet>\<C> \<turnstile> vs2 : (ts_c _> ts_c @ t1s)"
                                "cs = vs1 @ vs2"
                                "const_list vs1"
                                "const_list vs2"
      using e_type_const_list_cons[OF 6(4)] ts''_def(1) cl_def(1)
      by fastforce
    have l:"(length vs2) = (length t1s)"
      using e_type_const_list vs_def(2,5)
      by fastforce
    show ?case
    proof (cases cl)
      case (Func_native x11 x12 x13 x14)
      hence func_native_def:"cl = Func_native x11 (t1s _> t2s) x13 x14"
        using cl_def(3)
        unfolding cl_type_def
        by simp
      have "\<exists>a a'. \<lparr>s;vs;vs2 @ [Callcl cl]\<rparr> \<leadsto>_ i \<lparr>s;vs;a\<rparr>"
        using reduce.intros(5)[OF func_native_def] e_type_const_conv_vs[OF vs_def(5)] l
        unfolding n_zeros_def
        by fastforce
      thus ?thesis
        using progress_L0 vs_def(3,4) 6(3)
        by fastforce
    next
      case (Func_host x21 x22)
      hence func_host_def:"cl = Func_host (t1s _> t2s) x22"
        using cl_def(3)
        unfolding cl_type_def
        by simp
      obtain vcs where vcs_def:"vs2 = $$* vcs"
        using e_type_const_conv_vs[OF vs_def(5)]
        by blast
      fix hs
      have "\<exists>s' a a'. \<lparr>s;vs;vs2 @ [Callcl cl]\<rparr> \<leadsto>_ i \<lparr>s';vs;a\<rparr>"
      proof (cases "host_apply s (t1s _> t2s) x22 vcs hs")
        case None
        thus ?thesis
          using reduce.intros(7)[OF func_host_def] l vcs_def
          by fastforce
      next
        case (Some a)
        then obtain s' vcs' where ha_def:"host_apply s (t1s _> t2s) x22 vcs hs = Some (s', vcs')"
          by (metis surj_pair)
        have "list_all2 types_agree t1s vcs"
          using e_typing_imp_list_types_agree vs_def(2,4) vcs_def
          by simp
        thus ?thesis
          using reduce.intros(6)[OF func_host_def _ _ _ _ ha_def] l vcs_def
                host_apply_respect_type[OF _ ha_def]
          by fastforce
      qed
      thus ?thesis
        using vs_def(3,4) 6(3) progress_L0
        by fastforce
    qed
  next
    case (7 \<S> \<C> e0s ts t2s es n)
    consider (1) "(\<And>k lholed. \<not> Lfilled k lholed [$Return] es)"
                 "(\<And>k lholed i. (Lfilled k lholed [$Br i] es) \<Longrightarrow> i < k)"
                 "es \<noteq> [Trap]"
                 "\<not> const_list es"
           | (2) "\<exists>k lholed. Lfilled k lholed [$Return] es"
           | (3) "const_list es \<or> (es = [Trap])"
           | (4) "\<exists>k lholed i. (Lfilled k lholed [$Br i] es) \<and> i = k"
           | (5) "\<exists>k lholed i. (Lfilled k lholed [$Br i] es) \<and> i > k"
      using linorder_neqE_nat
      by blast
    thus ?case
    proof (cases)
      case 1
      have temp1:"es = [] @ es" "const_list []"
        unfolding const_list_def
        by auto
      have temp2:"\<S>\<bullet>\<C>\<lparr>label := [ts] @ label \<C>\<rparr> \<turnstile> [] : ([] _> [])"
        using b_e_typing.empty e_typing_s_typing.intros(1)
        by fastforce
      have "\<exists>s' vs' a. \<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';a\<rparr>"
        using 7(5)[OF 7(2), of "[]" "[]", OF temp1 temp2 1(1) _ 1(3,4) 7(14,15)]
              1(2) 7(16,17)
        unfolding const_list_def
        by fastforce
      then obtain s' vs' a where red_def:"\<lparr>s;vs;es\<rparr> \<leadsto>_ i \<lparr>s';vs';a\<rparr>"
        by blast
      have temp4:"\<And>es. Lfilled 0 (LBase [] []) es es"
        using Lfilled.intros(1)[of "[]" "(LBase [] [])" "[]"]
        unfolding const_list_def
        by fastforce
      hence temp5:"Lfilled 1 (LRec cs n e0s (LBase [] []) []) es (cs@[Label n e0s es])"
        using Lfilled.intros(2)[of cs "(LRec cs n e0s (LBase [] []) [])" n e0s "(LBase [] [])" "[]" 0 es es] 7(8)
        unfolding const_list_def
        by fastforce
      have temp6:"Lfilled 1 (LRec cs n e0s (LBase [] []) []) a (cs@[Label n e0s a])"
        using temp4 Lfilled.intros(2)[of cs "(LRec cs n e0s (LBase [] []) [])" n e0s "(LBase [] [])" "[]" 0 a a] 7(8)
        unfolding const_list_def
        by fastforce
      show ?thesis
        using reduce.intros(23)[OF _ temp5 temp6] 7(7) red_def
        by fastforce
    next
      case 2
      then obtain k lholed where "(Lfilled k lholed [$Return] es)"
        by blast
      hence "(Lfilled (k+1) (LRec cs n e0s lholed []) [$Return] (cs@[Label n e0s es]))"
        using Lfilled.intros(2) 7(8)
        by fastforce
      thus ?thesis
        using 7(10)[of "k+1"] 7(7)
      by fastforce
    next
      case 3
      hence temp1:"\<exists>a. \<lparr>s;vs;[Label n e0s es]\<rparr> \<leadsto>_ i \<lparr>s;vs;es\<rparr>"
        using reduce_simple.label_const reduce_simple.label_trap reduce.intros(1)
        by fastforce
      show ?thesis
        using progress_L0[OF _ 7(8)] 7(7) temp1
        by fastforce
    next
      case 4
      then obtain k lholed where lholed_def:"(Lfilled k lholed [$Br (k+0)] es)"
        by fastforce
      then obtain lholed' vs' \<C>' where lholed'_def:"(Lfilled k lholed' (vs'@[$Br (k)]) es)"
                                                   "\<S>\<bullet>\<C>' \<turnstile> vs' : ([] _> ts)"
                                                   "const_list vs'"
        using progress_LN[OF lholed_def 7(2), of ts]
        by fastforce
      have "\<exists>es' a. \<lparr>[Label n e0s es]\<rparr> \<leadsto> \<lparr>vs'@e0s\<rparr>"
        using reduce_simple.br[OF lholed'_def(3) _ lholed'_def(1)] 7(3)
              e_type_const_list[OF lholed'_def(3,2)]
        by fastforce
      hence "\<exists>es' a. \<lparr>s;vs;[Label n e0s es]\<rparr> \<leadsto>_ i \<lparr>s;vs;es'\<rparr>"
        using reduce.intros(1)
        by fastforce
      thus ?thesis
        using progress_L0 7(7,8)
        by fastforce
    next
      case 5
      then obtain i k lholed where lholed_def:"(Lfilled k lholed [$Br i] es)" "i > k"
        using less_imp_add_positive
        by blast
      have k1_def:"Lfilled (k+1) (LRec cs n e0s lholed []) [$Br i] cs_es"
        using 7(7) Lfilled.intros(2)[OF 7(8) _ lholed_def(1), of _ n e0s "[]"]
        by fastforce
      thus ?thesis
        using 7(11)[OF k1_def] lholed_def(2)
        by simp
    qed
  next
    case (8 i \<S> tvs vs \<C> rs es ts)
    have "length (local \<C>) = length vs"
      using 8(2,3) store_local_label_empty[OF 8(1,11)]
      by fastforce
    moreover
    have "Option.is_none (memory \<C>) = Option.is_none (inst.mem ((inst s)!i))"
      using store_mem_exists[OF 8(1,11)] 8(3)
      by simp
    ultimately show ?case
      using 8(6)[OF 8(4) _ _ _ 8(7,8,9,10,11,1)]
            e_typing_s_typing.intros(1)[OF b_e_typing.empty[of \<C>]]
      unfolding const_list_def
      by fastforce
  qed
  show ?thesis
    using prems2[OF assms]
    by fastforce
qed

lemma progress_e1:
  assumes "\<S>\<bullet>None \<tturnstile>_i vs;es : ts"
  shows "\<not>(Lfilled k lholed [$Return] es)"
proof -
  {
    assume "\<exists>k lholed. (Lfilled k lholed [$Return] es)"
    then obtain k lholed where local_assms:"(Lfilled k lholed [$Return] es)"
      by blast
    obtain \<C> where c_def:"i < length (s_inst \<S>)"
                   "\<C> = ((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i)) @ (map typeof vs), return := None\<rparr>"
                   "(\<S>\<bullet>\<C> \<turnstile> es : ([] _> ts))"
      using assms s_type_unfold
      by fastforce
    have "\<exists>rs. return \<C> = Some rs"
      using local_assms c_def(3)
    proof (induction "[$Return]" es arbitrary: \<C> ts rule: Lfilled.induct)
      case (L0 vs lholed es')
      thus ?case
        using e_type_comp_conc2[OF L0(3)] unlift_b_e[of \<S> \<C> "[Return]"] b_e_type_return
        by fastforce
    next
      case (LN vs lholed tls es' l es'' k lfilledk)
      thus ?case
        using e_type_comp_conc2[OF LN(5)] e_type_label[of \<S> \<C> tls es' lfilledk]
        by fastforce
    qed
    hence False
      using c_def(2)
      by fastforce
  }
  thus "\<And> k lholed. \<not>(Lfilled k lholed [$Return] es)"
    by blast
qed

lemma progress_e2:
  assumes "\<S>\<bullet>None \<tturnstile>_i vs;es : ts"
          "store_typing s \<S>"
  shows "(Lfilled k lholed [$Br (j)] es) \<Longrightarrow> j < k"
proof -
  {
    assume "(\<exists>i k lholed. (Lfilled k lholed [$Br (i)] es) \<and> i \<ge> k)"
    then obtain j k lholed where local_assms:"(Lfilled k lholed [$Br (k+j)] es)"
      by (metis le_iff_add)
    obtain \<C> where c_def:"i < length (s_inst \<S>)"
                   "\<C> = ((s_inst \<S>)!i)\<lparr>local := (local ((s_inst \<S>)!i)) @ (map typeof vs), return := None\<rparr>"
                   "(\<S>\<bullet>\<C> \<turnstile> es : ([] _> ts))"
      using assms s_type_unfold
      by fastforce
    have "j < length (label \<C>)"
      using progress_LN1[OF local_assms c_def(3)]
      by -
    hence False
      using store_local_label_empty(1)[OF c_def(1) assms(2)] c_def(2)
      by fastforce
  }
  thus "(\<And> j k lholed. (Lfilled k lholed [$Br (j)] es) \<Longrightarrow> j < k)"
    by fastforce
qed

lemma progress_e3:
  assumes "\<S>\<bullet>None \<tturnstile>_i vs;cs_es : ts'"
          "cs_es \<noteq> [Trap]"
          "\<not> const_list (cs_es)"
          "store_typing s \<S>"
  shows "\<exists>a s' vs' es'. \<lparr>s;vs;cs_es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  using assms progress_e progress_e1 progress_e2
  by fastforce

end