section \<open>Program Analysis\<close>
theory IMP2_Program_Analysis
imports "../basic/Annotated_Syntax" "../lib/Subgoal_Focus_Some" "../parser/Parser" IMP2_Basic_Decls
begin
  subsection \<open>Analysis Simproc\<close>

  
  definition [simp]: "ANALYZE x \<equiv> x"
  (*lemma ANALYZE_cong[named_ss vcg_bb cong]: "ANALYZE x = ANALYZE x" by simp*)
  
  simproc_setup ANALYZE ("ANALYZE x") 
    = \<open>fn _ => fn ctxt => let
    
        val analysis_unfolds = 
          @{thm ANALYZE_def} 
          :: Named_Theorems.get ctxt @{named_theorems analysis_unfolds}
          @ Named_Theorems.get ctxt @{named_theorems vcg_annotation_defs}
    
        val unfold_conv = 
           map (Local_Defs.meta_rewrite_rule ctxt #> perhaps (try Drule.abs_def)) analysis_unfolds
        |> Raw_Simplifier.rewrite ctxt true
    
    in
      unfold_conv #> SOME
    end  
  \<close>
  declare [[simproc del: ANALYZE]]

  declaration \<open>fn _ => Named_Simpsets.map_ctxt @{named_simpset vcg_bb} (
    fn ctxt => ctxt addsimprocs [@{simproc ANALYZE}]
  )\<close>

  (* TODO: There's a more general concept here: 
    Activating specific simpsets depending on the context, or, in this case, a trigger constant.
    DUP with STRIP_ANNOT in VCG
  *)

  
  lemmas [analysis_unfolds] = Inline_def Params_def AssignIdx_retv_def ArrayCpy_retv_def
  

  subsection \<open>Modifies Sets\<close>
  
  definition modifies :: "vname set \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool" where
    "modifies vars s\<^sub>1 s\<^sub>2 = (\<forall>x. x\<notin>vars \<longrightarrow> s\<^sub>1 x = s\<^sub>2 x)"
  
  context notes[simp] = modifies_def begin
    lemma modifies_refl[intro!, simp]: "modifies vs a a" by simp
    lemma modifies_sym[sym]: "modifies vs a b \<Longrightarrow> modifies vs b a" by simp
    lemma modifies_trans'[trans]: "modifies vs\<^sub>1 a b \<Longrightarrow> modifies vs\<^sub>2 b c \<Longrightarrow> modifies (vs\<^sub>1\<union>vs\<^sub>2) a c" by simp
    lemma modifies_trans[trans]: "modifies vs a b \<Longrightarrow> modifies vs b c \<Longrightarrow> modifies vs a c" by simp
  
    (* Test for correct order of trans-rules *)
    notepad begin
      fix vs a b c
      assume "modifies vs a b"
      also assume "modifies vs b c"
      finally have "modifies vs a c" . (* This must be trivial. If you get vs\<union>vs, something went wrong! *)
    end
    
    
    lemma modifies_join: "\<lbrakk> modifies vs\<^sub>1 a b; modifies vs\<^sub>2 a b \<rbrakk> \<Longrightarrow> modifies (vs\<^sub>1\<inter>vs\<^sub>2) a b" by auto
    
    lemma modifies_mono: "\<lbrakk> vs\<^sub>1\<subseteq>vs\<^sub>2; modifies vs\<^sub>1 a b \<rbrakk> \<Longrightarrow> modifies vs\<^sub>2 a b" by auto
    
    lemma modifies_equals: "modifies vs s s' \<Longrightarrow> x\<notin>vs \<Longrightarrow> s x = s' x" by auto
    lemma modifies_upd: 
      "x\<in>vs \<Longrightarrow> modifies vs s (s'(x:=v)) \<longleftrightarrow> modifies vs s s'" 
      "x\<in>vs \<Longrightarrow> modifies vs (s(x:=v)) s' \<longleftrightarrow> modifies vs s s'" 
      by auto
      
    lemma modifies_split: "modifies vs (<l|g>) (<l'|g'>) 
      \<longleftrightarrow> modifies (Collect is_global \<union> vs) l l' \<and> modifies (Collect is_local \<union> vs) g g'"  
      apply (auto simp: combine_query) by (metis combine_query)
      
  end  
    
  definition "wp_mod \<pi> vs c Q s = wp \<pi> c (\<lambda>s'. modifies vs s' s \<and> Q s') s "
  definition "wlp_mod \<pi> vs c Q s = wlp \<pi> c (\<lambda>s'. modifies vs s' s \<and> Q s') s "
    
  subsubsection \<open>Simplification of Modifies Tags\<close>  
    
  ML \<open>
  
    val simp_modifies_tac = let
      fun is_modifies _ ct = case Thm.term_of ct of _$(Const (@{const_name modifies},_)$_$_$_) => true | _ => false
      fun dest_modifies (Const _ $ (Const (@{const_name modifies},_)$vs$s$d)) = (vs,s,d)
        | dest_modifies t = raise TERM("dest_modifies",[t])
        
        
    in
      Subgoal_Focus_Some.FOCUS_SOME_PREMS is_modifies (fn {context=ctxt, prems, concl, ...} => let
      
        val sts = map (#2 o dest_modifies o Thm.prop_of) prems |> Termtab.make_set
  
        fun collect_vars (a$b) = if Termtab.defined sts a then Termtab.insert_set b else collect_vars a o collect_vars b
          | collect_vars (Abs (_,_,t)) = collect_vars t
          | collect_vars _ = I
            
        val vars = 
          Termtab.empty
          |> collect_vars (Thm.term_of concl) o fold collect_vars (map Thm.prop_of prems)
          |> Termtab.keys 
          |> map (Thm.cterm_of ctxt)
  
        val ctxt_bb = Named_Simpsets.put @{named_simpset vcg_bb} ctxt  
        fun mk_mod_thm x thm = let
          val thm = @{thm modifies_equals} OF [thm]
          fun is_triv thm = case Thm.prop_of thm of @{prop "True"} => true | _ => false
          
          val thm = Drule.infer_instantiate' ctxt [SOME x] thm
            |> full_simplify ctxt_bb
        in
          if is_triv thm then NONE else SOME thm
        end
          
        val thms = map_product (mk_mod_thm) vars prems |> map_filter I 
        
        val ctxt = Simplifier.put_simpset HOL_basic_ss ctxt addsimps thms
        
      
      in HEADGOAL (asm_full_simp_tac ctxt) end)
    end
  \<close>
  
  method_setup i_vcg_modifies_simp = \<open>Scan.succeed (SIMPLE_METHOD' o simp_modifies_tac)\<close>
  
  
  subsubsection \<open>Syntactic Approximation of Modifies Set\<close>

  primrec lhsv' :: "com \<Rightarrow> vname set" where
    "lhsv' (x[_] ::= _) = {x}"
  | "lhsv' (x[] ::= _) = {x}"
  | "lhsv' (CLEAR x[]) = {x}"
  | "lhsv' (Assign_Locals l) = Collect is_local"
  | "lhsv' SKIP = {}"  
  | "lhsv' (c\<^sub>1;; c\<^sub>2) = lhsv' c\<^sub>1 \<union> lhsv' c\<^sub>2"
  | "lhsv' (IF _ THEN c\<^sub>1 ELSE c\<^sub>2) = lhsv' c\<^sub>1 \<union> lhsv' c\<^sub>2"
  | "lhsv' (WHILE _ DO c) = lhsv' c"
  | "lhsv' (SCOPE c) = Set.filter is_global (lhsv' c)"
  | "lhsv' (PCall p) = {}"
  | lhsv'_pscope_simp_orig[simp del]: 
    "lhsv' (PScope \<pi> c) = \<Union>(ran (map_option lhsv' o \<pi>)) \<union> lhsv' c"
  
  definition "lhsv\<pi> \<pi> \<equiv> (\<Union>c\<in>ran \<pi>. lhsv' c)"
  
  lemma lhsv'_pscope_simp[simp]: "lhsv' (PScope \<pi> c) = lhsv\<pi> \<pi> \<union> lhsv' c"
    by (auto simp: ran_def lhsv'_pscope_simp_orig lhsv\<pi>_def)

  lemma lhsv\<pi>_empty: "lhsv\<pi> Map.empty = {}" by (auto simp: lhsv\<pi>_def)
  lemma lhsv\<pi>_upd: "m p = None \<Longrightarrow> lhsv\<pi> (m(p\<mapsto>c)) = lhsv' c \<union> lhsv\<pi> m" 
    apply (auto simp: lhsv\<pi>_def ran_def)
    by (metis option.simps(3))

  lemmas lhsv\<pi>_maplet[simp] = lhsv\<pi>_empty lhsv\<pi>_upd
  
  notepad begin
    have "lhsv\<pi> [''foo'' \<mapsto> \<^imp>\<open>a=5\<close>, ''bar'' \<mapsto> \<^imp>\<open>c=7; b=5; rec foo()\<close>] = {''a'', ''b'', ''c''}"
      by (simp add: Params_def)
  end

  
  primrec lhsv :: "program \<Rightarrow> com \<Rightarrow> vname set" where
    "lhsv \<pi> (x[_] ::= _) = {x}"
  | "lhsv \<pi> (x[] ::= _) = {x}"
  | "lhsv \<pi> (CLEAR x[]) = {x}"
  | "lhsv \<pi> (Assign_Locals l) = Collect is_local"
  | "lhsv \<pi> SKIP = {}"  
  | "lhsv \<pi> (c\<^sub>1;; c\<^sub>2) = lhsv \<pi> c\<^sub>1 \<union> lhsv \<pi> c\<^sub>2"
  | "lhsv \<pi> (IF _ THEN c\<^sub>1 ELSE c\<^sub>2) = lhsv \<pi> c\<^sub>1 \<union> lhsv \<pi> c\<^sub>2"
  | "lhsv \<pi> (WHILE _ DO c) = lhsv \<pi> c"
  | "lhsv \<pi> (SCOPE c) = Set.filter is_global (lhsv \<pi> c)"
  | "lhsv \<pi> (PCall p) = lhsv\<pi> \<pi>"
  | "lhsv \<pi> (PScope \<pi>' c) = lhsv\<pi> \<pi>' \<union> lhsv' c"
  
  
  text \<open>Install special rule for procedure scope\<close>  
  lemmas [named_ss vcg_bb] = lhsv'.simps
  lemmas [named_ss vcg_bb del] = lhsv'_pscope_simp_orig 
  lemmas [named_ss vcg_bb] = lhsv'_pscope_simp
  
  lemmas [named_ss vcg_bb] = lhsv.simps
  lemmas [named_ss vcg_bb] = lhsv\<pi>_maplet
    
  lemmas [named_ss vcg_bb] = is_global.simps
  
  
          
    
  lemma modifies_lhsv'_gen:
    assumes "lhsv\<pi> \<pi> \<subseteq> vs"
    assumes "lhsv' c \<subseteq> vs"
    assumes "\<pi>: (c,s) \<Rightarrow> t"
    shows "modifies vs t s"
    using assms(3,1,2)
  proof (induction arbitrary: vs)
    case (Scope \<pi> c s s')
    from Scope.IH[where vs="vs \<union> Collect is_local"] Scope.prems 
    show ?case by (fastforce simp: modifies_def combine_states_def) 
  next
    case (PCall \<pi> p c s t)
    then show ?case by (auto simp: ran_def lhsv\<pi>_def)
  next
    case (PScope \<pi>' p c s t \<pi>)
    then show ?case by (simp add: SUP_le_iff ranI lhsv\<pi>_def)
  qed (auto simp: modifies_def combine_states_def)

  lemma modifies_lhsv\<pi>:
    assumes "\<pi>: (c, s) \<Rightarrow> t"
    assumes "\<pi> p = Some c"
    shows "modifies (lhsv\<pi> \<pi>) t s"
    apply (rule modifies_lhsv'_gen[OF _ _ assms(1)])
    using assms(2) by (auto simp: lhsv\<pi>_def ran_def)

  lemma lhsv_approx: "lhsv \<pi>' c \<subseteq> lhsv\<pi> \<pi>' \<union> lhsv' c" 
    apply (induction c arbitrary: \<pi>')
              apply auto
    apply (auto simp: lhsv\<pi>_def)
    done
  
              

  lemma modifies_lhsv:
    assumes "\<pi>: (c, s) \<Rightarrow> t"
    shows "modifies (lhsv \<pi> c) t s"
    using assms
    apply (induction)
                apply (all \<open>(auto simp: modifies_def combine_states_def; fail)?\<close>)
     subgoal by (auto simp: modifies_lhsv\<pi>) []
    subgoal using lhsv_approx by (auto simp: modifies_def)
    done
    
    
      
  lemma wp_strengthen_modset: "wp \<pi> c Q s \<Longrightarrow> wp \<pi> c (\<lambda>s'. Q s' \<and> modifies (lhsv \<pi> c) s' s) s"
    unfolding wp_def 
    by (blast intro: modifies_lhsv)
  
  lemma wlp_strengthen_modset: "wlp \<pi> c Q s \<Longrightarrow> wlp \<pi> c (\<lambda>s'. Q s' \<and> modifies (lhsv \<pi> c) s' s) s"
    unfolding wlp_def 
    by (blast intro: modifies_lhsv)

  lemma wp_mod_lhsv_eq: "wp_mod \<pi> (lhsv \<pi> c) c Q s = wp \<pi> c Q s"
    unfolding wp_mod_def
    using modifies_lhsv wp_def by auto
  
  lemma wlp_mod_lhsv_eq: "wlp_mod \<pi> (lhsv \<pi> c) c Q s = wlp \<pi> c Q s"
    unfolding wlp_mod_def
    using modifies_lhsv wlp_def by auto

    
  subsubsection \<open>Hoare-Triple with Modifies-Set\<close>
  text \<open>We define a Hoare-Triple that contains a modifies declaration\<close>
  definition "HT_mods \<pi> mods P c Q \<equiv> HT \<pi> P c (\<lambda>s\<^sub>0 s. modifies mods s s\<^sub>0 \<and> Q s\<^sub>0 s)"
  definition "HT_partial_mods \<pi> mods P c Q \<equiv> HT_partial \<pi> P c (\<lambda>s\<^sub>0 s. Q s\<^sub>0 s \<and> modifies mods s s\<^sub>0)"

  lemma HT_mods_cong[named_ss vcg_bb cong]:
    assumes "vs = vs'"
    assumes "P=P'"
    assumes "c=c'"
    assumes "\<And>s\<^sub>0 s. modifies vs s s\<^sub>0 \<Longrightarrow> Q s\<^sub>0 s = Q' s\<^sub>0 s"
    shows "HT_mods \<pi> vs P c Q = HT_mods \<pi> vs' P' c' Q'"
    unfolding HT_mods_def HT_def using assms
    by (auto intro: wp_conseq)
    
  lemma HT_partial_mods_cong[named_ss vcg_bb cong]:
    assumes "vs = vs'"
    assumes "P=P'"
    assumes "c=c'"
    assumes "\<And>s\<^sub>0 s. modifies vs s s\<^sub>0 \<Longrightarrow> Q s\<^sub>0 s = Q' s\<^sub>0 s"
    shows "HT_partial_mods \<pi> vs P c Q = HT_partial_mods \<pi> vs' P' c' Q'"
    unfolding HT_partial_mods_def HT_partial_def using assms
    by (auto intro: wlp_conseq)
  
  lemma vcg_wp_conseq:
    assumes "HT_mods \<pi> mods P c Q"
    assumes "P s"
    assumes "\<And>s'. \<lbrakk>modifies mods s' s; Q s s'\<rbrakk> \<Longrightarrow> Q' s'"
    shows "wp \<pi> c Q' s"
    using assms unfolding HT_mods_def HT_def
    by (metis (no_types, lifting) wp_def)
    
  lemma vcg_wlp_conseq:
    assumes "HT_partial_mods \<pi> mods P c Q"
    assumes "P s"
    assumes "\<And>s'. \<lbrakk>modifies mods s' s; Q s s'\<rbrakk> \<Longrightarrow> Q' s'"
    shows "wlp \<pi> c Q' s"
    using assms unfolding HT_partial_mods_def HT_partial_def
    by (metis (no_types, lifting) wlp_def)

  text \<open>The last rule allows us to re-use a total correctness verification in a partial 
    correctness proof.\<close>  
  lemma vcg_wlp_wp_conseq:
    assumes "HT_mods \<pi> mods P c Q"
    assumes "P s"
    assumes "\<And>s'. \<lbrakk>modifies mods s' s; Q s s'\<rbrakk> \<Longrightarrow> Q' s'"
    shows "wlp \<pi> c Q' s"
    using assms vcg_wp_conseq wp_imp_wlp by auto
    
  (*
    TODO: Rules for combining proofs over the same program!
  *)
        
    
    
    
subsection \<open>Free Variables of Expressions\<close> 

text \<open>This function computes the set of variables that occur in an expression\<close>
fun fv_aexp :: "aexp \<Rightarrow> vname set" where
  "fv_aexp (N _) = {}"
| "fv_aexp (Vidx x i) = insert x (fv_aexp i)"
| "fv_aexp (Unop f a) = fv_aexp a"
| "fv_aexp (Binop f a b) = fv_aexp a \<union> fv_aexp b"

    
declare fv_aexp.simps[named_ss vcg_bb]

lemma aval_eq_on_fv: "(\<forall>x\<in>fv_aexp a. s x = s' x) \<Longrightarrow> aval a s = aval a s'"
  by (induction a) auto
    
lemma aval_indep_non_fv: "x\<notin>fv_aexp a \<Longrightarrow> aval a (s(x:=y)) = aval a s"
  by (induction a) auto

lemma redundant_array_assignment: "(x[] ::= a;; a[] ::= x) \<sim> (x[] ::= a)"
  apply rule
   apply (auto)
   apply (metis ArrayCpy fun_upd_def fun_upd_idem_iff)
  by (metis ArrayCpy Seq fun_upd_apply fun_upd_idem)

lemma redundant_var_assignment: 
  assumes "x\<notin>fv_aexp i" "x\<notin>fv_aexp j"
  shows "(x[i] ::= Vidx a j;; a[j] ::= Vidx x i) \<sim> (x[i] ::= Vidx a j)"
  apply (rule)
  using assms[THEN aval_indep_non_fv]
   apply auto
  subgoal
    by (smt Assign' aval.simps(1) aval.simps(2) fun_upd_apply fun_upd_idem_iff)
  subgoal
    by (simp add: Assign' fun_upd_twist)
  subgoal
    by (smt Seq aval.simps(2) big_step.intros(2) fun_upd_def fun_upd_triv)
  done

    
end
