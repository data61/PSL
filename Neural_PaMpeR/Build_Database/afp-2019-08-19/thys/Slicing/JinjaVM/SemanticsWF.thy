chapter \<open>Equivalence of the CFG and Jinja\<close>

theory SemanticsWF imports JVMInterpretation "../Basic/SemanticsCFG" begin

declare rev_nth [simp add]

section \<open>State updates\<close>

text \<open>
The following abbreviations update the stack and the local variables (in the representation
as used in the CFG) according to a \<open>frame list\<close> as it is used in Jinja's
state representation.
\<close>

abbreviation update_stk :: "((nat \<times> nat) \<Rightarrow> val) \<Rightarrow> (frame list) \<Rightarrow> ((nat \<times> nat) \<Rightarrow> val)"
where
  "update_stk stk frs \<equiv> (\<lambda>(a, b).
    if length frs \<le> a then stk (a, b)
      else let xs = fst (frs ! (length frs - Suc a))
        in if length xs \<le> b then stk (a, b) else xs ! (length xs - Suc b))"

abbreviation update_loc :: "((nat \<times> nat) \<Rightarrow> val) \<Rightarrow> (frame list) \<Rightarrow> ((nat \<times> nat) \<Rightarrow> val)"
where
  "update_loc loc frs \<equiv> (\<lambda>(a, b).
    if length frs \<le> a then loc (a, b)
      else let xs = fst (snd (frs ! (length frs - Suc a)))
        in if length xs \<le> b then loc (a, b) else xs ! b)"

subsection \<open>Some simplification lemmas\<close>

lemma update_loc_s2jvm [simp]:
  "update_loc loc (snd(snd(state_to_jvm_state P cs (h,stk,loc)))) = loc"
  by (auto intro!: ext simp: nth_locss)

lemma update_stk_s2jvm [simp]:
  "update_stk stk (snd(snd(state_to_jvm_state P cs (h,stk,loc)))) = stk"
  by (auto intro!: ext simp: nth_stkss)

lemma update_loc_s2jvm' [simp]:
  "update_loc loc (zip (stkss P cs stk) (zip (locss P cs loc) cs)) = loc"
  by (auto intro!: ext simp: nth_locss)

lemma update_stk_s2jvm' [simp]:
  "update_stk stk (zip (stkss P cs stk) (zip (locss P cs loc) cs)) = stk"
  by (auto intro!: ext simp: nth_stkss)

lemma find_handler_find_handler_forD:
  "find_handler (P\<^bsub>wf\<^esub>) a h frs = (xp',h',frs')
  \<Longrightarrow> find_handler_for P (cname_of h a) (framestack_to_callstack frs) =
       framestack_to_callstack frs'"
  by (induct frs, auto)

lemma find_handler_nonempty_frs [simp]:
  "(find_handler P a h frs \<noteq> (None, h', []))"
  by (induct frs, auto)

lemma find_handler_heap_eqD:
  "find_handler P a h frs = (xp, h', frs') \<Longrightarrow> h' = h"
  by (induct frs, auto)

lemma find_handler_frs_decrD:
  "find_handler P a h frs = (xp, h', frs') \<Longrightarrow> length frs' \<le> length frs"
  by (induct frs, auto)

lemma find_handler_decrD [dest]:
  "find_handler P a h frs = (xp, h', f#frs) \<Longrightarrow> False"
  by (drule find_handler_frs_decrD, simp)

lemma find_handler_decrD' [dest]:
  "\<lbrakk> find_handler P a h frs = (xp,h',f#frs'); length frs = length frs' \<rbrakk> \<Longrightarrow> False"
  by (drule find_handler_frs_decrD, simp)

lemma Suc_minus_Suc_Suc [simp]:
  "b < n - 1 \<Longrightarrow> Suc (n - Suc (Suc b)) = n - Suc b"
  by simp

lemma find_handler_loc_fun_eq':
  "find_handler (P\<^bsub>wf\<^esub>) a h
    (zip (stkss P cs stk) (zip (locss P cs loc) cs)) =
  (xf, h', frs)
  \<Longrightarrow> update_loc loc frs = loc"
proof
  fix x
  obtain a' b' where x: "x = (a'::nat,b'::nat)" by fastforce
  assume find_handler: "find_handler (P\<^bsub>wf\<^esub>) a h
    (zip (stkss P cs stk) (zip (locss P cs loc) cs)) =
    (xf, h', frs)"
  thus "update_loc loc frs x = loc x"
  proof (induct cs)
    case Nil
    thus ?case by simp
  next
    case (Cons aa cs')
    then obtain C M pc where step_case: "find_handler (P\<^bsub>wf\<^esub>) a h
      (zip (stkss P ((C,M,pc) # cs') stk)
      (zip (locss P ((C,M,pc) # cs') loc) ((C,M,pc) # cs'))) =
      (xf, h', frs)"
      by (cases aa, clarsimp)
    note IH = \<open>find_handler (P\<^bsub>wf\<^esub>) a h
      (zip (stkss P cs' stk) (zip (locss P cs' loc) cs')) =
      (xf, h', frs) \<Longrightarrow>
      update_loc loc frs x = loc x\<close>
    show ?thesis
    proof (cases "match_ex_table (P\<^bsub>wf\<^esub>) (cname_of h a) pc (ex_table_of (P\<^bsub>wf\<^esub>) C M)")
      case None
      with step_case IH show ?thesis
        by simp
    next
      case (Some e)
      with step_case x
      show ?thesis
        by (cases "length cs' = a'",
            auto simp: nth_Cons' (* nth_locs *) nth_locss)
    qed
  qed
qed

lemma find_handler_loc_fun_eq:
  "find_handler (P\<^bsub>wf\<^esub>) a h (snd(snd(state_to_jvm_state P cs (h,stk,loc)))) = (xf,h',frs)
  \<Longrightarrow> update_loc loc frs = loc"
  by (simp add: find_handler_loc_fun_eq')

lemma find_handler_stk_fun_eq':
  "\<lbrakk>find_handler (P\<^bsub>wf\<^esub>) a h
    (zip (stkss P cs stk) (zip (locss P cs loc) cs)) =
  (None, h', frs);
  cd = length frs - 1;
  i = length (fst(hd(frs))) - 1 \<rbrakk>
  \<Longrightarrow> update_stk stk frs = stk((cd, i) := Addr a)"
proof
  fix x
  obtain a' b' where x: "x = (a'::nat,b'::nat)" by fastforce
  assume find_handler: "find_handler (P\<^bsub>wf\<^esub>) a h
    (zip (stkss P cs stk) (zip (locss P cs loc) cs)) =
    (None, h', frs)"
    and calldepth: "cd = length frs - 1"
    and idx: "i = length (fst (hd frs)) - 1"
  from find_handler have "frs \<noteq> []"
    by clarsimp
  then obtain stk' loc' C' M' pc' frs' where frs: "frs = (stk',loc',C',M',pc')#frs'"
    by (cases frs, fastforce+)
  from find_handler
  show "update_stk stk frs x = (stk((cd, i) := Addr a)) x"
  proof (induct cs)
    case Nil
    thus ?case by simp
  next
    case (Cons aa cs')
    then obtain C M pc where step_case: "find_handler (P\<^bsub>wf\<^esub>) a h
      (zip (stkss P ((C,M,pc) # cs') stk)
      (zip (locss P ((C,M,pc) # cs') loc) ((C,M,pc) # cs'))) =
      (None, h', frs)"
      by (cases aa, clarsimp)
    note IH = \<open>find_handler (P\<^bsub>wf\<^esub>) a h
      (zip (stkss P cs' stk) (zip (locss P cs' loc) cs')) =
      (None, h', frs) \<Longrightarrow>
      update_stk stk frs x = (stk((cd, i) := Addr a)) x\<close>
    show ?thesis
    proof (cases "match_ex_table (P\<^bsub>wf\<^esub>) (cname_of h a) pc (ex_table_of (P\<^bsub>wf\<^esub>) C M)")
      case None
      with step_case IH show ?thesis
        by simp
    next
      case (Some e)
      show ?thesis
      proof (cases "a' = length cs'")
        case True
        with Some step_case frs calldepth idx x
        show ?thesis
          by (fastforce simp: nth_Cons')
      next
        case False
        with Some step_case frs calldepth idx x
        show ?thesis
          by (fastforce simp: nth_Cons' nth_stkss)
      qed
    qed
  qed
qed

lemma find_handler_stk_fun_eq:
  "find_handler (P\<^bsub>wf\<^esub>) a h (snd(snd(state_to_jvm_state P cs (h,stk,loc)))) = (None,h',frs)
  \<Longrightarrow> update_stk stk frs = stk((length frs - 1, length (fst(hd(frs))) - 1) := Addr a)"
  by (simp add: find_handler_stk_fun_eq')

lemma f2c_emptyD [dest]:
  "framestack_to_callstack frs = [] \<Longrightarrow> frs = []"
  by (simp add: framestack_to_callstack_def)

lemma f2c_emptyD' [dest]:
  "[] = framestack_to_callstack frs \<Longrightarrow> frs = []"
  by (simp add: framestack_to_callstack_def)

lemma correct_state_imp_valid_callstack:
  "\<lbrakk> P,cs \<turnstile>\<^bsub>BV\<^esub> s \<surd>; fst (last cs) = C0; fst(snd (last cs)) = Main \<rbrakk>
  \<Longrightarrow> valid_callstack (P,C0,Main) cs"
proof (cases cs rule: rev_cases)
  case Nil
  thus ?thesis by simp
next
  case (snoc cs' y)
  assume bv_correct: "P,cs \<turnstile>\<^bsub>BV\<^esub> s \<surd>"
    and last_C: "fst (last cs) = C0"
    and last_M: "fst(snd (last cs)) = Main"
  with snoc obtain pcX where [simp]: "cs = cs'@[(C0,Main,pcX)]"
    by (cases "last cs", fastforce)
  obtain h stk loc where [simp]: "s = (h,stk,loc)"
    by (cases s, fastforce)
  from bv_correct show ?thesis
  proof (cases "snd(snd(state_to_jvm_state P cs s))")
    case Nil
    thus ?thesis
      by (cases cs', auto)
  next
    case [simp]: (Cons a frs')
    obtain stk' loc' C M pc where [simp]: "a = (stk', loc', C, M, pc)" by (cases a, fastforce)
    from Cons bv_correct show ?thesis
      apply clarsimp
    proof (induct cs' arbitrary: stk' loc' C M pc frs')
      case Nil
      thus ?case by (fastforce simp: bv_conform_def)
    next
      case (Cons a' cs'')
      then have [simp]: "a' = (C,M,pc)"
        by (cases a', fastforce)
      from Cons obtain T Ts mxs mxl "is" xt
        where sees_M: "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl,is,xt) in C"
        by (clarsimp simp: bv_conform_def correct_state_def)
      with Cons
      have "pc < length is"
        by (auto dest: sees_method_fun
                 simp: bv_conform_def)
      from wf_jvmprog_is_wf [of P] sees_M
      have "wt_method (P\<^bsub>wf\<^esub>) C Ts T mxs mxl is xt (P\<^bsub>\<Phi>\<^esub> C M)"
        by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
      with \<open>pc < length is\<close> sees_M
      have "length Ts = locLength P C M 0 - Suc mxl"
        by (auto dest!: list_all2_lengthD
                  simp: wt_method_def wt_start_def)
      with Cons sees_M show ?case
        by (cases cs'',
            (fastforce dest: sees_method_fun simp: bv_conform_def)+)
    qed
  qed
qed

declare correct_state_def [simp del]

lemma bool_sym: "Bool (a = b) = Bool (b = a)"
  by auto

lemma find_handler_exec_correct:
  "\<lbrakk>(P\<^bsub>wf\<^esub>),(P\<^bsub>\<Phi>\<^esub>) \<turnstile> state_to_jvm_state P cs (h,stk,loc) \<surd>;
    (P\<^bsub>wf\<^esub>),(P\<^bsub>\<Phi>\<^esub>) \<turnstile> find_handler (P\<^bsub>wf\<^esub>) a h
      (zip (stkss P cs stk) (zip (locss P cs loc) cs)) \<surd>;
    find_handler_for P (cname_of h a) cs = (C', M', pc') # cs'
  \<rbrakk> \<Longrightarrow>
  (P\<^bsub>wf\<^esub>),(P\<^bsub>\<Phi>\<^esub>) \<turnstile> (None, h,
    (stks (stkLength P C' M' pc')
      (\<lambda>a'. (stk((length cs', stkLength P C' M' pc' - Suc 0) := Addr a)) (length cs', a')),
     locs (locLength P C' M' pc') (\<lambda>a. loc (length cs', a)), C', M', pc') #
    zip (stkss P cs' stk) (zip (locss P cs' loc) cs')) \<surd>"
proof (induct cs)
  case Nil
  thus ?case by simp
next
  case (Cons aa cs)
  note state_correct = \<open>P\<^bsub>wf\<^esub>,P\<^bsub>\<Phi>\<^esub> \<turnstile> state_to_jvm_state P (aa # cs) (h, stk, loc) \<surd>\<close>
  note IH = \<open>\<lbrakk>P\<^bsub>wf\<^esub>,P\<^bsub>\<Phi>\<^esub> \<turnstile> state_to_jvm_state P cs (h, stk, loc) \<surd>;
         P\<^bsub>wf\<^esub>,P\<^bsub>\<Phi>\<^esub> \<turnstile> find_handler P\<^bsub>wf\<^esub> a h (zip (stkss P cs stk) (zip (locss P cs loc) cs)) \<surd>;
         find_handler_for P (cname_of h a) cs = (C', M', pc') # cs'\<rbrakk>
        \<Longrightarrow> P\<^bsub>wf\<^esub>,P\<^bsub>\<Phi>\<^esub> \<turnstile> (None, h,
                     (stks (stkLength P C' M' pc')
                       (\<lambda>a'. (stk((length cs', stkLength P C' M' pc' - Suc 0) := Addr a))
                              (length cs', a')),
                      locs (locLength P C' M' pc') (\<lambda>a. loc (length cs', a)), C', M', pc') #
                     zip (stkss P cs' stk) (zip (locss P cs' loc) cs')) \<surd>\<close>
  note trg_state_correct = \<open>P\<^bsub>wf\<^esub>,P\<^bsub>\<Phi>\<^esub> \<turnstile> find_handler P\<^bsub>wf\<^esub> a h
            (zip (stkss P (aa # cs) stk)
              (zip (locss P (aa # cs) loc) (aa # cs))) \<surd>\<close>
  note fhf = \<open>find_handler_for P (cname_of h a) (aa # cs) = (C', M', pc') # cs'\<close>
  obtain C M pc where [simp]: "aa = (C,M,pc)" by (cases aa, fastforce)
  note P_wf = wf_jvmprog_is_wf [of P]
  from state_correct
  have cs_state_correct: "P\<^bsub>wf\<^esub>,P\<^bsub>\<Phi>\<^esub> \<turnstile> state_to_jvm_state P cs (h, stk, loc) \<surd>"
    apply (auto simp: correct_state_def)
    apply (cases "zip (stkss P cs stk) (zip (locss P cs loc) cs)")
     by fastforce+
  show ?thesis
  proof (cases "match_ex_table (P\<^bsub>wf\<^esub>) (cname_of h a) pc (ex_table_of (P\<^bsub>wf\<^esub>) C M)")
    case None
    with trg_state_correct fhf cs_state_correct IH show ?thesis
      by clarsimp
  next
    case (Some xte)
    with IH trg_state_correct fhf state_correct show ?thesis
      apply (cases "stkLength P C' M' (fst xte)", auto)
       apply (clarsimp simp: correct_state_def)
      apply (auto simp: correct_state_def)
      apply (rule_tac x="Ts" in exI)
      apply (rule_tac x="T" in exI)
      apply (rule_tac x="mxs" in exI)
      apply (rule_tac x="mxl\<^sub>0" in exI)
      apply (rule_tac x="is" in exI)
      apply (rule conjI)
       apply (rule_tac x="xt" in exI)
       apply clarsimp
      apply clarsimp
      apply (drule sees_method_fun, fastforce, clarsimp)
      apply (auto simp: list_all2_Cons1)
       apply (rule list_all2_all_nthI)
        apply clarsimp
       apply clarsimp
       apply (frule_tac ys="zs" in list_all2_lengthD)
       apply clarsimp
       apply (drule_tac p="n" and ys="zs" in list_all2_nthD)
        apply clarsimp
       apply clarsimp
       apply (case_tac "length aa - Suc (length aa - snd xte + n) = length zs - Suc n")
        apply clarsimp
       apply clarsimp
      apply (rule list_all2_all_nthI)
       apply clarsimp
      apply (frule_tac p="n" and ys="b" in list_all2_nthD)
       apply (clarsimp dest!: list_all2_lengthD)
      by (clarsimp dest!: list_all2_lengthD)
  qed
qed

lemma locs_rev_stks:
  "x \<ge> z \<Longrightarrow>
  locs z
    (\<lambda>b.
      if z < b then loc (Suc y, b)
        else if b \<le> z
          then stk (y, x + b - Suc z)
          else arbitrary)
  @ [stk (y, x - Suc 0)]
  =
  stk (y, x - Suc (z))
  # rev (take z (stks x (\<lambda>a. stk(y, a))))"
apply (rule nth_equalityI)
 apply (simp)
apply (auto simp: nth_append nth_Cons' (* nth_locs *) less_Suc_eq min.absorb2 max.absorb2)
done

lemma locs_invoke_purge:
  "(z::nat) > c \<Longrightarrow>
  locs l
    (\<lambda>b. if z = c \<longrightarrow> Q b then loc (c, b) else u b) =
  locs l (\<lambda>a. loc (c, a))"
  by (induct l, auto)


lemma nth_rev_equalityI:
  "\<lbrakk>length xs = length ys; \<forall>i<length xs. xs ! (length xs - Suc i) = ys ! (length ys - Suc i)\<rbrakk>
  \<Longrightarrow> xs = ys"
proof (induct xs ys rule: list_induct2)
  case Nil
  thus ?case by simp
next
  case (Cons x xs y ys)
  hence "\<forall>i<length ys. xs ! (length ys - Suc i) = ys ! (length ys - Suc i)"
    apply auto
    apply (erule_tac x="i" in allE)
    by (auto simp: nth_Cons')
  with Cons show ?case
    by (auto simp: nth_Cons)
qed

lemma length_locss:
  "i < length cs
  \<Longrightarrow> length (locss P cs loc ! (length cs - Suc i)) =
  locLength P (fst(cs ! (length cs - Suc i)))
              (fst(snd(cs ! (length cs - Suc i))))
              (snd(snd(cs ! (length cs - Suc i))))"
apply (induct cs, auto)
apply (case_tac "i = length cs")
 by (auto simp: nth_Cons')

lemma locss_invoke_purge:
  "z > length cs \<Longrightarrow>
  locss P cs
    (\<lambda>(a, b). if (a = z \<longrightarrow> Q b)
      then loc (a, b)
      else u b)
  = locss P cs loc"
  by (induct cs, auto simp: locs_invoke_purge [simplified])

lemma stks_purge':
  "d \<ge> b \<Longrightarrow> stks b (\<lambda>x. if x = d then e else stk x) = stks b stk"
  by simp

subsection \<open>Byte code verifier conformance\<close>

text \<open>Here we prove state conformance invariant under \<open>transfer\<close> for
our CFG. Therefore, we must assume, that the predicate of a potential preceding
predicate-edge holds for every update-edge.
\<close>
 
theorem bv_invariant:
  "\<lbrakk> valid_edge (P,C0,Main) a;
  sourcenode a = (_ (C,M,pc)#cs,x _);
  targetnode a = (_ (C',M',pc')#cs',x' _);
  pred (kind a) s;
  x \<noteq> None \<longrightarrow> (\<exists>a_pred. 
    sourcenode a_pred = (_ (C,M,pc)#cs,None _) \<and>
    targetnode a_pred = sourcenode a \<and>
    valid_edge (P,C0,Main) a_pred \<and>
    pred (kind a_pred) s
  );
  P,((C,M,pc)#cs) \<turnstile>\<^bsub>BV\<^esub> s \<surd> \<rbrakk>
  \<Longrightarrow> P,((C',M',pc')#cs') \<turnstile>\<^bsub>BV\<^esub> transfer (kind a) s \<surd>"
proof -
  assume ve: "valid_edge (P, C0, Main) a"
    and src [simp]: "sourcenode a = (_ (C,M,pc)#cs,x _)"
    and trg [simp]: "targetnode a = (_ (C',M',pc')#cs',x' _)"
    and pred_s: "pred (kind a) s"
    and a_pred: "x \<noteq> None \<longrightarrow> (\<exists>a_pred. 
      sourcenode a_pred = (_ (C,M,pc)#cs,None _) \<and>
      targetnode a_pred = sourcenode a \<and>
      valid_edge (P,C0,Main) a_pred \<and>
      pred (kind a_pred) s
    )"
    and state_correct: "P,((C,M,pc)#cs) \<turnstile>\<^bsub>BV\<^esub> s \<surd>"
  obtain h stk loc where s [simp]: "s = (h,stk,loc)" by (cases s, fastforce)
  note P_wf = wf_jvmprog_is_wf [of P]
  from ve obtain Ts T mxs mxl "is" xt
    where sees_M: "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl,is,xt) in C"
    and "pc < length is"
    and reachable: "P\<^bsub>\<Phi>\<^esub> C M ! pc \<noteq> None"
    by (cases x) (cases cs, auto)+
  from P_wf sees_M
  have wt_method: "wt_method (P\<^bsub>wf\<^esub>) C Ts T mxs mxl is xt (P\<^bsub>\<Phi>\<^esub> C M)"
    by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
  with sees_M \<open>pc < length is\<close> reachable
  have applicable: "app\<^sub>i ((is ! pc),(P\<^bsub>wf\<^esub>),pc,mxs,T,(the(P\<^bsub>\<Phi>\<^esub> C M ! pc)))"
    by (auto simp: wt_method_def)
  from state_correct ve P_wf
  have trg_state_correct:
    "(P\<^bsub>wf\<^esub>),(P\<^bsub>\<Phi>\<^esub>) \<turnstile> the (JVMExec.exec ((P\<^bsub>wf\<^esub>), state_to_jvm_state P ((C,M,pc)#cs) s)) \<surd>"
    apply simp
    apply (drule BV_correct_1)
      apply (fastforce simp: bv_conform_def)
     apply (simp add: exec_1_iff)
    apply (cases "instrs_of (P\<^bsub>wf\<^esub>) C M ! pc")
    apply (simp_all add: split_beta)
    done
  from reachable obtain ST LT where reachable: "(P\<^bsub>\<Phi>\<^esub>) C M ! pc = \<lfloor>(ST, LT)\<rfloor>"
    by fastforce
  with wt_method sees_M \<open>pc < length is\<close>
  have stk_loc_succs:
    "\<forall>pc' \<in> set (succs (is ! pc) (ST, LT) pc).
    stkLength P C M pc' = length (fst (eff\<^sub>i (is ! pc, (P\<^bsub>wf\<^esub>), ST, LT))) \<and>
    locLength P C M pc' = length (snd (eff\<^sub>i (is ! pc, (P\<^bsub>wf\<^esub>), ST, LT)))"
    unfolding wt_method_def apply (cases "is ! pc")
    using [[simproc del: list_to_set_comprehension]]
    apply (cases "is ! pc")
    apply (tactic \<open>PARALLEL_ALLGOALS
      (Clasimp.fast_force_tac (@{context} addSDs @{thms list_all2_lengthD}))\<close>)
    done
  have [simp]: "\<exists>x. x" by auto
  have [simp]: "Ex Not" by auto
  show ?thesis
  proof (cases "instrs_of (P\<^bsub>wf\<^esub>) C M ! pc")
    case (Invoke m n)
    from state_correct have "preallocated h"
      by (clarsimp simp: bv_conform_def correct_state_def hconf_def)
    from Invoke applicable sees_M have "stkLength P C M pc > n"
      by (cases "the (P\<^bsub>\<Phi>\<^esub> C M ! pc)") auto
    show ?thesis
    proof (cases x)
      case [simp]: None
      with ve Invoke obtain Q where kind: "kind a = (Q)\<^sub>\<surd>"
        by (auto elim!: JVM_CFG.cases)
      with ve Invoke have "(C',M',pc')#cs' = (C,M,pc)#cs"
        by (auto elim!: JVM_CFG.cases)
      with state_correct kind show ?thesis
        by simp
    next
      case [simp]: (Some aa)
      with ve Invoke obtain xf where [simp]: "aa = ((C',M',pc')#cs' , xf)"
        by (auto elim!: JVM_CFG.cases)
      from ve Invoke obtain f where kind: "kind a = \<Up>f"
        apply -
        apply clarsimp
        apply (erule JVM_CFG.cases)
        apply auto
        done
      show ?thesis
      proof (cases xf)
        case [simp]: True
        with a_pred Invoke have stk_n: "stk (length cs, stkLength P C M pc - Suc n) = Null"
          apply auto
          apply (erule JVM_CFG.cases)
          apply simp_all
          done
        from ve Invoke kind
        have [simp]: "f = (\<lambda>(h,stk,loc).
          (h, 
           stk((length cs',(stkLength P C' M' pc') - 1) := Addr (addr_of_sys_xcpt NullPointer)),
          loc))"
          apply -
          apply clarsimp
          apply (erule JVM_CFG.cases)
          apply auto
          done
        from ve Invoke
        have "find_handler_for P NullPointer ((C,M,pc)#cs) = (C',M',pc')#cs'"
          apply -
          apply clarsimp
          apply (erule JVM_CFG.cases)
          apply auto
          done
        with Invoke state_correct kind stk_n trg_state_correct applicable sees_M
          \<open>preallocated h\<close>
        show ?thesis
          apply (cases "the (P\<^bsub>\<Phi>\<^esub> C M ! pc)",
                 auto simp: bv_conform_def stkss_purge
                  simp del: find_handler_for.simps exec.simps app\<^sub>i.simps fun_upd_apply)
          apply (rule_tac cs="(C,M,pc)#cs" in find_handler_exec_correct)
            apply fastforce
           apply (fastforce simp: split_beta split: if_split_asm)
          apply fastforce
          done
      next
        case [simp]: False
        from a_pred Invoke
        have [simp]: "m = M'"
          by -(clarsimp, erule JVM_CFG.cases, auto)
        from a_pred Invoke
        have [simp]: "pc' = 0"
          by -(clarsimp, erule JVM_CFG.cases, auto)
        from ve Invoke
        have [simp]: "cs' = (C,M,pc)#cs"
          by -(clarsimp, erule JVM_CFG.cases, auto)
        from ve Invoke kind
        have [simp]:
          "f = (\<lambda>s. exec_instr (Invoke m n) P s (length cs) (stkLength P C M pc)
                               arbitrary (locLength P C' M' 0))"
          by -(clarsimp, erule JVM_CFG.cases, auto)
        from state_correct obtain ST LT where [simp]:
          "(P\<^bsub>\<Phi>\<^esub>) C M ! pc = \<lfloor>(ST,LT)\<rfloor>"
          by (auto simp: bv_conform_def correct_state_def)
        from a_pred Invoke
        have [simp]:
          "fst (method (P\<^bsub>wf\<^esub>)
          (cname_of h (the_Addr (stk (length cs, length ST - Suc n)))) M') = C'"
          by -(clarsimp, erule JVM_CFG.cases, auto)
        from a_pred Invoke
        have [simp]: "stk (length cs, length ST - Suc n) \<noteq> Null"
          by -(clarsimp, erule JVM_CFG.cases, auto)
        from state_correct applicable sees_M Invoke
        have [simp]: "ST ! n \<noteq> NT"
          apply (auto simp: correct_state_def bv_conform_def)
          apply (drule_tac p="n" and ys="ST" in list_all2_nthD)
           apply simp
          by clarsimp
        from applicable Invoke sees_M
        have "length ST > n"
          by auto
        with trg_state_correct Invoke
        have [simp]: "stkLength P C' M' 0 = 0"
          by (auto simp: split_beta correct_state_def
                  split: if_split_asm)
        from trg_state_correct Invoke \<open>length ST > n\<close>
        have "locLength P C' M' 0 =
          Suc n + fst(snd(snd(snd(snd(method (P\<^bsub>wf\<^esub>) 
                   (cname_of h (the_Addr (stk (length cs, length ST - Suc n)))) M')))))"
          by (auto simp: split_beta  (* nth_stks *) correct_state_def
                  dest!: list_all2_lengthD
                  split: if_split_asm)
        with Invoke state_correct trg_state_correct \<open>length ST > n\<close>
        have "JVMExec.exec  (P\<^bsub>wf\<^esub>, state_to_jvm_state P ((C, M, pc) # cs) s)
            =
            \<lfloor>(None, h,
                 (stks (stkLength P C' M' pc') (\<lambda>a. stk (Suc (length cs), a)),
                  locs (locLength P C' M' pc')
                   (\<lambda>a'. (\<lambda>(a, b).
                       if a = Suc (length cs) \<longrightarrow> locLength P C' M' 0 \<le> b then loc (a, b)
                       else if b \<le> n then stk (length cs, length ST - (Suc n - b))
                            else arbitrary) (Suc (length cs), a')),
                  C', M', pc') #
                 (stks (length ST) (\<lambda>a. stk (length cs, a)),
                  locs (length LT) (\<lambda>a. loc (length cs, a)), C, M, pc) #
                 zip (stkss P cs stk) (zip (locss P cs loc) cs))\<rfloor>"
          apply (auto simp: split_beta  (* nth_stks *) bv_conform_def)
           apply (rule nth_equalityI)
            apply simp
           apply (cases ST,
                  auto simp: nth_Cons' nth_append min.absorb1 min.absorb2)
          apply (rule nth_equalityI)
           apply simp
          by (auto simp: (* nth_locs *) (* nth_stks *) rev_nth nth_Cons' nth_append min_def)
        with Invoke state_correct kind trg_state_correct applicable sees_M
        show ?thesis
          apply (cases "the (P\<^bsub>\<Phi>\<^esub> C M ! pc)",
                 auto simp: bv_conform_def stkss_purge rev_nth (* nth_stks *)
                    simp del: find_handler_for.simps exec.simps app\<^sub>i.simps)
          apply(subst locss_invoke_purge, simp)
          by simp
      qed
    qed
  next
    case (Load nat)
    with stk_loc_succs sees_M reachable
    have "stkLength P C M (Suc pc) = Suc (stkLength P C M pc)"
      and "locLength P C M (Suc pc) = locLength P C M pc"
      by simp_all
    with state_correct ve P_wf applicable sees_M Load trg_state_correct
    show ?thesis
      apply auto
      apply (erule JVM_CFG.cases, simp_all)
      by (auto simp: bv_conform_def stkss_purge stks_purge')
  next
    case (Store nat)
    with stk_loc_succs sees_M reachable applicable
    have "stkLength P C M (Suc pc) = stkLength P C M pc - 1"
      and "locLength P C M (Suc pc) = locLength P C M pc"
      by auto
    with state_correct ve P_wf applicable sees_M Store trg_state_correct
    show ?thesis
      apply auto
      apply (erule JVM_CFG.cases, simp_all)
      by (auto simp: bv_conform_def locss_purge)
  next
    case (Push val)
    with stk_loc_succs sees_M reachable applicable
    have "stkLength P C M (Suc pc) = Suc (stkLength P C M pc)"
      and "locLength P C M (Suc pc) = locLength P C M pc"
      by auto
    with state_correct ve P_wf applicable sees_M Push trg_state_correct
    show ?thesis
      apply auto
      apply (erule JVM_CFG.cases, simp_all)
      by (auto simp: bv_conform_def stks_purge' stkss_purge)
  next
    case Pop
    with stk_loc_succs sees_M reachable applicable
    have "stkLength P C M (Suc pc) = stkLength P C M pc - 1"
      and "locLength P C M (Suc pc) = locLength P C M pc"
      by auto
    with state_correct ve P_wf applicable sees_M Pop trg_state_correct
    show ?thesis
      apply auto
      apply (erule JVM_CFG.cases, simp_all)
      by (auto simp: bv_conform_def)
  next
    case IAdd
    with stk_loc_succs sees_M reachable applicable
    have "stkLength P C M (Suc pc) = stkLength P C M pc - 1"
      and "locLength P C M (Suc pc) = locLength P C M pc"
      by auto
    with state_correct ve P_wf applicable sees_M IAdd trg_state_correct
    show ?thesis
      apply auto
      apply (erule JVM_CFG.cases, simp_all)
      by (auto simp: bv_conform_def stks_purge' stkss_purge add.commute)
  next
    case CmpEq
    with stk_loc_succs sees_M reachable applicable
    have "stkLength P C M (Suc pc) = stkLength P C M pc - 1"
      and "locLength P C M (Suc pc) = locLength P C M pc"
      by auto
    with state_correct ve P_wf applicable sees_M CmpEq trg_state_correct
    show ?thesis
      apply auto
       apply (erule JVM_CFG.cases, simp_all)
       apply (auto simp: bv_conform_def stks_purge' stkss_purge bool_sym)
      apply (erule JVM_CFG.cases, simp_all)
      by (auto simp: bv_conform_def stks_purge' stkss_purge bool_sym)
  next
    case (Goto b)
    with stk_loc_succs sees_M reachable applicable
    have "stkLength P C M (nat (int pc + b)) = stkLength P C M pc"
      and "locLength P C M (nat (int pc + b)) = locLength P C M pc"
      by auto
    with state_correct ve P_wf applicable sees_M Goto trg_state_correct
    show ?thesis
      apply auto
      by (erule JVM_CFG.cases, simp_all add: bv_conform_def)
  next
    case (IfFalse b)
    have nat_int_pc_conv: "nat (int pc + 1) = pc + 1"
      by (cases pc) auto
    from IfFalse stk_loc_succs sees_M reachable applicable
    have "stkLength P C M (Suc pc) = stkLength P C M pc - 1"
      and "stkLength P C M (nat (int pc + b)) = stkLength P C M pc - 1"
      and "locLength P C M (Suc pc) = locLength P C M pc"
      and "locLength P C M (nat (int pc + b)) = locLength P C M pc"
      by auto
    with state_correct ve P_wf applicable sees_M IfFalse pred_s nat_int_pc_conv
      trg_state_correct
    show ?thesis
      apply auto
      apply (erule JVM_CFG.cases, simp_all)
       by (auto simp: bv_conform_def split: if_split_asm)
  next
    case Return
    with ve obtain Ts' T' mxs' mxl' is' xt'
      where sees_M': "(P\<^bsub>wf\<^esub>) \<turnstile> C' sees M':Ts'\<rightarrow>T' = (mxs',mxl',is',xt') in C'"
      and "(pc' - 1) < length is'"
      and reachable': "P\<^bsub>\<Phi>\<^esub> C' M' ! (pc' - 1) \<noteq> None"
      apply auto
      apply (erule JVM_CFG.cases, auto)
      by (cases cs', auto)
    with Return ve wt_method sees_M applicable
    have "is' ! (pc' - 1) = Invoke M (length Ts)"
      apply auto
      apply (erule JVM_CFG.cases, auto)
      apply (drule sees_method_fun, fastforce, clarsimp)
      by (auto dest!: list_all2_lengthD simp: wt_method_def wt_start_def)
    from P_wf sees_M'
    have "wt_method (P\<^bsub>wf\<^esub>) C' Ts' T' mxs' mxl' is' xt' (P\<^bsub>\<Phi>\<^esub> C' M')"
      by (auto dest: sees_wf_mdecl simp: wf_jvm_prog_phi_def wf_mdecl_def)
    with ve Return \<open>pc' - 1 < length is'\<close> reachable' sees_M state_correct
    have "stkLength P C' M' pc' = stkLength P C' M' (pc' - 1) - length Ts"
      using [[simproc del: list_to_set_comprehension]]
      apply auto
      apply (erule JVM_CFG.cases, auto)
      apply (drule sees_method_fun, fastforce, clarsimp)
      using sees_M'
      apply hypsubst_thin
      apply (auto simp: wt_method_def)
      apply (erule_tac x="pc'" in allE)
      apply (auto simp: bv_conform_def correct_state_def not_less_eq less_Suc_eq)
       apply (drule sees_method_fun, fastforce, clarsimp)
       apply (drule sees_method_fun, fastforce, clarsimp)
      apply (auto simp: wt_start_def)
      apply (auto dest!: list_all2_lengthD)
      apply (drule sees_method_fun, fastforce, clarsimp)
      apply (drule sees_method_fun, fastforce, clarsimp)
      by auto
    from \<open>wt_method (P\<^bsub>wf\<^esub>) C' Ts' T' mxs' mxl' is' xt' (P\<^bsub>\<Phi>\<^esub> C' M')\<close>
      \<open>(pc' - 1) < length is'\<close> \<open>P\<^bsub>\<Phi>\<^esub> C' M' ! (pc' - 1) \<noteq> None\<close>
      \<open>is' ! (pc' - 1) = Invoke M (length Ts)\<close>
    have "stkLength P C' M' (pc' - 1) > 0"
      by (fastforce simp: wt_method_def)
    then obtain ST' STr' where [simp]: "fst (the (P\<^bsub>\<Phi>\<^esub> C' M' ! (pc' - 1))) = ST'#STr'"
      by (cases "fst (the (P\<^bsub>\<Phi>\<^esub> C' M' ! (pc' - 1)))", fastforce+)
    from wt_method
    have "locLength P C M 0 = Suc (length Ts) + mxl"
      by (auto dest!: list_all2_lengthD
                simp: wt_method_def wt_start_def)
    from \<open>wt_method (P\<^bsub>wf\<^esub>) C' Ts' T' mxs' mxl' is' xt' (P\<^bsub>\<Phi>\<^esub> C' M')\<close>
      ve Return \<open>pc' - 1 < length is'\<close> reachable' sees_M state_correct
    have "locLength P C' M' (pc' - 1) = locLength P C' M' pc'"
      using [[simproc del: list_to_set_comprehension]]
      apply auto
      apply (erule JVM_CFG.cases, auto)
      apply (drule sees_method_fun, fastforce, clarsimp)
      using sees_M'
      apply hypsubst_thin
      apply (auto simp: wt_method_def)
      apply (erule_tac x="pc'" in allE)
      apply (auto simp: wt_start_def)
       apply (clarsimp simp: bv_conform_def correct_state_def)
       apply (drule sees_method_fun, fastforce, clarsimp)
       apply (drule sees_method_fun, fastforce, clarsimp)
      by (auto dest!: list_all2_lengthD)
    with \<open>stkLength P C' M' pc' = stkLength P C' M' (pc' - 1) - length Ts\<close>
      Return state_correct ve P_wf applicable sees_M trg_state_correct sees_M'
      \<open>fst (the (P\<^bsub>\<Phi>\<^esub> C' M' ! (pc' - 1))) = ST'#STr'\<close> \<open>is' ! (pc' - 1) = Invoke M (length Ts)\<close>
      \<open>locLength P C M 0 = Suc (length Ts) + mxl\<close>
    show ?thesis
      apply (auto simp: bv_conform_def)
      apply (erule JVM_CFG.cases, auto simp: stkss_purge locss_purge)
      apply (drule sees_method_fun, fastforce, clarsimp)
      apply (auto simp: correct_state_def)
      apply (drule sees_method_fun, fastforce, clarsimp)
      apply (drule sees_method_fun, fastforce, clarsimp)
      apply (drule sees_method_fun, fastforce, clarsimp)
      apply (rule_tac x="Ts'" in exI)
      apply (rule_tac x="T'" in exI)
      apply (rule_tac x="mxs'" in exI)
      apply (rule_tac x="mxl'" in exI)
      apply (rule_tac x="is'" in exI)
      apply clarsimp
      apply (rule conjI)
       apply (rule_tac x="xt'" in exI)
       apply clarsimp
      apply (rule list_all2_all_nthI)
       apply clarsimp
      apply clarsimp
      apply (auto simp: rev_nth (* nth_stks *) list_all2_Cons1)
       apply (case_tac n, auto simp: list_all2_Cons1)
      apply (case_tac n, auto simp: list_all2_Cons1)
      apply (drule_tac p="nat" and ys="zs" in list_all2_nthD2)
       apply clarsimp
      by auto
  next
    case (New Cl)
    from state_correct have "preallocated h"
      by (clarsimp simp: bv_conform_def correct_state_def hconf_def)
    from New stk_loc_succs sees_M reachable applicable
    have "stkLength P C M (Suc pc) = Suc (stkLength P C M pc)"
      and "locLength P C M (Suc pc) = locLength P C M pc"
      by auto
    with New state_correct ve sees_M trg_state_correct applicable a_pred \<open>preallocated h\<close>
    show ?thesis
      apply (clarsimp simp del: exec.simps)
      apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       defer
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       apply (simp add: bv_conform_def stkss_purge del: exec.simps find_handler_for.simps)
       apply (rule_tac cs="(C,M,pc)#cs" in find_handler_exec_correct [simplified])
         apply fastforce
        apply fastforce
       apply clarsimp
      by (auto simp: split_beta bv_conform_def stks_purge' stkss_purge
           simp del: find_handler_for.simps)
  next
    case (Getfield Fd Cl)
    from state_correct have "preallocated h"
      by (clarsimp simp: bv_conform_def correct_state_def hconf_def)
    from Getfield stk_loc_succs sees_M reachable applicable
    have "stkLength P C M (Suc pc) = stkLength P C M pc"
      and "locLength P C M (Suc pc) = locLength P C M pc"
      by auto
    with Getfield state_correct ve sees_M trg_state_correct applicable a_pred \<open>preallocated h\<close>
    show ?thesis
      apply (clarsimp simp del: exec.simps)
      apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       defer
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       apply (simp add: bv_conform_def stkss_purge del: exec.simps find_handler_for.simps)
       apply (rule_tac cs="(C,M,pc)#cs" in find_handler_exec_correct [simplified])
         apply fastforce
        apply (fastforce simp: split_beta)
       apply clarsimp
      by (auto simp: split_beta bv_conform_def stks_purge' stkss_purge
           simp del: find_handler_for.simps)
  next
    case (Putfield Fd Cl)
    from state_correct have "preallocated h"
      by (clarsimp simp: bv_conform_def correct_state_def hconf_def)
    from Putfield stk_loc_succs sees_M reachable applicable
    have "stkLength P C M (Suc pc) = stkLength P C M pc - 2"
      and "locLength P C M (Suc pc) = locLength P C M pc"
      by auto
    with Putfield state_correct ve sees_M trg_state_correct applicable a_pred \<open>preallocated h\<close>
    show ?thesis
      apply (clarsimp simp del: exec.simps)
      apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       defer
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       apply (simp add: bv_conform_def stkss_purge del: exec.simps find_handler_for.simps)
       apply (rule_tac cs="(C,M,pc)#cs" in find_handler_exec_correct [simplified])
         apply fastforce
        apply (fastforce simp: split_beta)
       apply clarsimp
      by (auto simp: split_beta bv_conform_def stks_purge' stkss_purge
           simp del: find_handler_for.simps)
  next
    case (Checkcast Cl)
    from state_correct have "preallocated h"
      by (clarsimp simp: bv_conform_def correct_state_def hconf_def)
    from Checkcast stk_loc_succs sees_M reachable applicable
    have "stkLength P C M (Suc pc) = stkLength P C M pc"
      and "locLength P C M (Suc pc) = locLength P C M pc"
      by auto
    with Checkcast state_correct ve sees_M
      trg_state_correct applicable a_pred pred_s \<open>preallocated h\<close>
    show ?thesis
      apply (clarsimp simp del: exec.simps)
      apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       defer
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
       apply (clarsimp simp del: exec.simps find_handler_for.simps)
       apply (simp add: bv_conform_def stkss_purge del: exec.simps find_handler_for.simps)
       apply (rule_tac cs="(C,M,pc)#cs" in find_handler_exec_correct [simplified])
         apply fastforce
        apply (fastforce simp: split_beta)
       apply clarsimp
      by (auto simp: split_beta bv_conform_def
           simp del: find_handler_for.simps)
  next
    case Throw
    from state_correct have "preallocated h"
      by (clarsimp simp: bv_conform_def correct_state_def hconf_def)
    from Throw applicable state_correct sees_M obtain a
      where "stk(length cs, stkLength P C M pc - 1) = Null \<or>
             stk(length cs, stkLength P C M pc - 1) = Addr a"
      by (cases "stk(length cs, stkLength P C M pc - 1)",
          auto simp: is_refT_def bv_conform_def correct_state_def conf_def)
    with Throw state_correct ve trg_state_correct a_pred applicable sees_M \<open>preallocated h\<close>
    show ?thesis
      apply (clarsimp simp del: exec.simps)
      apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
      apply (clarsimp simp del: exec.simps find_handler_for.simps)
      apply (erule JVM_CFG.cases, simp_all del: exec.simps find_handler_for.simps)
      apply (clarsimp simp: bv_conform_def simp del: exec.simps find_handler_for.simps)
      apply (rule conjI)
       apply (clarsimp simp: stkss_purge simp del: exec.simps find_handler_for.simps)
       apply (rule_tac cs="(C,M,pc)#cs" in find_handler_exec_correct [simplified])
         apply fastforce
        apply (simp add: hd_stks)
       apply simp
      apply (clarsimp simp: stkss_purge simp del: exec.simps find_handler_for.simps)
      apply (simp del: find_handler_for.simps exec.simps cong: if_cong)
      apply (rule_tac cs="(C,M,pc)#cs" in find_handler_exec_correct [simplified])
        apply fastforce
       apply (simp add: hd_stks)
      by simp
  qed
qed


section \<open>CFG simulates Jinja's semantics\<close>

subsection \<open>Definitions\<close>

text \<open>
The following predicate defines the semantics of Jinja lifted to our
state representation. Thereby, we require the state to be byte code verifier
conform; otherwise the step in the semantics is undefined.

The predicate \<open>valid_callstack\<close> is actually an implication of the
byte code verifier conformance. But we list it explicitly for convenience.
\<close>

inductive sem :: "jvmprog \<Rightarrow> callstack \<Rightarrow> state \<Rightarrow> callstack \<Rightarrow> state \<Rightarrow> bool"
("_ \<turnstile> \<langle>_,_\<rangle> \<Rightarrow> \<langle>_,_\<rangle>")
  where Step:
  "\<lbrakk> prog = (P,C0,Main);
  P,cs \<turnstile>\<^bsub>BV\<^esub> s \<surd>;
  valid_callstack prog cs;
  JVMExec.exec ((P\<^bsub>wf\<^esub>), state_to_jvm_state P cs s) = \<lfloor>(None,h',frs')\<rfloor>;
  cs' = framestack_to_callstack frs';
  s = (h, stk, loc);
  s' = (h', update_stk stk frs', update_loc loc frs') \<rbrakk>
  \<Longrightarrow> prog \<turnstile> \<langle>cs,s\<rangle> \<Rightarrow> \<langle>cs',s'\<rangle>"

abbreviation identifies :: "j_node \<Rightarrow> callstack \<Rightarrow> bool"
where "identifies n cs \<equiv> (n = (_ cs,None _))"

subsection \<open>Some more simplification lemmas\<close>

lemma valid_callstack_tl:
  "valid_callstack prog ((C,M,pc)#cs) \<Longrightarrow> valid_callstack prog cs"
  by (cases prog, cases cs, auto)

lemma stkss_cong [cong]:
  "\<lbrakk> P = P';
  cs = cs';
  \<And>a b. \<lbrakk> a < length cs;
     b < stkLength P (fst(cs ! (length cs - Suc a)))
                     (fst(snd(cs ! (length cs - Suc a))))
                     (snd(snd(cs ! (length cs - Suc a)))) \<rbrakk>
    \<Longrightarrow> stk (a, b) = stk' (a, b) \<rbrakk>
  \<Longrightarrow> stkss P cs stk = stkss P' cs' stk'"
  by (auto, hypsubst_thin, induct cs',
    auto intro!: nth_equalityI simp: nth_Cons' (* nth_stks *))

lemma locss_cong [cong]:
  "\<lbrakk> P = P';
  cs = cs';
  \<And>a b. \<lbrakk> a < length cs;
     b < locLength P (fst(cs ! (length cs - Suc a)))
                     (fst(snd(cs ! (length cs - Suc a))))
                     (snd(snd(cs ! (length cs - Suc a)))) \<rbrakk>
    \<Longrightarrow> loc (a, b) = loc' (a, b) \<rbrakk>
  \<Longrightarrow> locss P cs loc = locss P' cs' loc'"
  by (auto, hypsubst_thin, induct cs',
    auto intro!: nth_equalityI simp: nth_Cons' (* nth_locs *))

lemma hd_tl_equalityI:
  "\<lbrakk> length xs = length ys; hd xs = hd ys; tl xs = tl ys \<rbrakk> \<Longrightarrow> xs = ys"
apply (induct xs arbitrary: ys)
 apply simp
by (case_tac ys, auto)

lemma stkLength_is_length_stk:
  "P\<^bsub>wf\<^esub>,P\<^bsub>\<Phi>\<^esub> \<turnstile> (None, h, (stk, loc, C, M, pc) # frs') \<surd> \<Longrightarrow> stkLength P C M pc = length stk"
  by (auto dest!: list_all2_lengthD simp: correct_state_def)

lemma locLength_is_length_loc:
  "P\<^bsub>wf\<^esub>,P\<^bsub>\<Phi>\<^esub> \<turnstile> (None, h, (stk, loc, C, M, pc) # frs') \<surd> \<Longrightarrow> locLength P C M pc = length loc"
  by (auto dest!: list_all2_lengthD simp: correct_state_def)

lemma correct_state_frs_tlD:
  "(P\<^bsub>wf\<^esub>),(P\<^bsub>\<Phi>\<^esub>) \<turnstile> (None, h, a # frs') \<surd> \<Longrightarrow> (P\<^bsub>wf\<^esub>),(P\<^bsub>\<Phi>\<^esub>) \<turnstile> (None, h, frs') \<surd>"
  by (cases frs', (fastforce simp: correct_state_def)+)

lemma update_stk_Cons [simp]:
  "stkss P (framestack_to_callstack frs') (update_stk stk ((stk', loc', C', M', pc') # frs')) =
  stkss P (framestack_to_callstack frs') (update_stk stk frs')"
apply (induct frs' arbitrary: stk' loc' C' M' pc')
 apply clarsimp
 apply (simp only: f2c_Nil)
 apply clarsimp
apply clarsimp
apply (simp only: f2c_Cons)
apply clarsimp
apply (rule stkss_cong)
  by (fastforce simp: nth_Cons')+

lemma update_loc_Cons [simp]:
  "locss P (framestack_to_callstack frs') (update_loc loc ((stk', loc', C', M', pc') # frs')) =
  locss P (framestack_to_callstack frs') (update_loc loc frs')"
apply (induct frs' arbitrary: stk' loc' C' M' pc')
 apply clarsimp
 apply (simp only: f2c_Nil)
 apply clarsimp
apply clarsimp
apply (simp only: f2c_Cons)
apply clarsimp
apply (rule locss_cong)
  by (fastforce simp: nth_Cons')+

lemma s2j_id:
  "(P\<^bsub>wf\<^esub>),(P\<^bsub>\<Phi>\<^esub>) \<turnstile> (None,h',frs') \<surd>
  \<Longrightarrow> state_to_jvm_state P (framestack_to_callstack frs')
       (h, update_stk stk frs', update_loc loc frs') = (None, h, frs')"
apply (induct frs')
 apply simp
apply simp
apply (rule hd_tl_equalityI)
  apply simp
 apply simp
 apply clarsimp
 apply (simp only: f2c_Cons fst_conv snd_conv)
 apply clarsimp
 apply (rule conjI)
  apply (rule nth_equalityI)
   apply (simp add: stkLength_is_length_stk)
  apply (clarsimp simp: (* nth_stks *) stkLength_is_length_stk)
  apply (case_tac a, simp_all)
 apply (rule nth_equalityI)
  apply (simp add: locLength_is_length_loc)
 apply (clarsimp simp: (* nth_locs *) locLength_is_length_loc)
apply (drule correct_state_frs_tlD)
apply simp
apply clarsimp
apply (simp only: f2c_Cons fst_conv snd_conv)
by clarsimp

lemma find_handler_last_cs_eqD:
  "\<lbrakk> find_handler P\<^bsub>wf\<^esub> a h frs = (None, h', frs');
  last frs = (stk,loc,C,M,pc);
  last frs' = (stk',loc',C',M',pc') \<rbrakk>
  \<Longrightarrow> C = C' \<and> M = M'"
  by (induct frs, auto split: if_split_asm)


lemma exec_last_frs_eq_class:
  "\<lbrakk> JVMExec.exec (P\<^bsub>wf\<^esub>, None, h, frs) = \<lfloor>(None, h', frs')\<rfloor>;
  last frs = (stk, loc, C, M, pc);
  last frs' = (stk', loc', C', M', pc');
  frs \<noteq> [];
  frs' \<noteq> [] \<rbrakk>
  \<Longrightarrow> C = C'"
apply (cases frs, auto split: if_split_asm)
 apply (cases "instrs_of P\<^bsub>wf\<^esub> C M ! pc", auto simp: split_beta)
 apply (case_tac "instrs_of P\<^bsub>wf\<^esub> ab ac ! b", auto simp: split_beta)
 apply (case_tac list, auto)
 apply (case_tac lista, auto)
apply (drule find_handler_last_cs_eqD)
  apply fastforce
 apply fastforce
by simp

lemma exec_last_frs_eq_method:
  "\<lbrakk> JVMExec.exec (P\<^bsub>wf\<^esub>, None, h, frs) = \<lfloor>(None, h', frs')\<rfloor>;
  last frs = (stk, loc, C, M, pc);
  last frs' = (stk', loc', C', M', pc');
  frs \<noteq> [];
  frs' \<noteq> [] \<rbrakk>
  \<Longrightarrow> M = M'"
apply (cases frs, auto split: if_split_asm)
 apply (cases "instrs_of P\<^bsub>wf\<^esub> C M ! pc", auto simp: split_beta)
 apply (case_tac "instrs_of P\<^bsub>wf\<^esub> ab ac ! b", auto simp: split_beta)
 apply (case_tac list, auto)
 apply (case_tac lista, auto)
apply (drule find_handler_last_cs_eqD)
  apply fastforce
 apply fastforce
by simp

lemma valid_callstack_append_last_class:
  "valid_callstack (P,C0,Main) (cs@[(C,M,pc)]) \<Longrightarrow> C = C0"
  by (induct cs, auto dest: valid_callstack_tl)

lemma valid_callstack_append_last_method:
  "valid_callstack (P,C0,Main) (cs@[(C,M,pc)]) \<Longrightarrow> M = Main"
  by (induct cs, auto dest: valid_callstack_tl)
 
lemma zip_stkss_locss_append_single [simp]:
  "zip (stkss P (cs @ [(C, M, pc)]) stk)
    (zip (locss P (cs @ [(C, M, pc)]) loc) (cs @ [(C, M, pc)]))
  = (zip (stkss P (cs @ [(C, M, pc)]) stk) (zip (locss P (cs @ [(C, M, pc)]) loc) cs))
  @ [(stks (stkLength P C M pc) (\<lambda>a. stk (0, a)),
      locs (locLength P C M pc) (\<lambda>a. loc (0, a)), C, M, pc)]"
  by (induct cs, auto)

subsection \<open>Interpretation of the \<open>CFG_semantics_wf\<close> locale\<close>

interpretation JVM_semantics_CFG_wf:
  CFG_semantics_wf "sourcenode" "targetnode" "kind" "valid_edge prog" "(_Entry_)"
   "sem prog" "identifies"
  for prog
proof(unfold_locales)
  fix n c s c' s'
  assume sem_step:"prog \<turnstile> \<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>"
    and "identifies n c"
  obtain P C0 M0
    where prog [simp]:"prog = (P,C0,M0)"
    by (cases prog,fastforce)
  obtain h stk loc
    where s [simp]: "s = (h,stk,loc)"
    by (cases s, fastforce)
  obtain h' stk' loc'
    where s' [simp]: "s' = (h',stk',loc')"
    by (cases s', fastforce)
  from sem_step s s' prog obtain C M pc cs C' M' pc' cs'
    where c [simp]: "c = (C,M,pc)#cs"
    by (cases c, auto elim: sem.cases simp: bv_conform_def)
  with sem_step prog obtain ST LT
    where wt [simp]: " (P\<^bsub>\<Phi>\<^esub>) C M ! pc = \<lfloor>(ST,LT)\<rfloor>"
    by (auto elim!: sem.cases, cases cs, fastforce+)
  note P_wf = wf_jvmprog_is_wf [of P]
  from sem_step prog obtain frs'
    where jvm_exec: "JVMExec.exec ((P\<^bsub>wf\<^esub>), state_to_jvm_state P c s) = \<lfloor>(None,h',frs')\<rfloor>"
    by (auto elim!: sem.cases)
  with sem_step prog s s'
  have loc': "loc' = update_loc loc frs'"
    and stk': "stk' = update_stk stk frs'"
    by (auto elim!: sem.cases)
  from sem_step s prog
  have state_wf: "P,c \<turnstile>\<^bsub>BV\<^esub> (h,stk,loc) \<surd>"
    by (auto elim!: sem.cases)
  hence state_correct: "(P\<^bsub>wf\<^esub>),(P\<^bsub>\<Phi>\<^esub>) \<turnstile> state_to_jvm_state P c (h,stk,loc) \<surd>"
    by (simp add: bv_conform_def)
  with P_wf jvm_exec s 
  have trg_state_correct: "(P\<^bsub>wf\<^esub>),(P\<^bsub>\<Phi>\<^esub>) \<turnstile> (None,h',frs') \<surd>"
    by -(rule BV_correct_1, (fastforce simp: exec_1_iff)+)
  from sem_step c s prog have prealloc: "preallocated h"
    by (auto elim: sem.cases
             simp: bv_conform_def correct_state_def hconf_def)
  from state_correct obtain Ts T mxs mxl "is" xt
    where sees_M: "(P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T = (mxs,mxl,is,xt) in C"
    by (clarsimp simp: bv_conform_def correct_state_def)
  with state_correct
  have "pc < length is"
    by (auto dest: sees_method_fun
             simp: bv_conform_def correct_state_def)
  with P_wf sees_M have
    applicable: "app\<^sub>i(is ! pc, (P\<^bsub>wf\<^esub>), pc, mxs, T, ST, LT)"
    by (fastforce dest!: sees_wf_mdecl
                  simp: wf_jvm_prog_phi_def wf_mdecl_def wt_method_def)
  from sem_step
  have v_cs: "valid_callstack prog c"
    by (auto elim: sem.cases)
  then obtain pcL where last_c: "last c = (C0,M0,pcL)"
    apply clarsimp
    apply (induct cs arbitrary: C M pc, simp)
    by fastforce
  from sees_M P_wf \<open>pc < length is\<close>
  have wt_instrs: "P\<^bsub>wf\<^esub>,T,mxs,length is,xt \<turnstile> is ! pc,pc :: (P\<^bsub>\<Phi>\<^esub>) C M"
    by -(drule wt_jvm_prog_impl_wt_instr, fastforce+)
  with applicable
  have effect: "\<forall>succ \<in> set (succs (is ! pc) (ST,LT) pc).
    (P\<^bsub>wf\<^esub>) \<turnstile> \<lfloor>eff\<^sub>i(is ! pc, (P\<^bsub>wf\<^esub>), ST, LT)\<rfloor> \<le>' (P\<^bsub>\<Phi>\<^esub>) C M ! succ \<and> succ < length is"
    apply clarsimp
    apply (erule_tac x="(succ, \<lfloor>eff\<^sub>i(is ! pc, (P\<^bsub>wf\<^esub>), ST, LT)\<rfloor> )" in ballE)
     by (erule_tac x="(succ, \<lfloor>eff\<^sub>i(is ! pc, (P\<^bsub>wf\<^esub>), ST, LT)\<rfloor> )" in ballE, clarsimp+)
   with P_wf sees_M last_c v_cs
   have v_cs_succ:
     "\<forall>succ \<in> set (succs (is ! pc) (ST,LT) pc). valid_callstack (P,C0,M0) ((C,M,succ)#cs)"
     by -(rule ballI,
       erule_tac x="succ" in ballE,
       auto,
       induct cs,
       fastforce+)
   from trg_state_correct v_cs jvm_exec
   have v_cs_f2c_frs':
     "valid_callstack (P,C0,M0) (framestack_to_callstack frs')"
     apply (cases frs' rule: rev_cases, simp)
     apply (rule_tac s="(h', update_stk stk frs', update_loc loc frs')"
       in correct_state_imp_valid_callstack)
       apply (simp only: bv_conform_def s2j_id)
      apply (auto dest!: f2c_emptyD simp del: exec.simps)
      apply (cases cs rule: rev_cases)
       apply (clarsimp simp del: exec.simps)
       apply (drule exec_last_frs_eq_class, fastforce+)
      apply (clarsimp simp del: exec.simps)
      apply (simp only: append_Cons [symmetric])
      apply (frule valid_callstack_append_last_class)
      apply (frule valid_callstack_append_last_method)
      apply (clarsimp simp del: exec.simps)
      apply (drule exec_last_frs_eq_class, fastforce+)
     apply (cases cs rule: rev_cases)
      apply (clarsimp simp del: exec.simps)
      apply (drule exec_last_frs_eq_method, fastforce+)
     apply (clarsimp simp del: exec.simps)
     apply (simp only: append_Cons [symmetric])
     apply (frule valid_callstack_append_last_method)
     apply (clarsimp simp del: exec.simps)
     by (drule exec_last_frs_eq_method, fastforce+)
  show "\<exists>n' as.
             CFG.path sourcenode targetnode (valid_edge prog) n as n' \<and>
             transfers (CFG.kinds kind as) s = s' \<and>
             preds (CFG.kinds kind as) s \<and> identifies n' c'"
  proof
    show "\<exists>as. CFG.path sourcenode targetnode (valid_edge prog) n as (_ c',None _) \<and>
      transfers (CFG.kinds kind as) s = s' \<and>
      preds (CFG.kinds kind as) s \<and>
      identifies (_ c',None _) c'"
    proof (cases "(instrs_of (P\<^bsub>wf\<^esub>) C M)!pc")
      case (Load nat)
      with sem_step s s' c prog 
      have c': "c' = (C,M,pc+1)#cs"
        by (auto elim!: sem.cases)
      from applicable sees_M Load
      have "nat < length LT"
        by simp
      from sees_M Load have "Suc pc \<in> set (succs (is ! pc) (ST,LT) pc)"
        by simp
      with prog sem_step Load v_cs_succ
      have v_edge:"valid_edge prog ((_ (C,M,pc)#cs,None _),
        \<Up>(\<lambda>s. exec_instr (instrs_of (P\<^bsub>wf\<^esub>) C M ! pc) P s (length cs) (stkLength P C M pc) 0 0),
        (_ (C,M,Suc pc)#cs,None _))"
        (is "valid_edge prog ?e1")
        by (auto elim!: sem.cases intro: JCFG_Straight_NoExc)
      with \<open>identifies n c\<close> c c' have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
        by -(simp,
          rule JVM_CFG_Interpret.path.Cons_path,
          rule JVM_CFG_Interpret.path.empty_path,
          auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
      moreover from Load jvm_exec loc' stk' c c' s s' prog wt \<open>nat < length LT\<close>
      have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
        by (auto intro!: ext
                   simp: JVM_CFG_Interpret.kinds_def
                         nth_stkss (* nth_stks *) nth_locss (* nth_locs *) nth_Cons' nth_tl
                         not_less_eq_eq Suc_le_eq)
      moreover have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
        by (simp add: JVM_CFG_Interpret.kinds_def)
      ultimately show ?thesis by fastforce
    next
      case (Store nat)
      with sem_step s s' c prog
      have c': "c' = (C,M,pc+1)#cs"
        by (auto elim!: sem.cases)
      from applicable Store sees_M
      have "length ST > 0 \<and> nat < length LT"
        by clarsimp
      then obtain ST1 STr where [simp]: "ST = ST1#STr" by (cases ST, fastforce+)
      from sees_M Store have "Suc pc \<in> set (succs (is ! pc) (ST, LT) pc)"
        by simp
      with prog sem_step Store v_cs_succ
      have v_edge:"valid_edge prog ((_ (C,M,pc)#cs,None _),
        \<Up>(\<lambda>s. exec_instr (instrs_of (P\<^bsub>wf\<^esub>) C M ! pc) P s (length cs) (stkLength P C M pc) 0 0),
        (_ (C,M,Suc pc)#cs,None _))"
        (is "valid_edge prog ?e1")
        by (fastforce elim: sem.cases intro: JCFG_Straight_NoExc)
      with \<open>identifies n c\<close> c c' have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
        by -(simp,
          rule JVM_CFG_Interpret.path.Cons_path,
          rule JVM_CFG_Interpret.path.empty_path,
          auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
      moreover from Store jvm_exec stk' loc' c c' s s' prog wt
        \<open>length ST > 0 \<and> nat < length LT\<close>
      have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
        by (auto intro!: ext
                   simp: JVM_CFG_Interpret.kinds_def
                         nth_stkss (* nth_stks *) nth_locss (* nth_locs *) nth_Cons' nth_tl
                         not_less_eq_eq hd_stks)
      moreover have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
        by (simp add: JVM_CFG_Interpret.kinds_def)
      ultimately show ?thesis by fastforce
    next
      case (Push val)
      with sem_step s s' c prog 
      have c': "c' = (C,M,pc+1)#cs"
        by (auto elim!: sem.cases)
      from sees_M Push have "Suc pc \<in> set (succs (is ! pc) (ST, LT) pc)"
        by simp
      with prog sem_step Push v_cs_succ
      have v_edge:"valid_edge prog ((_ (C,M,pc)#cs,None _),
        \<Up>(\<lambda>s. exec_instr (instrs_of (P\<^bsub>wf\<^esub>) C M ! pc) P s (length cs) (stkLength P C M pc) 0 0),
        (_ (C,M,Suc pc)#cs,None _))"
        (is "valid_edge prog ?e1")
        by (fastforce elim: sem.cases intro: JCFG_Straight_NoExc)
      with \<open>identifies n c\<close> c c' have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
        by -(simp,
          rule JVM_CFG_Interpret.path.Cons_path,
          rule JVM_CFG_Interpret.path.empty_path,
          auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
      moreover from Push jvm_exec stk' loc' c c' s s' prog wt
      have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
        by (auto intro!: ext
                   simp: JVM_CFG_Interpret.kinds_def
                         nth_stkss (* nth_stks *) nth_locss (* nth_locs *) nth_Cons' nth_tl
                         not_less_eq_eq)
      moreover have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
        by (simp add: JVM_CFG_Interpret.kinds_def)
      ultimately show ?thesis by fastforce
    next
      case (New Cl)
      show ?thesis
      proof (cases "new_Addr h")
        case None
        with New sem_step s s' c prog prealloc
        have c': "c' = find_handler_for P OutOfMemory c"
          by (fastforce elim!: sem.cases 
                        dest: find_handler_find_handler_forD)
        with jvm_exec New None prealloc
        have f2c_frs'_c': "framestack_to_callstack frs' = c'"
          by (auto dest!: find_handler_find_handler_forD)
        with New c' v_cs v_cs_f2c_frs'
        have v_pred_edge:"valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc). new_Addr h = None)\<^sub>\<surd>,
          (_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _))"
          (is "valid_edge prog ?e1")
          apply auto
               apply (rule JCFG_New_Exc_Pred, fastforce+)
              apply (rule_tac x="(\<lambda>(h, stk, loc). new_Addr h = None)" in exI)
              apply (rule JCFG_New_Exc_Pred, fastforce+)
             apply (cases "find_handler_for P OutOfMemory cs")
              apply (rule exI)
              apply clarsimp
              apply (rule JCFG_New_Exc_Exit, fastforce+)
             apply clarsimp
             apply (rule_tac x="\<lambda>(h, stk, loc).
               (h, stk((length list, stkLength P a aa b - Suc 0) :=
                        Addr (addr_of_sys_xcpt OutOfMemory)),
               loc)" in exI)
             apply (rule JCFG_New_Exc_Update, fastforce+)
            apply (rule JCFG_New_Exc_Pred, fastforce+)
           apply (rule exI)
           apply (rule JCFG_New_Exc_Pred, fastforce+)
          apply (rule exI)
          by (rule JCFG_New_Exc_Update, fastforce+)
        show ?thesis
        proof (cases c')
          case Nil
          with prog sem_step New c
          have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>([],True)\<rfloor> _),
            \<Up>id,
            (_Exit_))"
            (is "valid_edge prog ?e2")
            by (fastforce elim: sem.cases intro: JCFG_New_Exc_Exit)
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_Exit_)"
            by -(simp,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
          moreover from Nil None New sem_step c c' s s' prog
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto elim!: sem.cases simp: JVM_CFG_Interpret.kinds_def)
          moreover from None s have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis using Nil by fastforce
        next
          case (Cons a cs')
          then obtain C' M' pc' where Cons: "c' = (C',M',pc')#cs'" by (cases a, fastforce)
          from jvm_exec c s None New
          have "update_loc loc frs' = loc"
            by -(rule find_handler_loc_fun_eq' [of P _ h "(C,M,pc)#cs" stk loc], simp)
          with loc' have "loc' = loc"
            by simp
          from c Cons s s' sem_step jvm_exec prog       
          have "(C',M',pc')#cs' = framestack_to_callstack frs'"
            by (auto elim!: sem.cases)
          moreover obtain stk'' loc'' frs'' where frs': "frs' = (stk'',loc'',C',M',pc')#frs''"
            and cs': "cs' = framestack_to_callstack frs''" using calculation
            by (cases frs', fastforce+)
          ultimately
          have "update_stk stk frs' =
            stk((length cs',stkLength P C' M' pc' - Suc 0) := Addr (addr_of_sys_xcpt OutOfMemory))"
            using c s c' None Cons prog New trg_state_correct wt jvm_exec prealloc stk'
            by -(rule find_handler_stk_fun_eq' [of P _ h "(C,M,pc)#cs" _ loc h'],
              auto dest!: list_all2_lengthD
                    simp: hd_stks split_beta framestack_to_callstack_def
                          correct_state_def)
          with stk' have stk':
            "stk' = 
            stk((length cs',stkLength P C' M' pc' - Suc 0) := Addr (addr_of_sys_xcpt OutOfMemory))"
            by simp
          from New Cons v_cs_f2c_frs' v_cs f2c_frs'_c'
          have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _),
            \<Up>(\<lambda>(h,stk,loc).
              (h,
               stk((length cs',(stkLength P C' M' pc') - 1) :=
                 Addr (addr_of_sys_xcpt OutOfMemory)),
               loc)
             ),
            (_ c',None _))"
            (is "valid_edge prog ?e2")
            apply auto
              apply (rule JCFG_New_Exc_Update)
                 apply fastforce
                apply fastforce
               using Cons c' apply simp
              apply simp
             using v_pred_edge c' Cons apply clarsimp
            using v_pred_edge c' Cons apply clarsimp
            done
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
            by -(rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce+)
          moreover from New c c' s s' loc' stk' \<open>loc' = loc\<close> prog jvm_exec None
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto dest: find_handler_heap_eqD
                     simp: JVM_CFG_Interpret.kinds_def)
          moreover from None s
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis by fastforce
        qed
      next
        case (Some obj)
        with New sem_step s s' c prog prealloc
        have c': "c' = (C,M,Suc pc)#cs"
          by (auto elim!: sem.cases)
        with New jvm_exec Some
        have f2c_frs'_c': "framestack_to_callstack frs' = c'"
          by auto
        with New c' v_cs v_cs_f2c_frs'
        have v_pred_edge: "valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc). new_Addr h \<noteq> None)\<^sub>\<surd>,
          (_ (C,M,pc)#cs,\<lfloor>(c',False)\<rfloor> _))"
          (is "valid_edge prog ?e1")
          apply auto
            apply (fastforce intro!: JCFG_New_Normal_Pred)
           apply (rule exI)
           apply (fastforce intro!: JCFG_New_Normal_Pred)
          apply (rule exI)
          by (fastforce intro!: JCFG_New_Normal_Update)
        from New sees_M have "Suc pc \<in> set (succs (is ! pc) (ST, LT) pc)"
          by simp
        with prog New c' sem_step prog v_cs_succ
        have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>(c',False)\<rfloor> _),
          \<Up>(\<lambda>s. exec_instr (instrs_of (P\<^bsub>wf\<^esub>) C M ! pc) P s (length cs) (stkLength P C M pc) 0 0),
          (_ (C,M,Suc pc)#cs,None _))"
          (is "valid_edge prog ?e2")
          by (auto elim!: sem.cases intro: JCFG_New_Normal_Update JCFG_New_Normal_Pred)
        with v_pred_edge \<open>identifies n c\<close> c c'
        have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
          by -(simp,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.empty_path,
            auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
        moreover from New jvm_exec loc' stk' c c' s s' prog Some
        have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
          by (auto intro!: ext
                     simp: JVM_CFG_Interpret.kinds_def
                           nth_stkss (* nth_stks *) nth_locss (* nth_locs *) nth_Cons'
                           not_less_eq_eq hd_stks)
        moreover from Some s
        have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
          by (simp add: JVM_CFG_Interpret.kinds_def)
        ultimately show ?thesis by fastforce
      qed
    next
      case (Getfield Fd Cl)
      with applicable sees_M
      have "length ST > 0"
        by clarsimp
      then obtain ST1 STr where ST [simp]: "ST = ST1#STr" by (cases ST, fastforce+)
      show ?thesis
      proof (cases "stk(length cs, stkLength P C M pc - 1) = Null")
        case True
        with Getfield sem_step s s' c prog prealloc wt
        have c': "c' = find_handler_for P NullPointer c"
          by (cases "the (h (the_Addr Null))",
              auto elim!: sem.cases 
                   dest!: find_handler_find_handler_forD
                    simp: hd_stks)
        with Getfield True jvm_exec prealloc
        have "framestack_to_callstack frs' = c'"
          by (auto simp: split_beta dest!: find_handler_find_handler_forD)
        with Getfield prog c' v_cs v_cs_f2c_frs'
        have v_pred_edge:"valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc). stk(length cs, stkLength P C M pc - 1) = Null)\<^sub>\<surd>,
          (_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _))"
          (is "valid_edge prog ?e1")
          apply (auto simp del: find_handler_for.simps)
            apply (fastforce intro!: JCFG_Getfield_Exc_Pred)
           apply (fastforce intro!: JCFG_Getfield_Exc_Pred)
          apply auto
           apply (cases "find_handler_for P NullPointer cs")
            apply (fastforce intro!: JCFG_Getfield_Exc_Exit)
           apply (fastforce intro!: JCFG_Getfield_Exc_Update)
          apply (fastforce intro!: JCFG_Getfield_Exc_Update)
          done
        show ?thesis
        proof (cases c')
          case Nil
          with Getfield c prog c' v_pred_edge
          have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>([],True)\<rfloor> _),
            \<Up>id,
            (_Exit_))"
            (is "valid_edge prog ?e2")
            by (fastforce intro: JCFG_Getfield_Exc_Exit)
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_Exit_)"
            by -(simp,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
          moreover from Nil True Getfield sem_step c c' s s' prog wt \<open>length ST > 0\<close>
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto elim!: sem.cases
                      simp: hd_stks split_beta JVM_CFG_Interpret.kinds_def)
          moreover from True s
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis using Nil by fastforce
        next
          case (Cons a cs')
          then obtain C' M' pc' where Cons: "c' = (C',M',pc')#cs'" by (cases a, fastforce)
          from jvm_exec c s True Getfield wt ST
          have "update_loc loc frs' = loc"
            by -(rule find_handler_loc_fun_eq' [of P _ h "(C,M,pc)#cs" stk loc],
                 auto simp: split_beta hd_stks)
          with loc' have "loc' = loc"
            by simp
          from c Cons s s' sem_step jvm_exec prog
          have cs'_f2c_frs': "(C',M',pc')#cs' = framestack_to_callstack frs'"
            by (auto elim!: sem.cases)
          moreover obtain stk'' loc'' frs'' where "frs' = (stk'',loc'',C',M',pc')#frs''"
            and "cs' = framestack_to_callstack frs''" using calculation
            by (cases frs', fastforce+)
          ultimately
          have "update_stk stk frs' =
            stk((length cs',stkLength P C' M' pc' - Suc 0) := Addr (addr_of_sys_xcpt NullPointer))"
            using c s c' True Cons prog Getfield trg_state_correct wt ST jvm_exec prealloc stk'
            by -(rule find_handler_stk_fun_eq' [of P _ h "(C,M,pc)#cs" _ loc h'],
              auto dest!: list_all2_lengthD
                    simp: hd_stks split_beta framestack_to_callstack_def
                          correct_state_def)
          with stk' have stk':
            "stk' = 
            stk((length cs',stkLength P C' M' pc' - Suc 0) := Addr (addr_of_sys_xcpt NullPointer))"
            by simp
          from prog Cons Getfield c' v_cs v_cs_f2c_frs' jvm_exec
          have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _),
            \<Up>(\<lambda>(h,stk,loc).
              (h,
               stk((length cs',(stkLength P C' M' pc') - 1) :=
                 Addr (addr_of_sys_xcpt NullPointer)),
               loc)
             ),
            (_ c',None _))"
            (is "valid_edge prog ?e2")
            apply (auto simp del: exec.simps find_handler_for.simps)
                apply (rule JCFG_Getfield_Exc_Update, fastforce+)
               apply (simp only: cs'_f2c_frs')
              apply (fastforce intro!: JCFG_Getfield_Exc_Pred)
             apply (fastforce intro!: JCFG_Getfield_Exc_Update)
            by (simp only: cs'_f2c_frs')
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
            by -(rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce+)
          moreover from Getfield c c' s s' loc' stk' prog True jvm_exec
            \<open>loc' = loc\<close> wt ST
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto dest: find_handler_heap_eqD
                     simp: JVM_CFG_Interpret.kinds_def split_beta hd_stks)
          moreover from True s
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis by fastforce
        qed
      next
        case False
        with Getfield sem_step s s' c prog prealloc wt \<open>length ST > 0\<close>
        have c': "c' = (C,M,Suc pc)#cs"
          by (auto elim!: sem.cases 
                    simp: split_beta hd_stks)
        with False Getfield jvm_exec prealloc
        have "framestack_to_callstack frs' = c'"
          by (auto dest!: find_handler_find_handler_forD simp: split_beta)
        with Getfield c' v_cs v_cs_f2c_frs'
        have v_pred_edge: "valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc). stk(length cs, stkLength P C M pc - 1) \<noteq> Null)\<^sub>\<surd>,
          (_ (C,M,pc)#cs,\<lfloor>(c',False)\<rfloor> _))"
          (is "valid_edge prog ?e1")
          apply auto
            apply (fastforce intro: JCFG_Getfield_Normal_Pred)
           apply (fastforce intro: JCFG_Getfield_Normal_Pred)
          by (fastforce intro: JCFG_Getfield_Normal_Update)
        with prog c' Getfield v_cs_succ sees_M
        have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>(c',False)\<rfloor> _),
          \<Up>(\<lambda>s. exec_instr (instrs_of (P\<^bsub>wf\<^esub>) C M ! pc) P s (length cs) (stkLength P C M pc) 0 0),
          (_ (C,M,Suc pc)#cs,None _))"
          (is "valid_edge prog ?e2")
          by (fastforce intro: JCFG_Getfield_Normal_Update)
        with v_pred_edge \<open>identifies n c\<close> c c'
        have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
          by -(simp,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.empty_path,
            auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
        moreover from Getfield jvm_exec stk' loc' c c' s s' prog False wt ST
        have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
          by (auto intro!: ext
                     simp: nth_stkss nth_locss nth_tl nth_Cons' hd_stks
                           not_less_eq_eq split_beta JVM_CFG_Interpret.kinds_def)
        moreover from False s
        have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
          by (simp add: JVM_CFG_Interpret.kinds_def)
        ultimately show ?thesis by fastforce
      qed
    next
      case (Putfield Fd Cl)
      with applicable sees_M
      have "length ST > 1"
        by clarsimp
      then obtain ST1 STr' where "ST = ST1#STr'"
        by (cases ST, fastforce+)
      with \<open>length ST > 1\<close> obtain ST2 STr
        where ST: "ST = ST1#ST2#STr"
        by (cases STr', fastforce+)
      show ?thesis
      proof (cases "stk(length cs, stkLength P C M pc - 2) = Null")
        case True
        with Putfield sem_step s s' c prog prealloc wt \<open>length ST > 1\<close>
        have c': "c' = find_handler_for P NullPointer c"
          by (auto elim!: sem.cases 
                   dest!: find_handler_find_handler_forD
                    simp: hd_tl_stks split_beta)
        with Putfield jvm_exec True prealloc \<open>length ST > 1\<close> wt
        have "framestack_to_callstack frs' = c'"
          by (auto dest!: find_handler_find_handler_forD simp: split_beta hd_tl_stks)
        with Putfield c' v_cs v_cs_f2c_frs'
        have v_pred_edge:"valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc). stk(length cs, stkLength P C M pc - 2) = Null)\<^sub>\<surd>,
          (_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _))"
          (is "valid_edge prog ?e1")
          apply (auto simp del: find_handler_for.simps)
            apply (fastforce intro: JCFG_Putfield_Exc_Pred)
           apply (fastforce intro: JCFG_Putfield_Exc_Pred)
          apply (cases "find_handler_for P NullPointer ((C, M, pc)#cs)")
           apply (fastforce intro: JCFG_Putfield_Exc_Exit)
          by (fastforce intro: JCFG_Putfield_Exc_Update)
        show ?thesis
        proof (cases c')
          case Nil
          with Putfield c prog c' v_pred_edge
          have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>([],True)\<rfloor> _),
            \<Up>id,
            (_Exit_))"
            (is "valid_edge prog ?e2")
            by (fastforce intro: JCFG_Putfield_Exc_Exit)
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_Exit_)"
            by -(simp,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
          moreover from Nil True Putfield sem_step c c' s s' prog wt ST
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto elim!: sem.cases
                      simp: split_beta JVM_CFG_Interpret.kinds_def)
          moreover from True s
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis using Nil by fastforce
        next
          case (Cons a cs')
          then obtain C' M' pc' where Cons: "c' = (C',M',pc')#cs'" by (cases a, fastforce)
          from jvm_exec c s True Putfield ST wt
          have "update_loc loc frs' = loc"
            by -(rule find_handler_loc_fun_eq' [of P _ h "(C,M,pc)#cs" stk loc],
                 auto simp: split_beta hd_tl_stks if_split_eq1)
          with sem_step s s' c prog jvm_exec
          have loc':"loc' = loc"
            by (clarsimp elim!: sem.cases)
          from c Cons s s' sem_step jvm_exec prog       
          have "stk' = update_stk stk frs'"
            and cs'_f2c_frs': "(C',M',pc')#cs' = framestack_to_callstack frs'"
            by (auto elim!: sem.cases)
          moreover obtain stk'' loc'' frs'' where "frs' = (stk'',loc'',C',M',pc')#frs''"
            and "cs' = framestack_to_callstack frs''" using calculation
            by (cases frs', fastforce+)
          ultimately
          have stk':
            "update_stk stk frs' =
            stk((length cs',stkLength P C' M' pc' - Suc 0) := Addr (addr_of_sys_xcpt NullPointer))"
            using c s Cons True prog Putfield ST wt trg_state_correct jvm_exec
            by -(rule find_handler_stk_fun_eq' [of P _ h "(C,M,pc)#cs" _ loc h'],
              auto dest!: list_all2_lengthD
                    simp: hd_stks hd_tl_stks split_beta framestack_to_callstack_def
                          correct_state_def)
          from Cons Putfield c prog c' v_pred_edge v_cs_f2c_frs' jvm_exec
          have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _),
            \<Up>(\<lambda>(h,stk,loc).
              (h, stk((length cs',(stkLength P C' M' pc') - 1) :=
                    Addr (addr_of_sys_xcpt NullPointer)), loc) ),
            (_ c',None _))"
            (is "valid_edge prog ?e2")
            by (auto intro!: JCFG_Putfield_Exc_Update)
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
            by -(rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce+)
          moreover from True Putfield c c' s s' loc' stk' \<open>stk' = update_stk stk frs'\<close>
                        jvm_exec wt ST
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto dest: find_handler_heap_eqD
                     simp: JVM_CFG_Interpret.kinds_def hd_tl_stks split_beta)
          moreover from True s
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis by fastforce
        qed
      next
        case False
        with Putfield sem_step s s' c prog prealloc wt \<open>length ST > 1\<close>
        have c': "c' = (C,M,Suc pc)#cs"
          by (auto elim!: sem.cases 
                    simp: hd_tl_stks split_beta)
        with Putfield False jvm_exec \<open>length ST > 1\<close> wt
        have "framestack_to_callstack frs' = c'"
          by (auto simp: split_beta hd_tl_stks)
        with Putfield c' v_cs v_cs_f2c_frs'
        have v_pred_edge: "valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc). stk(length cs, stkLength P C M pc - 2) \<noteq> Null)\<^sub>\<surd>,
          (_ (C,M,pc)#cs,\<lfloor>(c',False)\<rfloor> _))"
          (is "valid_edge prog ?e1")
          apply auto
            apply (fastforce intro: JCFG_Putfield_Normal_Pred)
           apply (fastforce intro: JCFG_Putfield_Normal_Pred)
          by (fastforce intro: JCFG_Putfield_Normal_Update)
        with prog Putfield c' v_cs_succ sees_M
        have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>(c',False)\<rfloor> _),
          \<Up>(\<lambda>s. exec_instr (instrs_of (P\<^bsub>wf\<^esub>) C M ! pc) P s (length cs) (stkLength P C M pc) 0 0),
          (_ (C,M,Suc pc)#cs,None _))"
          (is "valid_edge prog ?e2")
          by (fastforce intro: JCFG_Putfield_Normal_Update)
        with v_pred_edge \<open>identifies n c\<close> c c'
        have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
          by -(simp,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.empty_path,
            auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
        moreover from Putfield jvm_exec stk' loc' c c' s s' prog False wt ST
        have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
          by (auto intro!: ext
                     simp: JVM_CFG_Interpret.kinds_def split_beta
                           (* nth_stks *) nth_stkss (* nth_locs *) nth_locss nth_Cons'
                           not_less_eq_eq)
        moreover from False s
        have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
          by (simp add: JVM_CFG_Interpret.kinds_def)
        ultimately show ?thesis by fastforce
      qed
    next
      case (Checkcast Cl)
      with applicable sees_M
      have "length ST > 0"
        by clarsimp
      then obtain ST1 STr where ST: "ST = ST1#STr" by (cases ST, fastforce+)
      show ?thesis
      proof (cases "\<not> cast_ok (P\<^bsub>wf\<^esub>) Cl h (stk(length cs,length ST - Suc 0))")
        case True
        with Checkcast sem_step s s' c prog prealloc wt \<open>length ST > 0\<close>
        have c': "c' = find_handler_for P ClassCast c"
          by (auto elim!: sem.cases 
                   dest!: find_handler_find_handler_forD
                    simp: hd_stks split_beta)
        with jvm_exec Checkcast True prealloc \<open>length ST > 0\<close> wt
        have "framestack_to_callstack frs' = c'"
          by (auto dest!: find_handler_find_handler_forD simp: hd_stks)
        with Checkcast c' v_cs v_cs_f2c_frs'
        have v_pred_edge:"valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc). \<not> cast_ok (P\<^bsub>wf\<^esub>) Cl h (stk(length cs, stkLength P C M pc - Suc 0)))\<^sub>\<surd>,
          (_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _))"
          (is "valid_edge prog ?e1")
          apply (auto simp del: find_handler_for.simps)
            apply (fastforce intro: JCFG_Checkcast_Exc_Pred)
           apply (fastforce intro: JCFG_Checkcast_Exc_Pred)
          apply (cases "find_handler_for P ClassCast ((C,M,pc)#cs)")
           apply (fastforce intro: JCFG_Checkcast_Exc_Exit)
          by (fastforce intro: JCFG_Checkcast_Exc_Update)
        show ?thesis
        proof (cases c')
          case Nil
          with Checkcast c prog c' v_pred_edge
          have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>([],True)\<rfloor> _),
            \<Up>id,
            (_Exit_))"
            (is "valid_edge prog ?e2")
            by (fastforce intro: JCFG_Checkcast_Exc_Exit)
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_Exit_)"
            by -(simp,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
          moreover from Nil True Checkcast sem_step c c' s s' prog wt \<open>length ST > 0\<close>
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto elim!: sem.cases
                      simp: hd_stks split_beta JVM_CFG_Interpret.kinds_def)
          moreover from True s wt
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis using Nil by fastforce
        next
          case (Cons a cs')
          then obtain C' M' pc' where Cons: "c' = (C',M',pc')#cs'" by (cases a, fastforce)
          from jvm_exec c s True Checkcast ST wt
          have loc'': "update_loc loc frs' = loc"
            by -(rule find_handler_loc_fun_eq' [of P _ h "(C,M,pc)#cs" stk loc],
                 auto simp: split_beta hd_tl_stks if_split_eq1)
          from c Cons s s' sem_step jvm_exec prog       
          have "stk' = update_stk stk frs'"
            and [simp]: "framestack_to_callstack frs' = (C', M', pc')#cs'"
            by (auto elim!: sem.cases)
          moreover obtain stk'' loc'' frs'' where "frs' = (stk'',loc'',C',M',pc')#frs''"
            and "cs' = framestack_to_callstack frs''" using calculation
            by (cases frs', fastforce+)
          ultimately
          have stk'':
            "update_stk stk frs' =
            stk((length cs',stkLength P C' M' pc' - Suc 0) := Addr (addr_of_sys_xcpt ClassCast))"
            using c s Cons True prog Checkcast ST wt trg_state_correct jvm_exec
            by -(rule find_handler_stk_fun_eq' [of P _ h "(C,M,pc)#cs" _ loc h'],
              auto dest!: list_all2_lengthD
                    simp: hd_stks hd_tl_stks split_beta framestack_to_callstack_def
                          correct_state_def)
          from prog Checkcast Cons c c' v_pred_edge v_cs_f2c_frs'
          have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _),
            \<Up>(\<lambda>(h,stk,loc).
              (h,
               stk((length cs',(stkLength P C' M' pc') - 1) :=
                 Addr (addr_of_sys_xcpt ClassCast)),
               loc)
             ),
            (_ c',None _))"
            (is "valid_edge prog ?e2")
            by (auto intro!: JCFG_Checkcast_Exc_Update)
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
            by -(rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce+)
          moreover from True Checkcast c s s' loc' stk' loc'' stk''
                        prog wt ST jvm_exec
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto dest: find_handler_heap_eqD
                        simp: JVM_CFG_Interpret.kinds_def split_beta)
          moreover from True s wt
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis by fastforce
        qed
      next
        case False
        with Checkcast sem_step s s' c prog prealloc wt \<open>length ST > 0\<close>
        have c': "c' = (C,M,Suc pc)#cs"
          by (auto elim!: sem.cases 
                    simp: hd_stks split_beta)
        with prog Checkcast sem_step c s v_cs_succ sees_M
        have v_pred_edge: "valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc). cast_ok (P\<^bsub>wf\<^esub>) Cl h (stk(length cs, stkLength P C M pc - Suc 0)))\<^sub>\<surd>,
          (_ (C,M,Suc pc)#cs,None _))"
          (is "valid_edge prog ?e1")
          by (auto intro!: JCFG_Checkcast_Normal_Pred elim: sem.cases)
        with \<open>identifies n c\<close> c c'
        have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
          by -(simp,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.empty_path,
            auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
        moreover from Checkcast jvm_exec stk' loc' c s s' prog False wt ST
        have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
          by (auto elim!: sem.cases
                  intro!: ext
                    simp: split_beta hd_stks JVM_CFG_Interpret.kinds_def
                          (* nth_stks *) nth_stkss (* nth_locs *) nth_locss nth_Cons'
                          not_less_eq_eq)
        moreover from False s wt
        have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
          by (simp add: JVM_CFG_Interpret.kinds_def)
        ultimately show ?thesis by fastforce
      qed
    next
      case (Invoke M' n')
      with applicable sees_M
      have "length ST > n'"
        by clarsimp
      moreover obtain STn where "STn = take n' ST" by fastforce
      moreover obtain STs where "STs = ST ! n'" by fastforce
      moreover obtain STr where "STr = drop (Suc n') ST" by fastforce
      ultimately have ST:" ST = STn@STs#STr \<and> length STn = n'"
        by (auto simp: id_take_nth_drop)
      with jvm_exec c s Invoke wt
      have "h = h'"
        by (auto dest: find_handler_heap_eqD
                 simp: split_beta (* nth_stks *) nth_Cons' if_split_eq1)
      show ?thesis
      proof (cases "stk(length cs, stkLength P C M pc - Suc n') = Null")
        case True
        with Invoke sem_step prog prealloc wt ST
        have c': "c' = find_handler_for P NullPointer c"
          apply (auto elim!: sem.cases
                      simp: (* nth_stks *) split_beta nth_Cons' ST
                      split: if_split_asm)
           by (auto dest!: find_handler_find_handler_forD)
        with jvm_exec True Invoke wt ST prealloc
        have "framestack_to_callstack frs' = c'"
          by (auto dest!: find_handler_find_handler_forD
                    simp: split_beta nth_Cons' (* nth_stks *) if_split_eq1)
        with Invoke c' v_cs v_cs_f2c_frs'
        have v_pred_edge: "valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc). stk(length cs, stkLength P C M pc - Suc n') = Null )\<^sub>\<surd>,
          (_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _))"
          (is "valid_edge prog ?e1")
          apply (auto simp del: find_handler_for.simps)
            apply (fastforce intro: JCFG_Invoke_Exc_Pred)
           apply (fastforce intro: JCFG_Invoke_Exc_Pred)
          apply (cases "find_handler_for P NullPointer ((C, M, pc) # cs)")
           apply (fastforce intro: JCFG_Invoke_Exc_Exit)
          by (fastforce intro: JCFG_Invoke_Exc_Update)
        show ?thesis
        proof (cases c')
          case Nil
          with prog Invoke c c' v_pred_edge
          have v_exec_edge: "valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>([],True)\<rfloor> _),
            \<Up>id,
            (_Exit_))"
            (is "valid_edge prog ?e2")
            by (fastforce intro: JCFG_Invoke_Exc_Exit)
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
            by -(simp,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
          moreover from Invoke jvm_exec stk' loc' c c' s s'
            prog True wt ST prealloc Nil \<open>h = h'\<close>
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto dest!: find_handler_find_handler_forD
                      simp: split_beta JVM_CFG_Interpret.kinds_def
                            (* nth_stks *) nth_Cons' if_split_eq1 framestack_to_callstack_def)
          moreover from s True
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis by fastforce
        next
          case (Cons a cs')
          then obtain C' M' pc' where Cons: "c' = (C',M',pc')#cs'" 
            by (cases a, fastforce)
          from jvm_exec c s True Invoke ST wt
          have loc'': "update_loc loc frs' = loc"
            by -(rule find_handler_loc_fun_eq' [of P _ h "(C,M,pc)#cs" stk loc],
                 auto simp: split_beta if_split_eq1 nth_Cons' (* nth_stks *))
          from c Cons s s' sem_step jvm_exec prog       
          have "stk' = update_stk stk frs'"
            and [simp]: "framestack_to_callstack frs' = (C',M',pc')#cs'"
            by (auto elim!: sem.cases)
          moreover obtain stk'' loc'' frs'' where "frs' = (stk'',loc'',C',M',pc')#frs''"
            and "cs' = framestack_to_callstack frs''" using calculation
            by (cases frs', fastforce+)
          ultimately
          have stk'':
            "update_stk stk frs' =
            stk((length cs',stkLength P C' M' pc' - Suc 0) := Addr (addr_of_sys_xcpt NullPointer))"
            using c s Cons True prog Invoke ST wt trg_state_correct jvm_exec
            by -(rule find_handler_stk_fun_eq' [of P _ h "(C,M,pc)#cs" _ loc h'],
              auto dest!: list_all2_lengthD
                    simp: (* nth_stks *) nth_Cons' split_beta correct_state_def if_split_eq1)
          from Cons Invoke c prog c' v_pred_edge v_cs_f2c_frs'
          have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _),
            \<Up>(\<lambda>(h,stk,loc).
              (h, stk((length cs',(stkLength P C' M' pc') - 1) :=
                         Addr (addr_of_sys_xcpt NullPointer)), loc) ),
            (_ c',None _))"
            (is "valid_edge prog ?e2")
            by (auto intro!: JCFG_Invoke_Exc_Update)
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
            by -(rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce+)
          moreover from Cons True Invoke jvm_exec c c' s s' loc' stk' loc'' stk''
                        prog wt ST \<open>h = h'\<close>
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto simp: JVM_CFG_Interpret.kinds_def split_beta)
          moreover from True s
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis by fastforce
        qed
      next
        case False
        obtain D where D:
          "D = fst (method P\<^bsub>wf\<^esub> (cname_of h (the_Addr (stk (length cs, length ST - Suc n')))) M')"
          by simp
        from c wt s state_correct
        have "(P\<^bsub>wf\<^esub>),h \<turnstile> stks (length ST) (\<lambda>a. stk (length cs, a)) [:\<le>] ST"
          by (clarsimp simp: bv_conform_def correct_state_def)
        with False ST wt
        have "STs \<noteq> NT"
          apply -
          apply (drule_tac p="n'" in list_all2_nthD)
           apply simp
          apply (auto simp: nth_Cons' split: if_split_asm)
          apply hypsubst_thin
          by (induct STn, auto simp: nth_Cons' split: if_split_asm)
        with applicable ST Invoke sees_M
        obtain D' where D': "STs = Class D'"
          by (clarsimp simp: nth_append)
        from Invoke c s jvm_exec False wt ST D
        obtain loc'' where frs': "frs' = ([],loc'',D,M',0)#(snd(snd(state_to_jvm_state P c s)))"
          by (auto simp: split_beta if_split_eq1 (* nth_stks *) nth_Cons' ST)
        with trg_state_correct
        obtain Ts' T' mb' where D_sees_M': "(P\<^bsub>wf\<^esub>) \<turnstile> D sees M':Ts'\<rightarrow>T' = mb' in D"
          by (auto simp: correct_state_def)
        from state_correct c s wt ST D'
        have stk_wt: "P\<^bsub>wf\<^esub>,h \<turnstile> stk (length cs, length STn + length STr) #
          stks (length STn + length STr) (\<lambda>a. stk (length cs, a)) [:\<le>] STn @ Class D' # STr"
          by (auto simp: correct_state_def)
        have "(stk (length cs, length STn + length STr) #
          stks (length STn + length STr) (\<lambda>a. stk (length cs, a))) ! length STn =
          stk (length cs, length STr) "
          by (auto simp: nth_Cons' (* nth_stks *) ST)
        with stk_wt
        have "P\<^bsub>wf\<^esub>,h \<turnstile> stk (length cs, length STr) :\<le> Class D'"
          by (drule_tac P="conf (P\<^bsub>wf\<^esub>) h" and p="length STn" in list_all2_nthD,
            auto simp: nth_append)
        with False ST wt
        have subD': "(P\<^bsub>wf\<^esub>) \<turnstile> (cname_of h (the_Addr (stk (length cs, length ST - Suc n')))) \<preceq>\<^sup>* D'"
          by (cases "stk (length cs, length STr)", auto simp: conf_def)
        from trg_state_correct frs' D_sees_M' Invoke s c
        have "length Ts' = n'"
          by (auto dest: sees_method_fun simp: correct_state_def)
        with c trg_state_correct wt ST D_sees_M' D P_wf frs' subD' D'
        obtain Ts T mxs mxl "is" xt
          where stk_sees_M':
          "(P\<^bsub>wf\<^esub>) \<turnstile> (cname_of h (the_Addr (stk (length cs, length ST - Suc n'))))
                           sees M':Ts\<rightarrow>T = (mxs,mxl,is,xt) in D"
          by (auto dest: sees_method_fun
                  dest!: sees_method_mono
                   simp: correct_state_def split_beta nth_append wf_jvm_prog_phi_def
               simp del: ST)
        with c s False jvm_exec Invoke frs' wt \<open>length ST > n'\<close>
        have loc'':
          "loc'' = stk (length cs, length ST - Suc n') #
                   rev (take n' (stks (length ST) (\<lambda>a. stk(length cs, a)))) @
                   replicate mxl arbitrary"
          by (auto simp: split_beta (* nth_stks *) if_split_eq1 simp del: ST)
        with trg_state_correct frs' Invoke wt \<open>length ST > n'\<close>
        have locLength_trg:
          "locLength P D M' 0 = n' + Suc mxl"
          by (auto dest: list_all2_lengthD simp: correct_state_def)
        from stk' frs' c s
        have "stk' = stk"
          by (auto intro!: ext
                     simp: (* nth_stks *) nth_stkss nth_Cons' not_less_eq_eq Suc_le_eq
                 simp del: ST)
        from loc' frs' c s loc'' wt ST
        have upd_loc': "loc' = (\<lambda>(a, b).
           if a = Suc (length cs) \<longrightarrow> Suc (n' + mxl) \<le> b then loc (a, b)
           else if b \<le> n' then stk (length cs, Suc (n' + length STr) - (Suc n' - b))
                else arbitrary)"
          by (auto intro!: ext
                     simp: (* nth_locs *) nth_locss nth_Cons' nth_append rev_nth (* nth_stks *) 
                           not_less_eq_eq Suc_le_eq less_Suc_eq add.commute
                           min.absorb1 min.absorb2 max.absorb1 max.absorb2)
        from frs' jvm_exec sem_step prog
        have c': "c' = (D,M',0)#c"
          by (auto elim!: sem.cases)
        from frs'
        have "framestack_to_callstack frs' = (D, M', 0) # (C, M, pc) # cs"
          by simp
        with Invoke c' v_cs v_cs_f2c_frs'
        have v_pred_edge: "valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk',loc).
            stk'(length cs, stkLength P C M pc - Suc n') \<noteq> Null \<and>
            fst(method (P\<^bsub>wf\<^esub>)
                 (cname_of h (the_Addr(stk'(length cs, stkLength P C M pc - Suc n')))) M'
            ) = D
          )\<^sub>\<surd>,
          (_ (C,M,pc)#cs,\<lfloor>(c',False)\<rfloor> _))"
          (is "valid_edge prog ?e1")
          apply auto
            apply (fastforce intro: JCFG_Invoke_Normal_Pred)
           apply (fastforce intro: JCFG_Invoke_Normal_Pred)
          apply (rule exI)
          by (fastforce intro: JCFG_Invoke_Normal_Update)
        with Invoke v_cs_f2c_frs' c' v_cs
        have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>(c',False)\<rfloor> _),
          \<Up>(\<lambda>s.
            exec_instr (instrs_of (P\<^bsub>wf\<^esub>) C M ! pc) P s
              (length cs) (stkLength P C M pc) 0 (locLength P D M' 0)
          ),
          (_ (D,M',0)#c,None _))"
          (is "valid_edge prog ?e2")
          by (fastforce intro!: JCFG_Invoke_Normal_Update
                     simp del: exec.simps valid_callstack.simps)
        with v_pred_edge \<open>identifies n c\<close> c c' locLength_trg
        have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
          by -(simp,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.empty_path,
            auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
        moreover from s s' \<open>h = h'\<close> \<open>stk' = stk\<close> upd_loc'
          locLength_trg stk_sees_M' Invoke c wt ST
        have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'" 
          by (simp add: JVM_CFG_Interpret.kinds_def)
        moreover from False s D wt have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
          by (simp add: JVM_CFG_Interpret.kinds_def)
        ultimately show ?thesis by fastforce
      qed
    next
      case Return
      with applicable sees_M
      have "length ST > 0"
        by clarsimp
      then obtain ST1 STr where ST: "ST = ST1#STr" by (cases ST, fastforce+)
      show ?thesis
      proof (cases cs)
        case Nil
        with sem_step s s' c prog Return
        have c': "c' = [] \<and> C = C0 \<and> M = M0"
          by (auto elim!: sem.cases)
        with prog sem_step Return Nil c
        have v_edge: "valid_edge prog ((_ (C,M,pc)#cs,None _),
          \<Up>id,
          (_Exit_))"
          (is "valid_edge prog ?e1")
          by (fastforce intro: JCFG_ReturnExit elim: sem.cases)
        with \<open>identifies n c\<close> c c' have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
          by -(simp,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.empty_path,
            auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
        moreover from Return sem_step c c' s s' prog wt Nil \<open>length ST > 0\<close>
        have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
          by (auto elim!: sem.cases simp: JVM_CFG_Interpret.kinds_def)
        moreover have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
          by (simp add: JVM_CFG_Interpret.kinds_def)
        ultimately show ?thesis by fastforce
      next
        case (Cons a cs')
        with c obtain D M' pc' where c: "c = (C,M,pc)#(D,M',pc')#cs'" by (cases a, fastforce)
        with prog sem_step Return
        have c': "c' = (D,M',Suc pc')#cs'"
          by (auto elim!: sem.cases)
        from c s jvm_exec Return
        have "h = h'"
          by (auto simp: split_beta)
        from c s jvm_exec loc' Return
        have "loc' = loc"
          by (auto intro!: ext
                     simp: split_beta not_less_eq_eq Suc_le_eq not_less_eq less_Suc_eq_le
                           (* nth_locs *) nth_locss hd_stks nth_Cons')
        from c s jvm_exec stk' Return ST wt trg_state_correct
        have stk_upd:
          "stk' =
          stk((length cs', stkLength P D M' (Suc pc') - 1) :=
            stk(Suc (length cs'), length ST - 1))"
          by (auto intro!: ext
                    dest!: list_all2_lengthD
                     simp: split_beta not_less_eq_eq Suc_le_eq
                           (* nth_stks *) nth_stkss hd_stks nth_Cons' correct_state_def)
        from jvm_exec Return c' c
        have "framestack_to_callstack frs' = c'"
          by auto
        with Return v_cs v_cs_f2c_frs' c' c
        have v_edge: "valid_edge prog ((_ (C,M,pc)#(D,M',pc')#cs',None _),
          \<Up>(\<lambda>s. exec_instr Return P s
             (Suc (length cs')) (stkLength P C M pc) (stkLength P D M' (Suc pc')) 0),
          (_ (D,M',Suc pc')#cs',None _))"
          (is "valid_edge prog ?e1")
          by (fastforce intro: JCFG_Return_Update)
        with \<open>identifies n c\<close> c c' 
        have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
          by -(simp,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.empty_path,
            auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
        moreover from stk' loc' s s' \<open>h = h'\<close> \<open>loc' = loc\<close> stk_upd wt
        have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
          by (simp add: JVM_CFG_Interpret.kinds_def)
        moreover have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
          by (simp add: JVM_CFG_Interpret.kinds_def)
        ultimately show ?thesis by fastforce
      qed
    next
      case Pop
      with sem_step s s' c prog 
      have c': "c' = (C,M,pc+1)#cs"
        by (auto elim!: sem.cases)
      from Pop sees_M applicable
      have "ST \<noteq> []"
        by clarsimp
      then obtain ST1 STr where ST: "ST = ST1#STr"
        by (cases ST, fastforce+)
      with c' jvm_exec Pop
      have "framestack_to_callstack frs' = c'"
        by auto
      with Pop v_cs v_cs_f2c_frs' c'
      have v_edge:"valid_edge prog ((_ (C,M,pc)#cs,None _),
        \<Up>(\<lambda>s. exec_instr (instrs_of (P\<^bsub>wf\<^esub>) C M ! pc) P s (length cs) (stkLength P C M pc) 0 0),
        (_ (C,M,Suc pc)#cs,None _))"
        (is "valid_edge prog ?e1")
        by (fastforce intro: JCFG_Straight_NoExc)
      with \<open>identifies n c\<close> c c' have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
        by -(simp,
          rule JVM_CFG_Interpret.path.Cons_path,
          rule JVM_CFG_Interpret.path.empty_path,
          auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
      moreover from Pop jvm_exec s s' stk' loc' c wt ST
      have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
        by (auto intro!: ext
                   simp: nth_stkss (* nth_stks *) nth_locss (* nth_locs *) nth_Cons' nth_tl
                         not_less_eq_eq Suc_le_eq JVM_CFG_Interpret.kinds_def)
      moreover have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
        by (simp add: JVM_CFG_Interpret.kinds_def)
      ultimately show ?thesis by fastforce
    next
      case IAdd
      with sem_step s s' c prog 
      have c': "c' = (C,M,pc+1)#cs"
        by (auto elim!: sem.cases)
      from IAdd applicable sees_M
      have "length ST > 1"
        by clarsimp
      then obtain ST1 STr' where "ST = ST1#STr'" by (cases ST, fastforce+)
      with \<open>length ST > 1\<close> obtain ST2 STr
        where ST: "ST = ST1#ST2#STr" by (cases STr', fastforce+)
      from c' jvm_exec IAdd
      have "framestack_to_callstack frs' = c'"
        by auto
      with IAdd c' v_cs v_cs_f2c_frs'
      have v_edge:"valid_edge prog ((_ (C,M,pc)#cs,None _),
        \<Up>(\<lambda>s. exec_instr (instrs_of (P\<^bsub>wf\<^esub>) C M ! pc) P s (length cs) (stkLength P C M pc) 0 0),
        (_ (C,M,Suc pc)#cs,None _))"
        (is "valid_edge prog ?e1")
        by (fastforce intro: JCFG_Straight_NoExc)
      with \<open>identifies n c\<close> c c'
      have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
        by -(simp,
          rule JVM_CFG_Interpret.path.Cons_path,
          rule JVM_CFG_Interpret.path.empty_path,
          auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
      moreover from IAdd jvm_exec c s s' stk' loc' wt ST
      have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
        by (auto intro!: ext
                   simp: nth_stkss (* nth_stks *) nth_locss (* nth_locs *) nth_Cons' nth_tl
                         hd_stks hd_tl_stks
                         not_less_eq_eq Suc_le_eq JVM_CFG_Interpret.kinds_def)
      moreover have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
        by (simp add: JVM_CFG_Interpret.kinds_def)
      ultimately show ?thesis by fastforce
    next
      case (IfFalse b)
      with applicable sees_M
      have "ST \<noteq> []"
        by clarsimp
      then obtain ST1 STr where ST [simp]: "ST = ST1#STr" by (cases ST, fastforce+)
      show ?thesis
      proof (cases "stk (length cs, stkLength P C M pc - 1) = Bool False \<and> b \<noteq> 1")
        case True
        with sem_step s s' c prog IfFalse wt ST
        have c': "c' = (C,M,nat (int pc + b))#cs"
          by (auto elim!: sem.cases
                    simp: hd_stks)
        with jvm_exec IfFalse True
        have "framestack_to_callstack frs' = c'"
          by auto
        with c' IfFalse True v_cs v_cs_f2c_frs'
        have v_edge: "valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc). stk (length cs, stkLength P C M pc - 1) = Bool False)\<^sub>\<surd>,
          (_ (C,M,nat (int pc + b))#cs,None _))"
          (is "valid_edge prog ?e1")
          by (fastforce intro: JCFG_IfFalse_False)
        with \<open>identifies n c\<close> c c' have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
          by -(simp,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.empty_path,
            auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
        moreover from IfFalse True jvm_exec c s s' stk' loc' wt ST
        have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
          by (auto intro!: ext
                     simp: hd_stks nth_stkss nth_locss nth_Cons' nth_tl
                           JVM_CFG_Interpret.kinds_def not_less_eq_eq)
        moreover from True s
        have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
          by (simp add: JVM_CFG_Interpret.kinds_def)
        ultimately show ?thesis by fastforce
      next
        case False
        have "nat (int pc + 1) = Suc pc"
          by (cases pc, auto)
        with False sem_step s s' c prog IfFalse wt ST
        have c': "c' = (C,M,Suc pc)#cs"
          by (auto elim!: sem.cases simp: hd_stks)
        with jvm_exec IfFalse False
        have "framestack_to_callstack frs' = c'"
          by auto
        with c' IfFalse False v_cs v_cs_f2c_frs'
        have v_edge: "valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc). stk (length cs, stkLength P C M pc - 1) \<noteq> Bool False \<or> b = 1)\<^sub>\<surd>,
          (_ (C,M,Suc pc)#cs,None _))"
          (is "valid_edge prog ?e1")
          by (fastforce intro: JCFG_IfFalse_Next)
        with \<open>identifies n c\<close> c c'
        have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
          by -(simp,
            rule JVM_CFG_Interpret.path.Cons_path,
            rule JVM_CFG_Interpret.path.empty_path,
            auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
        moreover from IfFalse False jvm_exec c s s' stk' loc' wt ST
        have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
          by (auto intro!: ext
                     simp: hd_stks nth_stkss nth_locss nth_Cons' nth_tl
                           JVM_CFG_Interpret.kinds_def not_less_eq_eq)
        moreover from False s
        have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
          by (simp add: JVM_CFG_Interpret.kinds_def)
        ultimately show ?thesis by fastforce
      qed
    next
      case (Goto i)
      with sem_step s s' c prog 
      have c': "c' = (C,M,nat (int pc + i))#cs"
        by (auto elim!: sem.cases)
      with jvm_exec Goto
      have "framestack_to_callstack frs' = c'"
        by auto
      with c' Goto v_cs v_cs_f2c_frs'
      have v_edge:"valid_edge prog ((_ (C,M,pc)#cs,None _),
        \<Up>id,
        (_ (C,M,nat (int pc + i))#cs,None _))"
        (is "valid_edge prog ?e1")
        by (fastforce intro: JCFG_Goto_Update)
      with \<open>identifies n c\<close> c c'
      have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
        by -(simp,
          rule JVM_CFG_Interpret.path.Cons_path,
          rule JVM_CFG_Interpret.path.empty_path,
          auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
      moreover from Goto jvm_exec c s s' stk' loc'
      have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
        by (auto intro!: ext
                   simp: nth_stkss (* nth_stks *) nth_locss (* nth_locs *) nth_Cons'
                         JVM_CFG_Interpret.kinds_def not_less_eq_eq)
      moreover have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
        by (simp add: JVM_CFG_Interpret.kinds_def)
      ultimately show ?thesis by fastforce
    next
      case CmpEq
      with sem_step s s' c prog 
      have c': "c' = (C,M,Suc pc)#cs"
        by (auto elim!: sem.cases)
      from CmpEq applicable sees_M
      have "length ST > 1"
        by clarsimp
      then obtain ST1 STr' where "ST = ST1#STr'" by (cases ST, fastforce+)
      with \<open>length ST > 1\<close> obtain ST2 STr
        where ST: "ST = ST1#ST2#STr" by (cases STr', fastforce+)
      from c' CmpEq jvm_exec
      have "framestack_to_callstack frs' = c'"
        by auto
      with c' CmpEq v_cs v_cs_f2c_frs'
      have v_edge:"valid_edge prog ((_ (C,M,pc)#cs,None _),
        \<Up>(\<lambda>s. exec_instr (instrs_of (P\<^bsub>wf\<^esub>) C M ! pc) P s (length cs) (stkLength P C M pc) 0 0),
        (_ (C,M,Suc pc)#cs,None _))"
        (is "valid_edge prog ?e1")
        by (fastforce intro: JCFG_Straight_NoExc)
      with \<open>identifies n c\<close> c c'
      have "JVM_CFG_Interpret.path prog n [?e1] (_ c',None _)"
        by -(simp,
          rule JVM_CFG_Interpret.path.Cons_path,
          rule JVM_CFG_Interpret.path.empty_path,
          auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
      moreover from CmpEq jvm_exec c s s' stk' loc' wt ST
      have "transfers (JVM_CFG_Interpret.kinds [?e1]) s = s'"
        by (auto intro!: ext
                   simp: nth_stkss (* nth_stks *) nth_locss (* nth_locs *) nth_Cons' nth_tl
                         hd_stks hd_tl_stks
                         not_less_eq_eq JVM_CFG_Interpret.kinds_def)
      moreover have "preds (JVM_CFG_Interpret.kinds [?e1]) s"
        by (simp add: JVM_CFG_Interpret.kinds_def)
      ultimately show ?thesis by fastforce
    next
      case Throw
      with sees_M applicable
      have "ST \<noteq> []"
        by clarsimp
      then obtain ST1 STr where ST: "ST = ST1#STr" by (cases ST, fastforce+)
      from jvm_exec sem_step
      have f2c_frs'_eq_c': "framestack_to_callstack frs' = c'"
        by (auto elim: sem.cases)
      show ?thesis
      proof (cases "stk(length cs, stkLength P C M pc - 1) = Null")
        case True
        with sem_step Throw s s' c prog wt ST prealloc
        have c':"c' = find_handler_for P NullPointer c"
          by (fastforce elim!: sem.cases
                        dest: find_handler_find_handler_forD
                        simp: hd_stks)
        with Throw v_cs v_cs_f2c_frs' f2c_frs'_eq_c' prealloc
        have v_pred_edge: "valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc).
            (stk(length cs, stkLength P C M pc - 1) = Null \<and>
             find_handler_for P NullPointer ((C,M,pc)#cs) = c') \<or>
            (stk(length cs, stkLength P C M pc - 1) \<noteq> Null \<and>
             find_handler_for P (cname_of h (the_Addr(stk(length cs, stkLength P C M pc - 1))))
               ((C,M,pc)#cs) = c')
          )\<^sub>\<surd>,
        (_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _))"
        (is "valid_edge prog ?e1")
        apply (auto simp del: find_handler_for.simps)
          apply (fastforce intro: JCFG_Throw_Pred)
         apply (fastforce intro: JCFG_Throw_Pred)
        apply (cases "find_handler_for P NullPointer ((C, M, pc) # cs)")
         apply (fastforce intro: JCFG_Throw_Exit)
        by (fastforce intro: JCFG_Throw_Update)
        show ?thesis
        proof (cases c')
          case Nil
          with prog Throw c c' sem_step v_pred_edge
          have v_exec_edge: "valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>([],True)\<rfloor> _),
            \<Up>id,
            (_Exit_))"
            (is "valid_edge prog ?e2")
            by (auto intro: JCFG_Throw_Exit)
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
            by -(simp,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce)
          moreover from Throw jvm_exec c c' s s' stk' loc'
            True Nil wt ST trg_state_correct prealloc
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (cases frs',
                auto dest: find_handler_find_handler_forD
                     simp: JVM_CFG_Interpret.kinds_def split_beta correct_state_def)
          moreover from True s wt c' c have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis by fastforce
        next
          case (Cons a cs')
          then obtain C' M' pc'
            where Cons: "c' = (C',M',pc')#cs'" by (cases a, fastforce)
          with jvm_exec s loc' c True Throw wt ST
          have "loc' = loc"
            by (auto intro!: ext
                       simp: find_handler_loc_fun_eq'
                             not_less_eq_eq nth_Cons' (* nth_locs *) nth_locss)
          from c Cons s s' sem_step jvm_exec prog
          have "stk' = update_stk stk frs'"
            and "(C',M',pc')#cs' = framestack_to_callstack frs'"
            by (auto elim!: sem.cases)
          moreover obtain stk'' loc'' frs'' where "frs' = (stk'',loc'',C',M',pc')#frs''"
            and "cs' = framestack_to_callstack frs''" using calculation
            by (cases frs', fastforce+)
          ultimately
          have stk'':
            "update_stk stk frs' =
            stk((length cs',stkLength P C' M' pc' - Suc 0) := Addr (addr_of_sys_xcpt NullPointer))"
            using c s Cons True prog Throw ST wt trg_state_correct jvm_exec
            by -(rule find_handler_stk_fun_eq' [of P _ h "(C,M,pc)#cs" _ loc h'],
              auto dest!: list_all2_lengthD
                    simp: (* nth_stks *) nth_Cons' split_beta correct_state_def if_split_eq1)
          from \<open>(C',M',pc')#cs' = framestack_to_callstack frs'\<close> Cons
          have "framestack_to_callstack frs' = c'"
            by simp
          with Cons Throw v_cs v_cs_f2c_frs' v_pred_edge
          have v_exec_edge:
            "valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _),
            \<Up>(\<lambda>(h,stk,loc).
            (h,
             stk((length cs',stkLength P C' M' pc' - 1) :=
              if (stk(length cs, stkLength P C M pc - 1) = Null)
                then Addr (addr_of_sys_xcpt NullPointer)
                else (stk(length cs, stkLength P C M pc - 1))),
             loc)
            ),
            (_ c',None _))"
            (is "valid_edge prog ?e2")
            by (auto intro!: JCFG_Throw_Update)
          with v_pred_edge \<open>identifies n c\<close> c c' True prog
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
            by -(rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce+)
          moreover from Cons True Throw jvm_exec c c' s s' \<open>loc' = loc\<close> stk' stk'' wt ST
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto dest: find_handler_heap_eqD simp: JVM_CFG_Interpret.kinds_def)
          moreover from True s wt c c'
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis by fastforce
        qed
      next
        case False
        with sem_step Throw s s' c prog wt ST prealloc
        have c':
          "c' = find_handler_for P
            (cname_of h (the_Addr(stk(length cs, stkLength P C M pc - 1)))) c"
          by (fastforce elim!: sem.cases
                        dest: find_handler_find_handler_forD
                        simp: hd_stks)
        with Throw v_cs v_cs_f2c_frs' f2c_frs'_eq_c'
        have v_pred_edge: "valid_edge prog ((_ (C,M,pc)#cs,None _),
          (\<lambda>(h,stk,loc).
            (stk(length cs, stkLength P C M pc - 1) = Null \<and>
             find_handler_for P NullPointer ((C,M,pc)#cs) = c') \<or>
            (stk(length cs, stkLength P C M pc - 1) \<noteq> Null \<and>
             find_handler_for P (cname_of h (the_Addr(stk(length cs, stkLength P C M pc - 1))))
               ((C,M,pc)#cs) = c')
          )\<^sub>\<surd>,
        (_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _))"
        (is "valid_edge prog ?e1")
        apply (auto simp del: find_handler_for.simps)
          apply (fastforce intro: JCFG_Throw_Pred)
         apply (fastforce intro: JCFG_Throw_Pred)
        apply (cases "find_handler_for P
          (cname_of h (the_Addr(stk(length cs, stkLength P C M pc - 1)))) ((C,M,pc)#cs)")
         apply (fastforce intro: JCFG_Throw_Exit)
        by (fastforce intro: JCFG_Throw_Update)
        show ?thesis
        proof (cases c')
          case Nil
          with prog Throw c c' v_pred_edge
          have v_exec_edge: "valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>([],True)\<rfloor> _),
            \<Up>id,
            (_Exit_))"
            (is "valid_edge prog ?e2")
            by (auto intro!: JCFG_Throw_Exit)
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
            by -(rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce+)
          moreover from Throw jvm_exec c c' s s' False Nil trg_state_correct wt ST
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (cases frs',
                auto dest: find_handler_find_handler_forD
                     simp: JVM_CFG_Interpret.kinds_def correct_state_def)
          moreover from False s wt c' c 
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis by fastforce
        next
          case (Cons a cs')
          then obtain C' M' pc'
            where Cons: "c' = (C',M',pc')#cs'" by (cases a, fastforce)
          with jvm_exec s loc' c Throw wt ST
          have "loc' = loc"
            by (auto intro!: ext
                       simp: find_handler_loc_fun_eq'
                             not_less_eq_eq nth_Cons' (* nth_locs *) nth_locss)
          from c Cons s s' sem_step jvm_exec prog
          have "stk' = update_stk stk frs'"
            and "(C',M',pc')#cs' = framestack_to_callstack frs'"
            by (auto elim!: sem.cases)
          moreover obtain stk'' loc'' frs'' where "frs' = (stk'',loc'',C',M',pc')#frs''"
            and "cs' = framestack_to_callstack frs''" using calculation
            by (cases frs', fastforce+)
          ultimately
          have stk'':
            "update_stk stk frs' =
            stk((length cs',stkLength P C' M' pc' - Suc 0) :=
              Addr (the_Addr (stk((length cs, stkLength P C M pc - Suc 0)))))"
            using c s Cons False prog Throw ST wt trg_state_correct jvm_exec
            by -(rule find_handler_stk_fun_eq' [of P _ h "(C,M,pc)#cs" _ loc h'],
              auto dest!: list_all2_lengthD
                    simp: (* nth_stks *) nth_Cons' split_beta correct_state_def if_split_eq1)
          from applicable False Throw ST sees_M
          have "is_refT ST1"
            by clarsimp
          with state_correct wt ST c False
          have addr_the_addr_stk_eq:
            "Addr(the_Addr(stk(length cs, length STr))) = stk(length cs, length STr)"
            by (cases "stk (length cs, length STr)",
              auto simp: correct_state_def is_refT_def conf_def)
          from \<open>(C',M',pc')#cs' = framestack_to_callstack frs'\<close> Cons
          have "framestack_to_callstack frs' = c'"
            by simp
          with Cons Throw v_cs v_cs_f2c_frs' v_pred_edge
          have v_exec_edge:"valid_edge prog ((_ (C,M,pc)#cs,\<lfloor>(c',True)\<rfloor> _),
            \<Up>(\<lambda>(h,stk,loc).
            (h,
            stk((length cs',stkLength P C' M' pc' - 1) :=
              if (stk(length cs, stkLength P C M pc - 1) = Null)
                then Addr (addr_of_sys_xcpt NullPointer)
                else (stk(length cs, stkLength P C M pc - 1))),
            loc)),
            (_ c',None _))"
            (is "valid_edge prog ?e2")
            by (auto intro!: JCFG_Throw_Update)
          with v_pred_edge \<open>identifies n c\<close> c c' Nil
          have "JVM_CFG_Interpret.path prog n [?e1,?e2] (_ c',None _)"
            by -(rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.Cons_path,
              rule JVM_CFG_Interpret.path.empty_path,
              auto simp: JVM_CFG_Interpret.valid_node_def, fastforce+)
          moreover from Cons False Throw jvm_exec c c' s s' loc' stk'
            addr_the_addr_stk_eq prog wt ST \<open>loc' = loc\<close> stk''
          have "transfers (JVM_CFG_Interpret.kinds [?e1,?e2]) s = s'"
            by (auto dest: find_handler_heap_eqD
                     simp: JVM_CFG_Interpret.kinds_def)
          moreover from False s wt c c'
          have "preds (JVM_CFG_Interpret.kinds [?e1,?e2]) s"
            by (simp add: JVM_CFG_Interpret.kinds_def)
          ultimately show ?thesis by fastforce
        qed
      qed
    qed
  qed
qed


end

