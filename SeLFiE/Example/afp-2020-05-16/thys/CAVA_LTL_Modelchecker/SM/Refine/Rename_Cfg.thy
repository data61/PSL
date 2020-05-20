theory Rename_Cfg
imports "../RefPoint/SM_Cfg"
  Type_System SM_Finite_Reachable Gen_Cfg_Bisim
  "HOL-Library.IArray"
begin

(* TODO: Move *)
lemma set_list_bind[simp]: "set (List.bind m f) = Set.bind (set m) (\<lambda>x. set (f x))"
  by (auto simp: List.bind_def)

lemma rel_mset_of_mapI:
  assumes "\<forall>x\<in>set l. R (f x) (g x)"
  shows "rel_mset R (mset (map f l)) (mset (map g l))"
  using assms
  apply (induction l)
  apply (auto simp: rel_mset_Zero rel_mset_Plus)
  done


(* TODO: Move? *)
lemma finite_max1_elemI:
  assumes "(\<forall>x y. x\<in>S \<and> y\<in>S \<longrightarrow> x=y)"  
  shows "finite S"
proof (cases "S={}")
  case False 
  with assms obtain x where "S={x}" by auto
  thus ?thesis by auto
qed auto


lemma left_unique_finite_sngI: 
  assumes "left_unique R" 
  shows "finite {a. R a b}"
proof (rule finite_subset)
  { 
    fix x y
    assume "x\<in>{a. R a b}" "y\<in>{a. R a b}"
    hence "x=y" using assms
      by (auto dest: left_uniqueD)
  } thus "finite {a. R a b}"
    by (blast intro: finite_max1_elemI)
qed auto   



function approx_reachable_list_aux :: "cmd \<Rightarrow> cmd list" where
  "approx_reachable_list_aux (Assign c x e) = [Assign c x e, Skip]"
| "approx_reachable_list_aux (Assign_local c x e) = [Assign_local c x e, Skip]"
| "approx_reachable_list_aux (Assign_global c x e) = [Assign_global c x e, Skip]"
| "approx_reachable_list_aux (Test e) = [Test e, Skip]"
| "approx_reachable_list_aux (Skip) = [Skip]"
| "approx_reachable_list_aux (Seq c1 c2) = (approx_reachable_list_aux c2) @ (do { c1\<leftarrow>approx_reachable_list_aux c1; [Seq c1 c2] })"
| "approx_reachable_list_aux (Or c1 c2) = (Or c1 c2) # (approx_reachable_list_aux c1 @ approx_reachable_list_aux c2)"
| "approx_reachable_list_aux (Break) = [Break,Invalid]"
| "approx_reachable_list_aux (Continue) = [Continue,Invalid]"
| "approx_reachable_list_aux (Iterate c1 c2) = Skip #
    (do { c1\<leftarrow>approx_reachable_list_aux c1; [Iterate c1 c2] })
  @ (do { c2'\<leftarrow>approx_reachable_list_aux c2; [Iterate c2' c2] })"
| "approx_reachable_list_aux Invalid = [Invalid]"
by pat_completeness auto

termination
  apply (relation "reachable_term_order_aux <*mlex*> measure size")
  apply (metis wf_measure wf_mlex)
  apply (auto simp: mlex_prod_def)
  done

lemma approx_reachable_list_aux_refine: 
  "set (approx_reachable_list_aux c) = approx_reachable c"
  apply (induction c rule: approx_reachable.induct)
  apply (simp_all)
  done

definition "cfg_V0 prog \<equiv> proc_decl.body ` set (program.processes prog)"
definition "cfg_V0_list prog \<equiv> remdups (map proc_decl.body (program.processes prog))"

lemma cfg_V0_list_invar: "distinct (cfg_V0_list prog)"
  unfolding cfg_V0_list_def by auto

lemma cfg_V0_list_refine: "set (cfg_V0_list prog) = cfg_V0 prog"
  unfolding cfg_V0_list_def cfg_V0_def by auto


definition "approx_reachable_list prog \<equiv> 
  remdups (concat (map approx_reachable_list_aux (cfg_V0_list prog)))"

definition "approx_reachable_prog prog \<equiv> \<Union>(approx_reachable`(cfg_V0 prog))"


lemma approx_reachable_list_invar: "distinct (approx_reachable_list prog)"
  unfolding approx_reachable_list_def
  by auto

lemma approx_reachable_list_refine: 
  "set (approx_reachable_list prog) = approx_reachable_prog prog"
  unfolding approx_reachable_list_def approx_reachable_prog_def
  by (auto simp: approx_reachable_list_aux_refine cfg_V0_list_refine)

text \<open>CFG successors\<close>
primrec cfg_succ :: "cmd \<Rightarrow> ((action+brk_ctd) \<times> cmd) set" where
  "cfg_succ (Assign c x e) = {((Inl (AAssign c x e)), Skip)}"
| "cfg_succ (Assign_local c x e) = {((Inl (AAssign_local c x e)), Skip)}"
| "cfg_succ (Assign_global c x e) = {((Inl (AAssign_global c x e)), Skip)}"
| "cfg_succ (Test e) = {((Inl (ATest e)), Skip)}"
| "cfg_succ (Seq c1 c2) =
  ( if c1=Skip then 
      {((Inl ASkip), c2)}
    else
      { (e,if c1'=Skip then c2 else Seq c1' c2) | c1' e.  (e,c1')\<in>cfg_succ c1}
  )"
| "cfg_succ (Or c1 c2) = cfg_succ c1 \<union> cfg_succ c2"
| "cfg_succ (Break) = {(Inr AIBreak, Invalid)}"
| "cfg_succ (Continue) = {(Inr AIContinue, Invalid)}"
| cfg_succ_iterate: 
  "cfg_succ (Iterate c cb) =
  (if c=Skip then {(Inl ASkip, Iterate cb cb)} else {})
  \<union> (
    \<lambda> (Inl e,c') \<Rightarrow> (Inl e, if c'=Skip then Iterate cb cb else Iterate c' cb)
    | (Inr AIBreak,_) \<Rightarrow> (Inl ASkip,Skip)
    | (Inr AIContinue,_) \<Rightarrow> (Inl ASkip, Iterate cb cb)
  )`cfg_succ c"
| "cfg_succ Skip = {}"
| "cfg_succ Invalid = {}"


declare cfg_succ_iterate[simp del]
lemma cfg_succ_iterate'[simp]: "cfg_succ (Iterate c cb) = 
  (if c=Skip then {(Inl ASkip, Iterate cb cb)} else {})
  \<union> { (Inl e, if c'=Skip then Iterate cb cb else Iterate c' cb) | e c'. (Inl e, c') \<in> cfg_succ c }
  \<union> (if \<exists>c'. (Inr AIBreak,c')\<in> cfg_succ c then { (Inl ASkip, Skip)} else {})
  \<union> (if \<exists>c'. (Inr AIContinue,c')\<in> cfg_succ c then { (Inl ASkip, Iterate cb cb)} else {})"
  unfolding cfg_succ_iterate
  apply (rule sym)
  apply (cases "c=Skip")
  apply simp
  apply safe
  apply simp_all
  apply force
  apply (force split: if_split_asm)
  apply (force split: if_split_asm)
  apply (auto split: if_split_asm sum.splits brk_ctd.splits)
  done

lemma cfg_succ_iff_cfg: "(a,c')\<in>cfg_succ c \<longleftrightarrow> cfg c a c'"
  apply rule
  apply (induction c arbitrary: a c')
  apply ((auto intro: cfg.intros split: if_split_asm) [])+
  
  apply (induction rule: cfg.induct)
  apply auto
  done

theorem cfg_succ_correct: "cfg_succ c = {(a,c'). cfg c a c'}"
  using cfg_succ_iff_cfg by auto

lemma cfg_succ_finite[simp, intro!]: "finite (cfg_succ c)"
  apply (induction c)
  using [[simproc add: finite_Collect]]
  apply (simp_all del: cfg_succ_iterate' add: cfg_succ_iterate)
  done
 

primrec cfg_succ_list :: "cmd \<Rightarrow> ((action+brk_ctd) \<times> cmd) list" where
  "cfg_succ_list (Assign ge x e) = [((Inl (AAssign ge x e)), Skip)]"
| "cfg_succ_list (Assign_local ge x e) = [((Inl (AAssign_local ge x e)), Skip)]"
| "cfg_succ_list (Assign_global ge x e) = [((Inl (AAssign_global ge x e)), Skip)]"
| "cfg_succ_list (Test e) = [((Inl (ATest e)), Skip)]"
| "cfg_succ_list (Seq c1 c2) =
    ( if c1=Skip then 
        [((Inl ASkip), c2)] 
      else 
        map (\<lambda>(e,c1'). (e,if c1'=Skip then c2 else Seq c1' c2)) (cfg_succ_list c1)
    )"
| "cfg_succ_list (Or c1 c2) = remdups (cfg_succ_list c1 @ cfg_succ_list c2)"
| "cfg_succ_list (Break) = [(Inr AIBreak, Invalid)]"
| "cfg_succ_list (Continue) = [(Inr AIContinue, Invalid)]"
| cfg_succ_list_iterate: 
  "cfg_succ_list (Iterate c cb) =
  (if c=Skip then [(Inl ASkip, Iterate cb cb)] else [])
  @ remdups (map (
    \<lambda> (Inl e,c') \<Rightarrow> (Inl e, if c'=Skip then Iterate cb cb else Iterate c' cb)
    | (Inr AIBreak,_) \<Rightarrow> (Inl ASkip,Skip)
    | (Inr AIContinue,_) \<Rightarrow> (Inl ASkip, Iterate cb cb)
  ) (cfg_succ_list c))"
| "cfg_succ_list Skip = []"
| "cfg_succ_list Invalid = []"

(* FIXME: Strange, the simplifier should know such lemmas!? *)
lemma Seq_ne_structural[simp]:
  "Seq a b \<noteq> a"
  "Seq a b \<noteq> b"
  "a \<noteq> Seq a b"
  "b \<noteq> Seq a b"
proof -
  show G1: "Seq a b \<noteq> a"
    by (induction a arbitrary: b) auto
  show G2: "Seq a b \<noteq> b"
    by (induction b arbitrary: a) auto
  show "a \<noteq> Seq a b" using G1 by simp
  show "b \<noteq> Seq a b" using G2 by simp
qed

lemma cfg_succ_list_invar: "distinct (cfg_succ_list c)"
  apply (induction c)
  apply (auto simp: distinct_map)
  apply (rule inj_onI)
  apply (auto split: if_split_asm ) []
  done  

lemma cfg_succ_list_refine: "set (cfg_succ_list c) = cfg_succ c"
  apply (induction c)
  apply (simp_all only: cfg_succ.simps cfg_succ_list.simps 
    if_distrib[of set] if_same_eq set_map)
  apply (simp_all)
  apply (auto, force+) []
  done

definition "cfg'_succ_list c \<equiv> map (map_prod projl id) (filter (isl o fst) (cfg_succ_list c))"

lemma cfg'_succ_list_invar: "distinct (cfg'_succ_list c)"
  unfolding cfg'_succ_list_def
  apply (auto simp: distinct_map cfg_succ_list_invar intro!: inj_onI)
  apply (rename_tac a a' foo)
  apply (case_tac a, simp_all)
  done
  
lemma cfg'_succ_list_refine: "set (cfg'_succ_list c) = {(a,c'). cfg' c a c'}"
  unfolding cfg'_succ_list_def
  by (force simp: cfg_succ_list_refine cfg'_def cfg_succ_correct)





definition "index_of l x \<equiv> 
  if \<exists>i<length l. l!i=x then
    Some (THE i. i<length l \<and> l!i=x)
  else None"

lemma index_of_Some_conv:
  assumes "distinct l"
  shows "index_of l x = Some i \<longleftrightarrow> i < length l \<and> l ! i = x"
proof safe
  show "index_of l x = Some i \<Longrightarrow> i < length l"
    using assms unfolding index_of_def distinct_conv_nth
    by (metis (mono_tags, lifting) option.distinct(1) option.inject theI)
  show "index_of l x = Some i \<Longrightarrow> l ! i = x"
    using assms unfolding index_of_def distinct_conv_nth
    by (metis (mono_tags, lifting) option.distinct(1) option.inject theI)
  show "i < length l \<Longrightarrow> x = l ! i \<Longrightarrow> index_of l (l ! i) = Some i"
    using assms unfolding index_of_def distinct_conv_nth by auto
qed

lemma dom_index_of: "dom (index_of l) = set l"
  by (auto simp: index_of_def in_set_conv_nth split: if_split_asm)

lemma index_of_None_conv: "index_of l x = None \<longleftrightarrow> x\<notin>set l"
  using dom_index_of[of l] by auto

lemma index_of_Nil: "index_of [] x = None"
  by (auto simp: index_of_None_conv)

lemma index_of_Cons: "distinct (a#l) 
  \<Longrightarrow> index_of (a#l) x = (if x=a then Some 0 else map_option Suc (index_of l x))"
  apply (auto simp: index_of_Some_conv)
  apply (cases "index_of (a # l) x")
  apply (simp_all only: )
  apply (cases "index_of l x")
  apply (simp_all only: ) [2]
  apply (auto simp: index_of_Some_conv index_of_None_conv) [2]
  apply (cases "index_of l x")
  apply (simp_all only: )
  apply (auto simp: index_of_Some_conv index_of_None_conv 
    in_set_conv_nth nth_Cons nth_eq_iff_index_eq split: nat.splits)
  done

primrec cr_index_of where
  "cr_index_of [] x = None"
| "cr_index_of (a#l) x = (if x=a then Some 0 else map_option Suc (cr_index_of l x))"

lemma cr_index_of_eq: "distinct l \<Longrightarrow> cr_index_of l = index_of l"
  apply (induction l)
  apply (auto simp: index_of_Nil index_of_Cons)
  done

locale sl_graph = asystem +
  fixes rlist and succ_list
  assumes rl_distinct: "distinct rlist"
  assumes rl_reachable: "E\<^sup>* `` V0 \<subseteq> set rlist"
  assumes rl_closed: "\<And>c c'. \<lbrakk>c\<in>set rlist; (c, c') \<in> step\<rbrakk> \<Longrightarrow> c'\<in>set rlist"
  assumes sl_distinct: "c\<in>set rlist \<Longrightarrow> distinct (succ_list c)"
  assumes sl_succs: "set (succ_list c) = {(a,c'). astep c a c'}"
begin
  definition "succs_tab \<equiv> map succ_list rlist"

  lemma astep_succs_tab_conv:
    assumes R: "c\<in>set rlist"
    shows "astep c a c' \<longleftrightarrow> (\<exists>i<length succs_tab. c=rlist!i \<and> (a,c')\<in>set (succs_tab!i))"
  proof -
    from R obtain i where "i<length rlist" and RLI[simp]: "rlist!i=c"
      by (auto simp: in_set_conv_nth)
    hence 1: "i<length succs_tab" "succs_tab!i=succ_list c"
      unfolding succs_tab_def
      by auto

    have AUX: "\<And>j. \<lbrakk>c = rlist!j; j<length succs_tab\<rbrakk> \<Longrightarrow> i=j" 
    proof -
      fix j
      assume "c = rlist!j" "j<length succs_tab"
      hence "rlist!j=rlist!i" "j<length rlist" by (simp_all add: succs_tab_def)
      with nth_eq_iff_index_eq[OF rl_distinct \<open>i<length rlist\<close> \<open>j<length rlist\<close>]  
      show "i=j" by simp
    qed

    from 1 show ?thesis using sl_succs 
      by (auto dest: AUX)
  qed

  lemma succs_tab_invar: "i<length succs_tab \<Longrightarrow> distinct (succs_tab!i)"
    unfolding succs_tab_def 
    using rl_reachable sl_distinct
    by auto

  lemma succs_tab_rl: "\<lbrakk>i<length rlist; (a,c')\<in>set (succs_tab!i)\<rbrakk> 
    \<Longrightarrow> c' \<in> set rlist"
    unfolding succs_tab_def
    apply (simp add: sl_succs)
    apply (rule rl_closed[rotated])
    unfolding step_def
    apply blast
    apply simp
    done

  definition "mapped_succs_tab \<equiv> IArray (
    map (map (\<lambda>(a,c'). (a,the (cr_index_of rlist c')))) succs_tab)"

  lemma [simp]: 
    "IArray.length mapped_succs_tab = length succs_tab"  
    "length succs_tab = length rlist"
    unfolding mapped_succs_tab_def succs_tab_def by auto

  definition "\<gamma> c \<equiv> the (cr_index_of rlist c)"
  definition "\<alpha> i \<equiv> rlist!i"
  definition "succ_impl ci \<equiv> 
    if ci<IArray.length mapped_succs_tab then 
      mapped_succs_tab!!ci
    else []"
  definition "astep_impl c a c' \<equiv> (a,c')\<in>set (succ_impl c)"

  lemma astep_succ_finite[simp, intro!]: 
    "finite {(a,c'). astep_impl c a c'}"
    unfolding astep_impl_def
    by auto

  lemma astep_succ_finite_c[simp, intro!]:
    "finite ({c'. \<exists>a. astep_impl c a c'})"
  proof -
    have "{c'. \<exists>a. astep_impl c a c'} = snd`{(a,c'). astep_impl c a c'}"
      by auto
    also have "finite \<dots>" by auto
    finally show ?thesis .
  qed  

  lemma \<alpha>_inj: "inj_on \<alpha> {0..<length rlist}"
    by (auto intro!: inj_onI simp: \<alpha>_def nth_eq_iff_index_eq[OF rl_distinct])

  lemma \<gamma>_inj: "inj_on \<gamma> (set rlist)"
    using rl_reachable
    apply (auto intro!: inj_onI 
      simp: \<gamma>_def rl_distinct 
      cr_index_of_eq)
    by (metis index_of_None_conv index_of_Some_conv not_None_eq 
      option.sel rl_distinct)
    
  lemma \<gamma>_\<alpha>_inverse: "i<length rlist \<Longrightarrow> \<gamma> (\<alpha> i) = i"  
    unfolding \<alpha>_def \<gamma>_def
    apply (auto simp: cr_index_of_eq[OF rl_distinct])
    apply (cases "index_of rlist (rlist ! i)", simp_all)
    apply (auto simp: index_of_None_conv index_of_Some_conv[OF rl_distinct]
      simp: nth_eq_iff_index_eq[OF rl_distinct])
    done
    
  lemma \<alpha>_\<gamma>_inverse: "c\<in>set rlist \<Longrightarrow> \<alpha> (\<gamma> c) = c"  
    unfolding \<alpha>_def \<gamma>_def
    apply (auto simp: cr_index_of_eq[OF rl_distinct])
    apply (cases "index_of rlist c", simp_all)
    apply (auto simp: index_of_None_conv index_of_Some_conv[OF rl_distinct]
      simp: nth_eq_iff_index_eq[OF rl_distinct])
    done

  lemma \<gamma>_invar: "c\<in>set rlist \<Longrightarrow> \<gamma> c < length rlist"
    apply (auto simp: \<gamma>_def cr_index_of_eq rl_distinct)
    by (metis index_of_None_conv index_of_Some_conv 
      not_None_eq option.sel rl_distinct)

  lemma \<alpha>_invar: "i<length rlist \<Longrightarrow> \<alpha> i \<in> set rlist"
    unfolding \<alpha>_def by simp  

  definition "invar i \<equiv> i<length rlist"    
  definition "rel \<equiv> brp \<alpha> invar"  
  definition "reli \<equiv> brp \<gamma> (\<lambda>x. x\<in>set rlist)"  

  lemma bi_unique_rel: "bi_unique rel"
    apply (intro bi_uniqueI left_uniqueI right_uniqueI)
    by (auto simp: rel_def build_relp_def invar_def
      inj_onD[OF \<alpha>_inj])

  lemma bi_unique_reli: "bi_unique reli"
    apply (intro bi_uniqueI left_uniqueI right_uniqueI)
    by (auto simp: reli_def build_relp_def 
      inj_onD[OF \<gamma>_inj])

  lemma rel_inv_eq_reli: "rel\<inverse>\<inverse> = reli"
    by (auto 
      intro!: ext 
      simp: rel_def reli_def build_relp_def invar_def
      simp: \<gamma>_\<alpha>_inverse \<alpha>_\<gamma>_inverse \<gamma>_invar \<alpha>_invar
      )

  corollary reli_inv_eq_rel: "reli\<inverse>\<inverse> = rel"
    using arg_cong[where f="\<lambda>r. r\<inverse>\<inverse>", OF rel_inv_eq_reli, simplified]
    by simp

  lemma rel_unfold1: "c\<in>set rlist \<Longrightarrow> rel i c \<longleftrightarrow> i = \<gamma> c"  
    unfolding reli_inv_eq_rel[symmetric]
    by (simp add: reli_def build_relp_def)

  lemma is_reachable_criE:
    assumes R: "c \<in> E\<^sup>* `` V0"
    obtains i where "cr_index_of rlist c = Some i"
  proof -
    from R have IS: "c\<in>set rlist" using rl_reachable by auto

    show ?thesis
      using IS
      by (auto 
        simp: cr_index_of_eq[OF rl_distinct] index_of_Some_conv[OF rl_distinct]
        simp: in_set_conv_nth
        intro: that)
  qed

  lemma sim1i: "\<lbrakk> astep c1 a c2; reli c1 c1' \<rbrakk> \<Longrightarrow> \<exists>c2'. reli c2 c2' \<and> astep_impl c1' a c2'"
    apply (auto simp: reli_def build_relp_def)
    apply (rule rl_closed, auto simp: step_def) []
  proof -
    assume R: "c1\<in>set rlist" and S: "astep c1 a c2"
    then obtain i where L: "i<length succs_tab" 
      and C1: "c1=rlist!i" and AC': "(a,c2)\<in>set (succs_tab!i)"
      by (auto simp: astep_succs_tab_conv)

    have [simp]: "i<length rlist" using L by simp  
    note [simp] = L

    from C1 have [simp]: "\<gamma> c1 = i"  
      unfolding \<gamma>_def
      apply (cases "cr_index_of rlist c1")
      apply simp_all
      apply (auto simp: cr_index_of_eq[OF rl_distinct] 
        index_of_Some_conv[OF rl_distinct] index_of_None_conv 
        nth_eq_iff_index_eq[OF rl_distinct])        
      done

    show "astep_impl (\<gamma> c1) a (\<gamma> c2)" 
      using AC'
      apply (auto simp: astep_impl_def succ_impl_def mapped_succs_tab_def)
      apply (auto simp: \<gamma>_def)
      done
  qed

  lemma sim2i: "\<lbrakk> astep_impl c1' a c2'; reli c1 c1' \<rbrakk> \<Longrightarrow> \<exists>c2. reli c2 c2' \<and> astep c1 a c2"
  proof -
    assume "reli c1 c1'"
    hence R: "c1\<in>set rlist" and [simp]: "c1'=\<gamma> c1" 
      by (auto simp: reli_def build_relp_def)
    
    hence [simp]: "\<gamma> c1 < length rlist"
      unfolding \<gamma>_def using rl_reachable
      apply (cases "cr_index_of rlist c1", simp_all)
      apply (auto simp: \<alpha>_def cr_index_of_eq[OF rl_distinct] 
        index_of_None_conv index_of_Some_conv[OF rl_distinct])
      done

    have [simp]: "rlist!\<gamma> c1 = c1"
      unfolding \<alpha>_def[symmetric]
      by (simp add: \<alpha>_\<gamma>_inverse R)

    assume "astep_impl c1' a c2'"
    then obtain c2 where "(a, c2) \<in> set (succs_tab ! \<gamma> c1)" and [simp]: "c2' = \<gamma> c2"
      apply (auto simp: astep_impl_def succ_impl_def mapped_succs_tab_def)
      apply (auto simp: \<gamma>_def)
      done
    with astep_succs_tab_conv[THEN iffD2, OF R, OF exI, of c1' a c2]
      have "astep c1 a c2" by auto
     moreover hence "c2\<in>set rlist" 
      using rl_closed[OF R, of c2] by (auto simp: step_def)
    hence "reli c2 c2'"
      by (auto simp: reli_def build_relp_def)
    ultimately show "\<exists>c2. reli c2 c2' \<and> astep c1 a c2" by blast  
  qed    

  corollary sim1: "\<lbrakk> astep_impl c1' a c2'; rel c1' c1 \<rbrakk> \<Longrightarrow> \<exists>c2. rel c2' c2 \<and> astep c1 a c2"
    using sim2i unfolding reli_inv_eq_rel[symmetric] by simp

  corollary sim2: "\<lbrakk> astep c1 a c2; rel c1' c1 \<rbrakk> \<Longrightarrow> \<exists>c2'. rel c2' c2 \<and> astep_impl c1' a c2'"
    using sim1i unfolding reli_inv_eq_rel[symmetric] by simp


  lemma succ_impl_invar: "distinct (succ_impl ci)"
    unfolding succ_impl_def mapped_succs_tab_def invar_def
    using succs_tab_invar[of ci]
    apply (clarsimp simp: distinct_map)
    apply (fold \<gamma>_def)
    apply (rule inj_onI)
    apply clarsimp (* TODO: This proof is not particular clean *)
    apply (drule (1) succs_tab_rl[rotated])
    apply (drule (1) succs_tab_rl[rotated])
    by (metis \<alpha>_\<gamma>_inverse local.\<alpha>_def)
    
  lemma succ_impl_invarc: "\<lbrakk>invar c; (a,c')\<in>set (succ_impl c)\<rbrakk> \<Longrightarrow> invar c'"
    unfolding succ_impl_def mapped_succs_tab_def invar_def
    apply (clarsimp)
    by (metis \<gamma>_def \<gamma>_invar succs_tab_rl)
        
  lemma astep_impl_invarc: "\<lbrakk>invar c; astep_impl c a c'\<rbrakk> \<Longrightarrow> invar c'"  
    unfolding astep_impl_def
    by (auto intro: succ_impl_invarc)

end

lemma path'_path_conv:
  "li'.cs.path c p c' \<longleftrightarrow> cfg_lts.path c (map Inl p) c'"
  by (induction p arbitrary: c) (auto simp: cfg'_def)

lemma approx_reachable_approx': "li'.cs.reachable c c' \<Longrightarrow> c' \<in> approx_reachable c"
  using approx_reachable_approx[of c c']
  by (auto simp: LTS.reachable_def path'_path_conv)

(* TODO: Move *)
lemma approx_reachable_closed':
  assumes "c\<in>approx_reachable c0"
  assumes "cfg' c a c'"
  shows "c'\<in>approx_reachable c0"
  using assms
  unfolding cfg'_def
  using approx_reachable_closed
  by blast

type_synonym cmdc = nat
type_synonym local_config = "(cmdc, local_state) Gen_Scheduler.local_config"
type_synonym global_config = "(cmdc, local_state, global_state) Gen_Scheduler.global_config"

locale cprog = 
  fixes prog :: program
begin
  sublocale comp: asystem "\<lambda>x. x\<in>cfg_V0 prog" cfg' .

  sublocale comp: sl_graph 
    "\<lambda>x. x\<in>cfg_V0 prog" cfg' 
    "approx_reachable_list prog" "cfg'_succ_list" 
  apply unfold_locales
  apply (simp_all 
    add: approx_reachable_list_invar approx_reachable_list_refine
    add: cfg'_succ_list_invar cfg'_succ_list_refine
    add: approx_reachable_prog_def 
    ) 
  using approx_reachable_approx'
  apply (auto simp: comp.step_path_conv LTS.reachable_def) []

  using approx_reachable_closed' unfolding comp.step_def
  by blast

  abbreviation "cfgc \<equiv> comp.astep_impl"

  definition init_pc :: "proc_decl \<Rightarrow> local_config" where
    "init_pc pd \<equiv> \<lparr>
      local_config.command = comp.\<gamma> (proc_decl.body pd),
      local_config.state = \<lparr>
        local_state.variables = init_valuation (proc_decl.local_vars pd)
      \<rparr>
    \<rparr>"
  
  definition init_gc :: "global_config" where
    "init_gc \<equiv> \<lparr>
      global_config.processes = mset (map init_pc (program.processes prog)),
      global_config.state = \<lparr>
        global_state.variables = init_valuation (program.global_vars prog)
      \<rparr>
    \<rparr>"


  sublocale lih': Gen_Scheduler'_linit 
    cfgc la_en' la_ex' 
    "{init_gc}" global_config.state .

  sublocale hc_bisim: Gen_Cfg_Bisim_Pre comp.rel
    cfgc cfg' la_en' la_ex'
    apply unfold_locales
    apply (blast dest: comp.sim1)
    apply (blast dest: comp.sim2)
    done

  lemma approx_reachable_prog0: "p \<in> set (program.processes prog) \<Longrightarrow>
         body p \<in> approx_reachable_prog prog"  
    unfolding approx_reachable_prog_def
    by (auto simp: cfg_V0_def intro!: bexI)


  sublocale hc_bisim: Gen_Cfg_LBisim comp.rel
    cfgc "{init_gc}" global_config.state
    cfg' "{SM_Semantics.init_gc prog}" global_config.state la_en' la_ex'
    apply unfold_locales
    apply (auto 
      simp: init_gc_def SM_Semantics.init_gc_def 
      simp: init_pc_def SM_Semantics.init_pc_def 
      simp: hc_bisim.rel_gc_def hc_bisim.rel_lc_def
      simp del: mset_map simp: mset_map[symmetric]
      intro!: rel_mset_of_mapI)

    apply (subst comp.rel_unfold1)
    apply (unfold approx_reachable_list_refine)
    apply (simp add: approx_reachable_prog0)
    apply simp

    apply (subst comp.rel_unfold1)
    apply (unfold approx_reachable_list_refine)
    apply (simp add: approx_reachable_prog0)
    apply simp
    done
    
  lemma lih'_accept_eq_li': "lih'.sa.accept = li'.sa.accept prog"  
    by (rule hc_bisim.accept_bisim)


  definition "lc_\<alpha> lc \<equiv> \<lparr>
    local_config.command = comp.\<alpha> (local_config.command lc),
    local_config.state = local_config.state lc
  \<rparr>"
  definition "lc_invar lc \<equiv> comp.invar (local_config.command lc)"

  lemma hc_bisim_rel_lc_brp_conv: "hc_bisim.rel_lc = brp lc_\<alpha> lc_invar"
    apply (intro ext)
    unfolding hc_bisim.rel_lc_def 
    unfolding comp.rel_def lc_\<alpha>_def lc_invar_def build_relp_def
    by auto
    
  definition "gc_\<alpha> gc \<equiv> \<lparr>
    global_config.processes = image_mset lc_\<alpha> (global_config.processes gc),
    global_config.state = global_config.state gc
  \<rparr>"
  definition "gc_invar gc \<equiv> \<forall>lc. lc \<in># global_config.processes gc \<longrightarrow> lc_invar lc"

  lemma hc_bisim_rel_gc_brp_conv: "hc_bisim.rel_gc = brp gc_\<alpha> gc_invar"
    apply (intro ext)
    unfolding hc_bisim.rel_gc_def hc_bisim_rel_lc_brp_conv
    unfolding comp.rel_def gc_\<alpha>_def gc_invar_def
    apply (auto simp: rel_mset_brp)
    apply (auto simp: build_relp_def)
    done

  lemmas bi_unique_rel_gc = hc_bisim.bi_unique_rel_gcI[OF comp.bi_unique_rel] 
  lemmas bi_unique_rel_lc = hc_bisim.bi_unique_rel_lcI[OF comp.bi_unique_rel] 

  lemma run_sim_lih'_li: "lih'.sa.is_run r \<Longrightarrow> li'.sa.is_run prog (gc_\<alpha> o r)"
    apply (rule hc_bisim.s1.br_run_sim)
    unfolding hc_bisim_rel_gc_brp_conv
    by auto

  lemmas lih'_reachable_finite_sim = hc_bisim.s1.reachable_finite_sim

end

context well_typed_prog begin 
  sublocale cprog .

  lemma lih'_accept_eq: "lih'.sa.accept = ref_accept prog"  
    by (simp add: lih'_accept_eq_li' li'.accept_eq)

  lemma lih'_is_run_sim: "lih'.sa.is_run r \<Longrightarrow> ref_is_run prog (Some o gc_\<alpha> o r)"
    apply (drule run_sim_lih'_li)
    unfolding li'.is_run_conv 
    by (auto simp: o_def)

  lemma lih'_finite_reachable: "finite ((g_E lih'.system_automaton)\<^sup>* `` g_V0 lih'.system_automaton)"
    apply (rule lih'_reachable_finite_sim)
    apply (rule li'_finite_reachable)
    unfolding rel_of_pred_def
    apply simp
    apply (rule left_unique_finite_sngI)
    using bi_unique_rel_gc
    apply (simp add: bi_unique_alt_def)
    done
  
end

(* Executable *)
type_synonym comp_info = "(cmd list \<times> (action \<times> nat) list iarray)"
(* TODO: Using a list is slow. Could use a hashmap to map commands to
  their indices *)

definition comp_info_of :: "program \<Rightarrow> comp_info" where
  "comp_info_of prog \<equiv> let
  rlist = approx_reachable_list prog;
  succs_tab = map cfg'_succ_list rlist;
  mapped_succs_tab = IArray (
    map (map (\<lambda>(a,c'). (a,the (cr_index_of rlist c')))) succs_tab)
in
  (rlist,mapped_succs_tab)"

definition ccfg_succ_impl 
  :: "comp_info \<Rightarrow> nat \<Rightarrow> (action \<times> nat) list"
where
  "ccfg_succ_impl cinf c \<equiv> 
    let mst=snd cinf in 
      if c<IArray.length mst then mst!!c else []"

lemma (in cprog) ccfg_succ_impl: 
  "ccfg_succ_impl (comp_info_of prog) = comp.succ_impl"
  apply (intro ext)
  unfolding comp.succ_impl_def comp.mapped_succs_tab_def comp.succs_tab_def
  unfolding ccfg_succ_impl_def comp_info_of_def
  by simp

definition comp_\<gamma>_impl :: "comp_info \<Rightarrow> cmd \<Rightarrow> cmdc" where
  "comp_\<gamma>_impl cinf c \<equiv> the (cr_index_of (fst cinf) c)"

lemma (in cprog) comp_\<gamma>_impl: "comp_\<gamma>_impl (comp_info_of prog) = comp.\<gamma>"
  apply (intro ext)
  unfolding comp.\<gamma>_def
  unfolding comp_\<gamma>_impl_def comp_info_of_def
  by simp
  

export_code comp_info_of ccfg_succ_impl comp_\<gamma>_impl checking SML


end

