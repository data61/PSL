section \<open>Generic DFS and Refinement\<close>
theory General_DFS_Structure
imports "../../Param_DFS"
begin
text \<open>
  We define the generic structure of DFS algorithms, 
  and use this to define a notion of refinement between DFS algorithms.
\<close>


(*        Generic plot: 
          Define generic DFS-scheme (paramDFS is instance)
          Make basic assumptions on DFS scheme parameters: 
            discovered increasing, new_root_discovered, \<dots>
          Show how to implement scheme by FOREACH/WHILE, etc
          This gives a generic implementation for all things that follow basic DFS scheme

          Then define simplified DFS-variants (using general DFS scheme): 
            With on-stack, without on-stack
          Also refine without on-stack to restriction (?)

          Orthogonal refinements:
            1. Refine algorithmic structure, operations remain the same: i.e. fe_impl, rec_impl, ...
            2. Refine operations, structure remains the same:
                 Special case: Refine operations while keeping parametrization
*)


named_theorems DFS_code_unfold \<open>DFS framework: Unfolding theorems to prepare term for automatic refinement\<close>
(*ML {*
  structure DFS_code_unfold = Named_Thms (
    val name = @{binding DFS_code_unfold}
    val description = "DFS framework: Unfolding theorems to prepare term for automatic refinement"
  )
*}
setup DFS_code_unfold.setup*)

(* Basic setup *)
lemmas [DFS_code_unfold] = 
  REC_annot_def (* TODO: Setup REC_annot for autoref!*)
  GHOST_elim_Let (* TODO: Unfold in autoref. Can we (ab)use autoref_op_pat_def for that *)
  comp_def (* TODO: Setup transfer package to handle this ((RETURN o f) x) *)


subsection \<open>Generic DFS Algorithm\<close>
record ('v,'s) gen_dfs_struct = 
  gds_init :: "'s nres"
  gds_is_break :: "'s \<Rightarrow> bool"
  gds_is_empty_stack :: "'s \<Rightarrow> bool"
  gds_new_root :: "'v \<Rightarrow> 's \<Rightarrow> 's nres"
  gds_get_pending :: "'s \<Rightarrow> ('v \<times> 'v option \<times> 's) nres"
  gds_finish :: "'v \<Rightarrow> 's \<Rightarrow> 's nres"
  gds_is_discovered :: "'v \<Rightarrow> 's \<Rightarrow> bool"
  gds_is_finished :: "'v \<Rightarrow> 's \<Rightarrow> bool"
  gds_back_edge :: "'v \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's nres"
  gds_cross_edge :: "'v \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's nres"
  gds_discover :: "'v \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's nres"


locale gen_dfs_defs =
  fixes gds :: "('v,'s) gen_dfs_struct"
  fixes V0 :: "'v set"
begin

  definition "gen_step s \<equiv> 
    if gds_is_empty_stack gds s then do {
      v0 \<leftarrow> SPEC (\<lambda>v0. v0\<in>V0 \<and> \<not>gds_is_discovered gds v0 s);
      gds_new_root gds v0 s
    } else  do {
        (u,Vs,s) \<leftarrow> gds_get_pending gds s;
        case Vs of 
          None \<Rightarrow> gds_finish gds u s 
        | Some v \<Rightarrow> do {
          if gds_is_discovered gds v s then (
            if gds_is_finished gds v s then
              gds_cross_edge gds u v s
            else
              gds_back_edge gds u v s
          ) else 
            gds_discover gds u v s
        }
      }"

  definition "gen_cond  s 
    \<equiv> (V0 \<subseteq> {v. gds_is_discovered gds v s} \<longrightarrow> \<not>gds_is_empty_stack gds s)
      \<and> \<not>gds_is_break gds s"

  definition "gen_dfs 
    \<equiv> gds_init gds \<bind> WHILE gen_cond gen_step"

  definition "gen_dfsT 
    \<equiv> gds_init gds \<bind> WHILET gen_cond gen_step"

  abbreviation "gen_discovered s \<equiv> {v . gds_is_discovered gds v s}"


  abbreviation "gen_rwof \<equiv> rwof (gds_init gds) gen_cond gen_step"

  definition "pre_new_root v0 s \<equiv> 
    gen_rwof s \<and> gds_is_empty_stack gds s \<and> \<not>gds_is_break gds s 
    \<and> v0\<in>V0 - gen_discovered s"

  definition "pre_get_pending s \<equiv>
    gen_rwof s \<and> \<not>gds_is_empty_stack gds s \<and> \<not>gds_is_break gds s"

  definition "post_get_pending u Vs s0 s \<equiv> pre_get_pending s0 
    \<and> inres (gds_get_pending gds s0) (u,Vs,s)"

  definition "pre_finish u s0 s \<equiv> post_get_pending u None s0 s"  
  definition "pre_cross_edge u v s0 s \<equiv> 
    post_get_pending u (Some v) s0 s \<and> gds_is_discovered gds v s 
    \<and> gds_is_finished gds v s"
  definition "pre_back_edge u v s0 s \<equiv> 
    post_get_pending u (Some v) s0 s \<and> gds_is_discovered gds v s 
      \<and> \<not>gds_is_finished gds v s"
  definition "pre_discover u v s0 s \<equiv> 
    post_get_pending u (Some v) s0 s \<and> \<not>gds_is_discovered gds v s"

  lemmas pre_defs = pre_new_root_def pre_get_pending_def post_get_pending_def
    pre_finish_def pre_cross_edge_def pre_back_edge_def pre_discover_def

  definition "gen_step_assert s \<equiv> 
    if gds_is_empty_stack gds s then do {
      v0 \<leftarrow> SPEC (\<lambda>v0. v0\<in>V0 \<and> \<not>gds_is_discovered gds v0 s);
      ASSERT (pre_new_root v0 s);
      gds_new_root gds v0 s
    } else do {
        ASSERT (pre_get_pending s);
        let s0=GHOST s;
        (u,Vs,s) \<leftarrow> gds_get_pending gds s;
        case Vs of 
          None \<Rightarrow> do {ASSERT (pre_finish u s0 s); gds_finish gds u s}
        | Some v \<Rightarrow> do {
          if gds_is_discovered gds v s then do {
            if gds_is_finished gds v s then do {
              ASSERT (pre_cross_edge u v s0 s);
              gds_cross_edge gds u v s
            } else do {
              ASSERT (pre_back_edge u v s0 s);
              gds_back_edge gds u v s
            }
          } else do {
            ASSERT (pre_discover u v s0 s);
            gds_discover gds u v s
          }
        }
      }"

  definition "gen_dfs_assert 
    \<equiv> gds_init gds \<bind> WHILE gen_cond gen_step_assert"

  definition "gen_dfsT_assert 
    \<equiv> gds_init gds \<bind> WHILET gen_cond gen_step_assert"

  abbreviation "gen_rwof_assert \<equiv> rwof (gds_init gds) gen_cond gen_step_assert"

  lemma gen_step_eq_assert: "\<lbrakk>gen_cond s; gen_rwof s\<rbrakk>
       \<Longrightarrow> gen_step s = gen_step_assert s"
    apply (rule antisym)
    subgoal  
      apply (unfold gen_step_def[abs_def] gen_step_assert_def[abs_def]) []
      apply (unfold GHOST_elim_Let) []
      apply (rule refine_IdD)
      apply refine_rcg  
      apply refine_dref_type
      by simp_all  
    
    subgoal    
      apply (simp (no_asm) only: gen_step_def[abs_def] gen_step_assert_def[abs_def]) []
      apply (unfold GHOST_elim_Let) []
      apply (rule refine_IdD)
      apply (refine_rcg bind_refine')
      apply refine_dref_type
      by (auto simp: pre_defs gen_cond_def) 
    done
        
  lemma gen_dfs_eq_assert: "gen_dfs = gen_dfs_assert"
    unfolding gen_dfs_def gen_dfs_assert_def
    apply (rule antisym)
      
    subgoal  
      apply (unfold gen_step_def[abs_def] gen_step_assert_def[abs_def]) []
      apply (unfold GHOST_elim_Let) []
      apply (rule refine_IdD)
      by (refine_rcg, refine_dref_type, simp_all) []

    subgoal    
      apply (subst (2) WHILE_eq_I_rwof)
      apply (rule refine_IdD)
      apply (refine_rcg, simp_all)

      apply (simp (no_asm) only: gen_step_def[abs_def] gen_step_assert_def[abs_def]) []
      apply (unfold GHOST_elim_Let) []
      apply (rule refine_IdD)
      apply (refine_rcg bind_refine')
      apply refine_dref_type  
      by (auto simp: pre_defs gen_cond_def)
    done

  lemma gen_dfsT_eq_assert: "gen_dfsT = gen_dfsT_assert"
    unfolding gen_dfsT_def gen_dfsT_assert_def
    apply (rule antisym)
    subgoal  
      apply (unfold gen_step_def[abs_def] gen_step_assert_def[abs_def]) []
      apply (unfold GHOST_elim_Let) []
      apply (rule refine_IdD)
      by (refine_rcg, refine_dref_type, simp_all) []

    subgoal  
      apply (subst (2) WHILET_eq_I_rwof)
      apply (rule refine_IdD)
      apply (refine_rcg, simp_all)
  
      apply (simp (no_asm) only: gen_step_def[abs_def] gen_step_assert_def[abs_def]) []
      apply (unfold GHOST_elim_Let) []
      apply (rule refine_IdD)
      apply (refine_rcg bind_refine', refine_dref_type)
      by (auto simp: pre_defs gen_cond_def)
    done


  lemma gen_rwof_eq_assert:
    assumes NF: "nofail gen_dfs"
    shows "gen_rwof = gen_rwof_assert"
    apply (rule ext)
    apply (rule iffI)

    subgoal  
      apply (rule rwof_step_refine)
      apply (fold gen_dfs_assert_def gen_dfs_eq_assert, rule NF)
      apply assumption

      apply (simp (no_asm) only: gen_step_def[abs_def] gen_step_assert_def[abs_def]) []
      apply (unfold GHOST_elim_Let) []
      apply (rule leofI)
      apply (rule refine_IdD)
      by (refine_rcg bind_refine', refine_dref_type,
              auto simp: pre_defs gen_cond_def) []

    subgoal  
      apply (rule rwof_step_refine)
      apply (fold gen_dfs_def, rule NF)
      apply assumption
  
      apply (simp (no_asm) only: gen_step_def[abs_def] gen_step_assert_def[abs_def]) []
      apply (unfold GHOST_elim_Let) []
      apply (rule leofI)
      apply (rule refine_IdD)
      by (refine_rcg bind_refine', refine_dref_type,
              auto simp: pre_defs gen_cond_def) []
    done

  lemma gen_dfs_le_gen_dfsT: "gen_dfs \<le> gen_dfsT" 
    unfolding gen_dfs_def gen_dfsT_def
    apply (rule bind_mono)
    apply simp
    unfolding WHILET_def WHILE_def
    apply (rule WHILEI_le_WHILEIT)
    done


end

locale gen_dfs = gen_dfs_defs gds V0 
  for gds :: "('v,'s) gen_dfs_struct"
  and V0 :: "'v set"

(* Formalize the structure of a parameterized DFS *)

(* Define the operations on the basic state *)
record ('v,'s,'es) gen_basic_dfs_struct = 
  gbs_init :: "'es \<Rightarrow> 's nres"
  gbs_is_empty_stack :: "'s \<Rightarrow> bool"
  gbs_new_root :: "'v \<Rightarrow> 's \<Rightarrow> 's nres"
  gbs_get_pending :: "'s \<Rightarrow> ('v \<times> 'v option \<times> 's) nres"
  gbs_finish :: "'v \<Rightarrow> 's \<Rightarrow> 's nres"
  gbs_is_discovered :: "'v \<Rightarrow> 's \<Rightarrow> bool"
  gbs_is_finished :: "'v \<Rightarrow> 's \<Rightarrow> bool"
  gbs_back_edge :: "'v \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's nres"
  gbs_cross_edge :: "'v \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's nres"
  gbs_discover :: "'v \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 's nres"



locale gen_param_dfs_defs =
  fixes gbs :: "('v,'s,'es) gen_basic_dfs_struct"
  fixes param :: "('v,'s,'es) gen_parameterization"
  fixes upd_ext :: "('es\<Rightarrow>'es) \<Rightarrow> 's \<Rightarrow> 's"
  fixes V0 :: "'v set"
begin

  definition "do_action bf ef s \<equiv> do {
    s \<leftarrow> bf s;
    e \<leftarrow> ef s;
    RETURN (upd_ext (\<lambda>_. e) s)
  }"

  definition "do_init \<equiv> do {
    e \<leftarrow> on_init param;
    gbs_init gbs e
  }"

  definition "do_new_root v0 
    \<equiv> do_action (gbs_new_root gbs v0) (on_new_root param v0)"  

  definition "do_finish u 
    \<equiv> do_action (gbs_finish gbs u) (on_finish param u)"

  definition "do_back_edge u v
    \<equiv> do_action (gbs_back_edge gbs u v) (on_back_edge param u v)"

  definition "do_cross_edge u v
    \<equiv> do_action (gbs_cross_edge gbs u v) (on_cross_edge param u v)"
  
  definition "do_discover u v
    \<equiv> do_action (gbs_discover gbs u v) (on_discover param u v)"

  lemmas do_action_defs[DFS_code_unfold] = 
    do_action_def do_init_def do_new_root_def
    do_finish_def do_back_edge_def do_cross_edge_def do_discover_def

  definition "gds \<equiv> \<lparr>
    gds_init = do_init,
    gds_is_break = is_break param,
    gds_is_empty_stack = gbs_is_empty_stack gbs,
    gds_new_root = do_new_root,
    gds_get_pending = gbs_get_pending gbs,
    gds_finish = do_finish,
    gds_is_discovered = gbs_is_discovered gbs,
    gds_is_finished = gbs_is_finished gbs,
    gds_back_edge = do_back_edge,
    gds_cross_edge = do_cross_edge,
    gds_discover = do_discover
  \<rparr>"

  lemmas gds_simps[simp,DFS_code_unfold] 
    = gen_dfs_struct.simps[mk_record_simp, OF gds_def]

  sublocale gen_dfs_defs gds V0 .
end

locale gen_param_dfs = gen_param_dfs_defs gbs param upd_ext V0
  for gbs :: "('v,'s,'es) gen_basic_dfs_struct"
  and param :: "('v,'s,'es) gen_parameterization"
  and upd_ext :: "('es\<Rightarrow>'es) \<Rightarrow> 's \<Rightarrow> 's"
  and V0 :: "'v set"

context param_DFS_defs begin

  definition "gbs \<equiv> \<lparr>
    gbs_init = RETURN o empty_state,
    gbs_is_empty_stack = is_empty_stack ,
    gbs_new_root = RETURN oo new_root ,
    gbs_get_pending = get_pending ,
    gbs_finish = RETURN oo finish ,
    gbs_is_discovered = is_discovered ,
    gbs_is_finished = is_finished ,
    gbs_back_edge = RETURN ooo back_edge ,
    gbs_cross_edge = RETURN ooo cross_edge ,
    gbs_discover = RETURN ooo discover
  \<rparr>"

  lemmas gbs_simps[simp] = gen_basic_dfs_struct.simps[mk_record_simp, OF gbs_def]

  sublocale gen_dfs: gen_param_dfs_defs gbs param state.more_update V0 .

  lemma gen_cond_simp[simp]: "gen_dfs.gen_cond = cond"
    apply (intro ext)
    unfolding cond_def gen_dfs.gen_cond_def
    by simp

  lemma gen_step_simp[simp]: "gen_dfs.gen_step = step"  
    apply (intro ext)
    unfolding gen_dfs.gen_step_def[abs_def] 
    apply (simp 
      cong: if_cong option.case_cong 
      add: gen_dfs.do_action_defs[abs_def])

    unfolding step_def[abs_def] do_defs get_new_root_def pred_defs
    apply (simp 
      cong: if_cong option.case_cong)
    done

  lemma gen_init_simp[simp]: "gen_dfs.do_init = init"
    unfolding init_def
    apply (simp add: gen_dfs.do_action_defs[abs_def])
    done

  lemma gen_dfs_simp[simp]: "gen_dfs.gen_dfs = it_dfs"
    unfolding it_dfs_def gen_dfs.gen_dfs_def 
    apply (simp)
    done

  lemma gen_dfsT_simp[simp]: "gen_dfs.gen_dfsT = it_dfsT"
    unfolding it_dfsT_def gen_dfs.gen_dfsT_def 
    apply (simp)
    done

end

context param_DFS begin
  sublocale gen_dfs: gen_param_dfs gbs param state.more_update V0 .
end


subsection \<open>Refinement Between DFS Implementations\<close>
(* This locale expresses refinement between two general DFS implementations *)

locale gen_dfs_refine_defs =
  c: gen_dfs_defs gdsi V0i + a: gen_dfs_defs gds V0 
  for gdsi V0i gds V0

locale gen_dfs_refine =
  c: gen_dfs gdsi V0i + a: gen_dfs gds V0 + gen_dfs_refine_defs gdsi V0i gds V0
  for gdsi V0i gds V0 +
  fixes V S
  assumes BIJV[relator_props]: "bijective V"
  assumes V0_param[param]: "(V0i,V0)\<in>\<langle>V\<rangle>set_rel"
  assumes is_discovered_param[param]: (* TODO: Add preconditions for predicate refinement assumption *)
    "(gds_is_discovered gdsi,gds_is_discovered gds)\<in>V\<rightarrow>S\<rightarrow>bool_rel"
  assumes is_finished_param[param]: 
    "(gds_is_finished gdsi,gds_is_finished gds)\<in>V\<rightarrow>S\<rightarrow>bool_rel"
  assumes is_empty_stack_param[param]:
    "(gds_is_empty_stack gdsi,gds_is_empty_stack gds)\<in>S\<rightarrow>bool_rel"
  assumes is_break_param[param]:
    "(gds_is_break gdsi,gds_is_break gds)\<in>S\<rightarrow>bool_rel"
  assumes init_refine[refine]: 
    "gds_init gdsi \<le> \<Down> S (gds_init gds)"
  assumes new_root_refine[refine]: 
    "\<lbrakk>a.pre_new_root v0 s; (v0i,v0)\<in>V; (si,s)\<in>S\<rbrakk> 
      \<Longrightarrow> gds_new_root gdsi v0i si \<le> \<Down> S (gds_new_root gds v0 s)"
  assumes get_pending_refine[refine]:
    "\<lbrakk>a.pre_get_pending s; (si,s)\<in>S\<rbrakk>
      \<Longrightarrow> gds_get_pending gdsi si \<le> \<Down>(V \<times>\<^sub>r \<langle>V\<rangle>option_rel \<times>\<^sub>r S) (gds_get_pending gds s)"
  assumes finish_refine[refine]: 
    "\<lbrakk>a.pre_finish v s0 s; (vi,v)\<in>V; (si,s)\<in>S\<rbrakk> 
      \<Longrightarrow> gds_finish gdsi vi si \<le> \<Down> S (gds_finish gds v s)"
  assumes cross_edge_refine[refine]: 
    "\<lbrakk>a.pre_cross_edge u v s0 s; (ui,u)\<in>V; (vi,v)\<in>V; (si,s)\<in>S\<rbrakk> 
      \<Longrightarrow> gds_cross_edge gdsi ui vi si \<le> \<Down> S (gds_cross_edge gds u v s)"
  assumes back_edge_refine[refine]: 
    "\<lbrakk>a.pre_back_edge u v s0 s; (ui,u)\<in>V; (vi,v)\<in>V; (si,s)\<in>S\<rbrakk> 
      \<Longrightarrow> gds_back_edge gdsi ui vi si \<le> \<Down> S (gds_back_edge gds u v s)"
  assumes discover_refine[refine]: 
    "\<lbrakk>a.pre_discover u v s0 s; (ui,u)\<in>V; (vi,v)\<in>V; (si,s)\<in>S\<rbrakk> 
      \<Longrightarrow> gds_discover gdsi ui vi si \<le> \<Down> S (gds_discover gds u v s)"

begin
  term "gds_is_discovered gdsi"

  (*sublocale bij_rel_param!: bij_rel_param V using BIJV by unfold_locales*)

  lemma select_v0_refine[refine]:
    assumes s_param: "(si,s)\<in>S"
    shows "SPEC (\<lambda>v0. v0 \<in> V0i \<and> \<not> gds_is_discovered gdsi v0 si)
           \<le> \<Down> V (SPEC (\<lambda>v0. v0 \<in> V0 \<and> \<not> gds_is_discovered gds v0 s))"
    apply (rule RES_refine)
    apply (simp add: Bex_def[symmetric], elim conjE)
    apply (drule set_relD1[OF V0_param], elim bexE)
    apply (erule bexI[rotated])
    using is_discovered_param[param_fo, OF _ s_param]
    apply auto
    done

  lemma gen_rwof_refine: 
    assumes NF: "nofail (a.gen_dfs)"
    assumes RW: "c.gen_rwof s"
    obtains s' where "(s,s')\<in>S" and "a.gen_rwof s'"
  proof -
    from NF have NFa: "nofail (a.gen_dfs_assert)"
      unfolding a.gen_dfs_eq_assert .

    have "\<exists>s'. (s, s') \<in> S \<and> a.gen_rwof_assert s'"
      apply (rule rwof_refine[OF RW NFa[unfolded a.gen_dfs_assert_def]])

      apply (rule leofI, rule init_refine)
    
      (* TODO: Proof duplication between this and gen_dfs_refine.
        Hope for better rwof/mgi-theory!
      *)
      unfolding c.gen_cond_def a.gen_cond_def
      apply (rule IdD)
      apply (simp only: subset_Collect_conv)
      apply parametricity 
    
      unfolding c.gen_step_def a.gen_step_assert_def GHOST_elim_Let
      apply (rule leofI)
      apply (refine_rcg IdD)
      apply simp_all
      apply ((rule IdD, parametricity) | (auto) [])+
      done
    thus ?thesis 
      unfolding a.gen_rwof_eq_assert[OF NF, symmetric]
      by (blast intro: that)
  qed

  lemma gen_step_refine[refine]: "(si,s)\<in>S \<Longrightarrow> c.gen_step si \<le> \<Down>S (a.gen_step_assert s)"
    unfolding c.gen_step_def a.gen_step_assert_def GHOST_elim_Let
    apply (refine_rcg IdD)
    apply simp_all
    apply ((rule IdD, parametricity) | (auto) [])+
    done
    


  lemma gen_dfs_refine[refine]: "c.gen_dfs \<le> \<Down>S a.gen_dfs"  
    unfolding c.gen_dfs_def a.gen_dfs_eq_assert[unfolded a.gen_dfs_assert_def]
    apply refine_rcg
    unfolding c.gen_cond_def a.gen_cond_def
    apply (rule IdD)
    apply (simp only: subset_Collect_conv)
    apply parametricity 
    done

  lemma gen_dfsT_refine[refine]: "c.gen_dfsT \<le> \<Down>S a.gen_dfsT"  
    unfolding c.gen_dfsT_def a.gen_dfsT_eq_assert[unfolded a.gen_dfsT_assert_def]
    apply refine_rcg
    unfolding c.gen_cond_def a.gen_cond_def
    apply (rule IdD)
    apply (simp only: subset_Collect_conv)
    apply parametricity 
    done

end


(* Locale that states refinement of basic operations, without making 
  assumptions on parameterization *)
locale gbs_refinement =
  c: gen_param_dfs gbsi parami upd_exti V0i +
  a: gen_param_dfs gbs param upd_ext V0
  for gbsi parami upd_exti V0i gbs param upd_ext V0 +
  fixes V S ES
  assumes BIJV: "bijective V"
  assumes V0_param[param]: "(V0i,V0)\<in>\<langle>V\<rangle>set_rel"

  assumes is_discovered_param[param]: 
    "(gbs_is_discovered gbsi,gbs_is_discovered gbs)\<in>V\<rightarrow>S\<rightarrow>bool_rel"

  assumes is_finished_param[param]: 
    "(gbs_is_finished gbsi,gbs_is_finished gbs)\<in>V\<rightarrow>S\<rightarrow>bool_rel"

  assumes is_empty_stack_param[param]:
    "(gbs_is_empty_stack gbsi,gbs_is_empty_stack gbs)\<in>S\<rightarrow>bool_rel"

  assumes is_break_param[param]:
    "(is_break parami,is_break param)\<in>S\<rightarrow>bool_rel"

  assumes gbs_init_refine[refine]: "(ei, e) \<in> ES \<Longrightarrow> gbs_init gbsi ei \<le> \<Down> S (gbs_init gbs e)"

  assumes gbs_new_root_refine[refine]:
    "\<lbrakk>a.pre_new_root v0 s; (v0i, v0) \<in> V; (si, s) \<in> S\<rbrakk>
       \<Longrightarrow> gbs_new_root gbsi v0i si \<le> \<Down> S (gbs_new_root gbs v0 s)"

  assumes gbs_get_pending_refine[refine]:
    "\<lbrakk>a.pre_get_pending s; (si, s) \<in> S\<rbrakk>
            \<Longrightarrow> gbs_get_pending gbsi si
                \<le> \<Down> (V \<times>\<^sub>r \<langle>V\<rangle>option_rel \<times>\<^sub>r S) (gbs_get_pending gbs s)"

  assumes gbs_finish_refine[refine]:
    "\<lbrakk>a.pre_finish v s0 s; (vi, v) \<in> V; (si, s) \<in> S\<rbrakk>
       \<Longrightarrow> gbs_finish gbsi vi si \<le> \<Down> S (gbs_finish gbs v s)"

  assumes gbs_cross_edge_refine[refine]:
    "\<lbrakk>a.pre_cross_edge u v s0 s; (ui, u) \<in> V; (vi, v) \<in> V; (si, s) \<in> S\<rbrakk>
      \<Longrightarrow> gbs_cross_edge gbsi ui vi si \<le> \<Down> S (gbs_cross_edge gbs u v s)"

  assumes gbs_back_edge_refine[refine]:
    "\<lbrakk>a.pre_back_edge u v s0 s; (ui, u) \<in> V; (vi, v) \<in> V; (si, s) \<in> S\<rbrakk>
      \<Longrightarrow> gbs_back_edge gbsi ui vi si \<le> \<Down> S (gbs_back_edge gbs u v s)"

  assumes gbs_discover_refine[refine]:
    "\<lbrakk>a.pre_discover u v s0 s; (ui, u) \<in> V; (vi, v) \<in> V; (si, s) \<in> S\<rbrakk>
      \<Longrightarrow> gbs_discover gbsi ui vi si \<le> \<Down> S (gbs_discover gbs u v s)"

(* Locale that states refinement of parameterization, without making
  assumptions on basic operations *)
locale param_refinement =
  c: gen_param_dfs gbsi parami upd_exti V0i +
  a: gen_param_dfs gbs param upd_ext V0
  for gbsi parami upd_exti V0i gbs param upd_ext V0 +
  fixes V S ES
  assumes upd_ext_param[param]: "(upd_exti, upd_ext)\<in>(ES \<rightarrow> ES) \<rightarrow> S \<rightarrow> S"

  assumes on_init_refine[refine]: "on_init parami \<le> \<Down> ES (on_init param)"

  assumes is_break_param[param]: 
    "(is_break parami, is_break param) \<in> S \<rightarrow> bool_rel"

  assumes on_new_root_refine[refine]:
    "\<lbrakk>a.pre_new_root v0 s; (v0i, v0) \<in> V; (si, s) \<in> S;
        (si', s') \<in> S; nf_inres (gbs_new_root gbs v0 s) s'\<rbrakk>
       \<Longrightarrow> on_new_root parami v0i si' \<le> \<Down> ES (on_new_root param v0 s')"

  assumes on_finish_refine[refine]:
    "\<lbrakk>a.pre_finish v s0 s; (vi, v) \<in> V; (si, s) \<in> S; (si', s') \<in> S;
        nf_inres (gbs_finish gbs v s) s'\<rbrakk>
       \<Longrightarrow> on_finish parami vi si' \<le> \<Down> ES (on_finish param v s')"

  assumes on_cross_edge_refine[refine]:
    "\<lbrakk>a.pre_cross_edge u v s0 s; (ui, u) \<in> V; (vi, v) \<in> V; (si, s) \<in> S;
        (si', s') \<in> S; nf_inres (gbs_cross_edge gbs u v s) s'\<rbrakk>
       \<Longrightarrow> on_cross_edge parami ui vi si' \<le> \<Down> ES (on_cross_edge param u v s')"

  assumes on_back_edge_refine[refine]:
    "\<lbrakk>a.pre_back_edge u v s0 s; (ui, u) \<in> V; (vi, v) \<in> V; (si, s) \<in> S;
        (si', s') \<in> S; nf_inres (gbs_back_edge gbs u v s) s'\<rbrakk>
       \<Longrightarrow> on_back_edge parami ui vi si' \<le> \<Down> ES (on_back_edge param u v s')"

  assumes on_discover_refine[refine]:
    "\<lbrakk>a.pre_discover u v s0 s; (ui, u) \<in> V; (vi, v) \<in> V; (si, s) \<in> S;
        (si', s') \<in> S; nf_inres (gbs_discover gbs u v s) s'\<rbrakk>
       \<Longrightarrow> on_discover parami ui vi si' \<le> \<Down> ES (on_discover param u v s')"


locale gen_param_dfs_refine_defs =
  c: gen_param_dfs_defs gbsi parami upd_exti V0i +
  a: gen_param_dfs_defs gbs param upd_ext V0
  for gbsi parami upd_exti V0i gbs param upd_ext V0
begin
  sublocale gen_dfs_refine_defs c.gds V0i a.gds V0 .
end

locale gen_param_dfs_refine =
  gbs_refinement where V=V and S=S and ES=ES 
+ param_refinement where V=V and S=S and ES=ES
+ gen_param_dfs_refine_defs
  for V :: "('vi\<times>'v) set" and S:: "('si\<times>'s) set" and ES :: "('esi\<times>'es) set"
begin

  sublocale gen_dfs_refine c.gds V0i a.gds V0 V S
    apply unfold_locales
    apply (simp_all add: BIJV V0_param a.do_action_defs c.do_action_defs)
    apply (parametricity+) [4]
    apply refine_rcg
    apply (refine_rcg bind_refine_abs', assumption+, parametricity) []
    apply refine_rcg
    apply (refine_rcg bind_refine_abs', assumption+, parametricity) []
    apply (refine_rcg bind_refine_abs', assumption+, parametricity) []
    apply (refine_rcg bind_refine_abs', assumption+, parametricity) []
    apply (refine_rcg bind_refine_abs', assumption+, parametricity) []
    done

end

end


