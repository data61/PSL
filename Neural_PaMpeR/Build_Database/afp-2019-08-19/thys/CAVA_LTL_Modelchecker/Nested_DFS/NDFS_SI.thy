(**
  Author: Peter Lammich
  Inspired by Rene Neumann's DFS-Framework and Nested DFS formalization
**)
section \<open>Nested DFS using Standard Invariants Approach\<close>
theory NDFS_SI
imports 
  CAVA_Automata.Automata_Impl
  CAVA_Automata.Lasso
  NDFS_SI_Statistics
  CAVA_Base.CAVA_Code_Target
begin

text \<open>
  Implementation of a nested DFS algorithm for accepting cycle detection
  using the refinement framework. The algorithm uses the improvement of 
  Holzmann et al.~\cite{HPY97}, i.e., it reports a cycle if the inner 
  DFS finds a path back to 
  the stack of the outer DFS. Moreover, an early cycle detection optimization is
  implemented~\cite{SE05}, i.e., the outer DFS may already report a cycle on 
  a back-edge involving an accepting node.

  The algorithm returns a witness in case that an accepting cycle is detected.
  
  The design approach to this algorithm is to first establish invariants of a
  generic DFS-Algorithm, which are then used to instantiate the concrete
  nested DFS-algorithm for B\"uchi emptiness check. This formalization can be
  seen as a predecessor of the formalization of 
  Gabow's algorithm~\cite{La14_ITP}, where this technique has been
  further developed.
\<close>

subsection "Tools for DFS Algorithms"

subsubsection "Invariants"
definition "gen_dfs_pre E U S V u0 \<equiv>
  E``U \<subseteq> U   \<comment> \<open>Upper bound is closed under transitions\<close>
  \<and> finite U \<comment> \<open>Upper bound is finite\<close>
  \<and> V \<subseteq> U    \<comment> \<open>Visited set below upper bound\<close>
  \<and> u0 \<in> U   \<comment> \<open>Start node in upper bound\<close>
  \<and> E``(V-S) \<subseteq> V \<comment> \<open>Visited nodes closed under reachability, or on stack\<close>
  \<and> u0\<notin>V     \<comment> \<open>Start node not yet visited\<close>
  \<and> S \<subseteq> V    \<comment> \<open>Stack is visited\<close>
  \<and> (\<forall>v\<in>S. (v,u0)\<in>(E\<inter>S\<times>UNIV)\<^sup>*) \<comment> \<open>\<open>u0\<close> reachable from stack, only over stack\<close>
  "

definition "gen_dfs_var U \<equiv> finite_psupset U"

definition "gen_dfs_fe_inv E U S V0 u0 it V brk \<equiv> 
  (\<not>brk \<longrightarrow> E``(V-S) \<subseteq> V)  \<comment> \<open>Visited set closed under reachability\<close>
  \<and> E``{u0} - it \<subseteq> V     \<comment> \<open>Successors of \<open>u0\<close> visited\<close>
  \<and> V0 \<subseteq> V               \<comment> \<open>Visited set increasing\<close>
  \<and> V \<subseteq> V0 \<union> (E - UNIV\<times>S)\<^sup>* `` (E``{u0} - it - S) \<comment> \<open>All visited nodes reachable\<close>
"

definition "gen_dfs_post E U S V0 u0 V brk \<equiv> 
  (\<not>brk \<longrightarrow> E``(V-S) \<subseteq> V) \<comment> \<open>Visited set closed under reachability\<close>
  \<and> u0 \<in> V               \<comment> \<open>\<open>u0\<close> visited\<close>
  \<and> V0 \<subseteq> V               \<comment> \<open>Visited set increasing\<close>
  \<and> V \<subseteq> V0 \<union> (E - UNIV\<times>S)\<^sup>* `` {u0} \<comment> \<open>All visited nodes reachable\<close>
"


definition "gen_dfs_outer E U V0 it V brk \<equiv>
  V0 \<subseteq> U      \<comment> \<open>Start nodes below upper bound\<close>
  \<and> E``U \<subseteq> U  \<comment> \<open>Upper bound is closed under transitions\<close>
  \<and> finite U \<comment> \<open>Upper bound is finite\<close>
  \<and> V \<subseteq> U    \<comment> \<open>Visited set below upper bound\<close>
  \<and> (\<not>brk \<longrightarrow> E``V \<subseteq> V)  \<comment> \<open>Visited set closed under reachability\<close>
  \<and> (V0 - it \<subseteq> V) \<comment> \<open>Start nodes already iterated over are visited\<close>"


subsubsection "Invariant Preservation"
lemma gen_dfs_outer_initial: 
  assumes "finite (E\<^sup>*``V0)"
  shows "gen_dfs_outer E (E\<^sup>*``V0) V0 V0 {} brk"
  using assms unfolding gen_dfs_outer_def
  by (auto intro: rev_ImageI)

lemma gen_dfs_pre_initial: 
  assumes "gen_dfs_outer E U V0 it V False"
  assumes "v0\<in>U - V"
  shows "gen_dfs_pre E U {} V v0"
  using assms unfolding gen_dfs_pre_def gen_dfs_outer_def
  apply auto
  done

lemma fin_U_imp_wf:
  assumes "finite U"
  shows "wf (gen_dfs_var U)"
  using assms unfolding gen_dfs_var_def by auto


lemma gen_dfs_pre_imp_wf:
  assumes "gen_dfs_pre E U S V u0"
  shows "wf (gen_dfs_var U)"
  using assms unfolding gen_dfs_pre_def gen_dfs_var_def by auto

lemma gen_dfs_pre_imp_fin:
  assumes "gen_dfs_pre E U S V u0"
  shows "finite (E `` {u0})"
  apply (rule finite_subset[where B="U"])
  using assms unfolding gen_dfs_pre_def
  by auto

text \<open>Inserted \<open>u0\<close> on stack and to visited set\<close>
lemma gen_dfs_pre_imp_fe:
  assumes "gen_dfs_pre E U S V u0"
  shows "gen_dfs_fe_inv E U (insert u0 S) (insert u0 V) u0 
    (E``{u0}) (insert u0 V) False"
  using assms unfolding gen_dfs_pre_def gen_dfs_fe_inv_def
  apply auto
  done

lemma gen_dfs_fe_inv_pres_visited:
  assumes "gen_dfs_pre E U S V u0"
  assumes "gen_dfs_fe_inv E U (insert u0 S) (insert u0 V) u0 it V' False"
  assumes "t\<in>it" "it\<subseteq>E``{u0}" "t\<in>V'"
  shows "gen_dfs_fe_inv E U (insert u0 S) (insert u0 V) u0 (it-{t}) V' False"
  using assms unfolding gen_dfs_fe_inv_def
  apply auto
  done

lemma gen_dfs_upper_aux:
  assumes "(x,y)\<in>E'\<^sup>*"
  assumes "(u0,x)\<in>E"
  assumes "u0\<in>U"
  assumes "E'\<subseteq>E"
  assumes "E``U \<subseteq> U"
  shows "y\<in>U"
  using assms
  by induct auto


lemma gen_dfs_fe_inv_imp_var:
  assumes "gen_dfs_pre E U S V u0"
  assumes "gen_dfs_fe_inv E U (insert u0 S) (insert u0 V) u0 it V' False"
  assumes "t\<in>it" "it\<subseteq>E``{u0}" "t\<notin>V'"
  shows "(V',V) \<in> gen_dfs_var U"
  using assms unfolding gen_dfs_fe_inv_def gen_dfs_pre_def gen_dfs_var_def
  apply (clarsimp simp add: finite_psupset_def)
  apply (blast dest: gen_dfs_upper_aux)
  done

lemma gen_dfs_fe_inv_imp_pre:
  assumes "gen_dfs_pre E U S V u0"
  assumes "gen_dfs_fe_inv E U (insert u0 S) (insert u0 V) u0 it V' False"
  assumes "t\<in>it" "it\<subseteq>E``{u0}" "t\<notin>V'"
  shows "gen_dfs_pre E U (insert u0 S) V' t"
  using assms unfolding gen_dfs_fe_inv_def gen_dfs_pre_def
  apply clarsimp
  apply (intro conjI)
  apply (blast dest: gen_dfs_upper_aux)
  apply blast
  apply blast
  apply blast
  apply clarsimp
  apply (rule rtrancl_into_rtrancl[where b=u0])
  apply (auto intro: rev_subsetD[OF _ rtrancl_mono[where r="E \<inter> S \<times> UNIV"]]) []
  apply blast
  done

lemma gen_dfs_post_imp_fe_inv:
  assumes "gen_dfs_pre E U S V u0"
  assumes "gen_dfs_fe_inv E U (insert u0 S) (insert u0 V) u0 it V' False"
  assumes "t\<in>it" "it\<subseteq>E``{u0}" "t\<notin>V'"
  assumes "gen_dfs_post E U (insert u0 S) V' t V'' cyc"
  shows "gen_dfs_fe_inv E U (insert u0 S) (insert u0 V) u0 (it-{t}) V'' cyc"
  using assms unfolding gen_dfs_fe_inv_def gen_dfs_post_def gen_dfs_pre_def
  apply clarsimp
  apply (intro conjI)
  apply blast
  apply blast
  apply blast
  apply (erule order_trans)
  apply simp
  apply (rule conjI)
    apply (erule order_trans[
      where y="insert u0 (V \<union> (E - UNIV \<times> insert u0 S)\<^sup>* 
        `` (E `` {u0} - it - insert u0 S))"])
    apply blast

    apply (cases cyc)
      apply simp
      apply blast

      apply simp
      apply blast
  done

lemma gen_dfs_post_aux:
  assumes 1: "(u0,x)\<in>E"
  assumes 2: "(x,y)\<in>(E - UNIV \<times> insert u0 S)\<^sup>*"
  assumes 3: "S\<subseteq>V" "x\<notin>V"
  shows "(u0, y) \<in> (E - UNIV \<times> S)\<^sup>*"
proof -
  from 1 3 have "(u0,x)\<in>(E - UNIV \<times> S)" by blast
  also have "(x,y)\<in>(E - UNIV \<times> S)\<^sup>*"
    apply (rule_tac rev_subsetD[OF 2 rtrancl_mono])
    by auto
  finally show ?thesis .
qed

lemma gen_dfs_fe_imp_post_brk:
  assumes "gen_dfs_pre E U S V u0"
  assumes "gen_dfs_fe_inv E U (insert u0 S) (insert u0 V) u0 it V' True"
  assumes "it\<subseteq>E``{u0}"
  shows "gen_dfs_post E U S V u0 V' True"
  using assms unfolding gen_dfs_pre_def gen_dfs_fe_inv_def gen_dfs_post_def
  apply clarify
  apply (intro conjI)
  apply simp
  apply simp
  apply simp
  apply clarsimp
  apply (blast intro: gen_dfs_post_aux)
  done


lemma gen_dfs_fe_inv_imp_post:
  assumes "gen_dfs_pre E U S V u0"
  assumes "gen_dfs_fe_inv E U (insert u0 S) (insert u0 V) u0 {} V' cyc"
  assumes "cyc\<longrightarrow>cyc'"
  shows "gen_dfs_post E U S V u0 V' cyc'"
  using assms unfolding gen_dfs_pre_def gen_dfs_fe_inv_def gen_dfs_post_def
  apply clarsimp
  apply (intro conjI)
  apply blast
  apply (auto intro: gen_dfs_post_aux) []
  done

lemma gen_dfs_pre_imp_post_brk:
  assumes "gen_dfs_pre E U S V u0"
  shows "gen_dfs_post E U S V u0 (insert u0 V) True"
  using assms unfolding gen_dfs_pre_def gen_dfs_post_def
  apply auto
  done

subsubsection "Consequences of Postcondition"
lemma gen_dfs_post_imp_reachable: 
  assumes "gen_dfs_pre E U S V0 u0"
  assumes "gen_dfs_post E U S V0 u0 V brk"
  shows "V \<subseteq> V0 \<union> E\<^sup>*``{u0}"
  using assms unfolding gen_dfs_post_def gen_dfs_pre_def
  apply clarsimp
  apply (blast intro: rev_subsetD[OF _ rtrancl_mono])
  done

lemma gen_dfs_post_imp_complete:
  assumes "gen_dfs_pre E U {} V0 u0"
  assumes "gen_dfs_post E U {} V0 u0 V False"
  shows "V0 \<union> E\<^sup>*``{u0} \<subseteq> V"
  using assms unfolding gen_dfs_post_def gen_dfs_pre_def
  apply clarsimp
  apply (blast dest: Image_closed_trancl)
  done

lemma gen_dfs_post_imp_eq:
  assumes "gen_dfs_pre E U {} V0 u0"
  assumes "gen_dfs_post E U {} V0 u0 V False"
  shows "V = V0 \<union> E\<^sup>*``{u0}"
  using gen_dfs_post_imp_reachable[OF assms] gen_dfs_post_imp_complete[OF assms]
  by blast

lemma gen_dfs_post_imp_below_U:
  assumes "gen_dfs_pre E U S V0 u0"
  assumes "gen_dfs_post E U S V0 u0 V False"
  shows "V \<subseteq> U"
  using assms unfolding gen_dfs_pre_def gen_dfs_post_def
  apply clarsimp
  apply (blast intro: rev_subsetD[OF _ rtrancl_mono] dest: Image_closed_trancl)
  done

lemma gen_dfs_post_imp_outer:
  assumes "gen_dfs_outer E U V0 it Vis0 False"
  assumes "gen_dfs_post E U {} Vis0 v0 Vis False"
  assumes "v0 \<in> it" "it \<subseteq> V0" "v0 \<notin> Vis0"
  shows "gen_dfs_outer E U V0 (it - {v0}) Vis False"
proof -
  {
    assume "v0 \<in> it" "it \<subseteq> V0" "V0 \<subseteq> U" "E `` U \<subseteq> U"
    hence "E\<^sup>* `` {v0} \<subseteq> U"
      by (metis (full_types) empty_subsetI insert_subset rtrancl_reachable_induct subset_trans)
  } note AUX=this

  show ?thesis
    using assms
    unfolding gen_dfs_outer_def gen_dfs_post_def
    using AUX
    by auto
qed

lemma gen_dfs_outer_already_vis:
  assumes "v0 \<in> it" "it \<subseteq> V0" "v0 \<in> V" 
  assumes "gen_dfs_outer E U V0 it V False"
  shows "gen_dfs_outer E U V0 (it - {v0}) V False"
  using assms
  unfolding gen_dfs_outer_def
  by auto

subsection "Abstract Algorithm"

subsubsection \<open>Inner (red) DFS\<close>

text \<open>A witness of the red algorithm is a node on the stack and a path
  to this node\<close>
type_synonym 'v red_witness = "('v list \<times> 'v) option"
text \<open>Prepend node to red witness\<close>
fun prep_wit_red :: "'v \<Rightarrow> 'v red_witness \<Rightarrow> 'v red_witness" where
  "prep_wit_red v None = None"
| "prep_wit_red v (Some (p,u)) = Some (v#p,u)"

text \<open>
  Initial witness for node \<open>u\<close> with onstack successor \<open>v\<close> 
\<close>
definition red_init_witness :: "'v \<Rightarrow> 'v \<Rightarrow> 'v red_witness" where
  "red_init_witness u v = Some ([u],v)"

definition red_dfs where
  "red_dfs E onstack V u \<equiv> 
    REC\<^sub>T (\<lambda>D (V,u). do {
      let V=insert u V;
      NDFS_SI_Statistics.vis_red_nres;

      \<comment> \<open>Check whether we have a successor on stack\<close>
      brk \<leftarrow> FOREACH\<^sub>C (E``{u}) (\<lambda>brk. brk=None) 
        (\<lambda>t _. 
          if t\<in>onstack then 
            RETURN (red_init_witness u t) 
          else 
          RETURN None
        )
        None;

      \<comment> \<open>Recurse for successors\<close>
      case brk of
        None \<Rightarrow>
          FOREACH\<^sub>C (E``{u}) (\<lambda>(V,brk). brk=None)
            (\<lambda>t (V,_). 
              if t\<notin>V then do {
                (V,brk) \<leftarrow> D (V,t);
                RETURN (V,prep_wit_red u brk)
              } else RETURN (V,None))
            (V,None)
      | _ \<Rightarrow> RETURN (V,brk)
    }) (V,u)
  "


datatype 'v blue_witness = 
  NO_CYC                    \<comment> \<open>No cycle detected\<close>
| REACH "'v" "'v list"      \<comment> \<open>Path from current start node to node on 
  stack, path contains accepting node.\<close>
(* REACH u p: u is on stack, p is non-empty path from u0 to u, a node 
  in u or p is accepting *)
| CIRC "'v list" "'v list"  \<comment> \<open>@{text "CIRI pr pl"}: Lasso found from 
  current start node.\<close>

text \<open>Prepend node to witness\<close>
primrec prep_wit_blue :: "'v \<Rightarrow> 'v blue_witness \<Rightarrow> 'v blue_witness" where
  "prep_wit_blue u0 NO_CYC = NO_CYC"
| "prep_wit_blue u0 (REACH u p) = (
  if u0=u then
    CIRC [] (u0#p)
  else
    REACH u (u0#p)
  )"
| "prep_wit_blue u0 (CIRC pr pl) = CIRC (u0#pr) pl"

text \<open>Initialize blue witness\<close>
fun init_wit_blue :: "'v \<Rightarrow> 'v red_witness \<Rightarrow> 'v blue_witness" where
  "init_wit_blue u0 None = NO_CYC"
| "init_wit_blue u0 (Some (p,u)) = (
  if u=u0 then
    CIRC [] p
  else REACH u p)"

definition init_wit_blue_early :: "'v \<Rightarrow> 'v \<Rightarrow> 'v blue_witness" 
  where "init_wit_blue_early s t \<equiv> if s=t then CIRC [] [s] else REACH t [s]"

text \<open>Extract result from witness\<close>

term lasso_ext

definition "extract_res cyc 
  \<equiv> (case cyc of 
      CIRC pr pl \<Rightarrow> Some (pr,pl)
     | _ \<Rightarrow> None)"

subsubsection \<open>Outer (Blue) DFS\<close>
definition blue_dfs
  :: "('a,_) b_graph_rec_scheme \<Rightarrow> ('a list \<times> 'a list) option nres" 
  where
  "blue_dfs G \<equiv> do {
    NDFS_SI_Statistics.start_nres;
    (_,_,cyc) \<leftarrow> FOREACHc (g_V0 G) (\<lambda>(_,_,cyc). cyc=NO_CYC) 
      (\<lambda>v0 (blues,reds,_). do {
        if v0 \<notin> blues then do {
          (blues,reds,_,cyc) \<leftarrow> REC\<^sub>T (\<lambda>D (blues,reds,onstack,s). do {
            let blues=insert s blues;
            let onstack=insert s onstack;
            let s_acc = s \<in> bg_F G;
            NDFS_SI_Statistics.vis_blue_nres;
            (blues,reds,onstack,cyc) \<leftarrow> 
            FOREACH\<^sub>C ((g_E G)``{s}) (\<lambda>(_,_,_,cyc). cyc=NO_CYC) 
              (\<lambda>t (blues,reds,onstack,cyc). 
                if t \<in> onstack \<and> (s_acc \<or> t \<in> bg_F G) then (
                  RETURN (blues,reds,onstack, init_wit_blue_early s t)
                ) else if t\<notin>blues then do {
                  (blues,reds,onstack,cyc) \<leftarrow> D (blues,reds,onstack,t);
                  RETURN (blues,reds,onstack,(prep_wit_blue s cyc))
                } else do {
                  NDFS_SI_Statistics.match_blue_nres;
                  RETURN (blues,reds,onstack,cyc)
                })
              (blues,reds,onstack,NO_CYC);

            (reds,cyc) \<leftarrow> 
            if cyc=NO_CYC \<and> s_acc then do {
              (reds,rcyc) \<leftarrow> red_dfs (g_E G) onstack reds s;
              RETURN (reds, init_wit_blue s rcyc)
            } else RETURN (reds,cyc);

            let onstack=onstack - {s};
            RETURN (blues,reds,onstack,cyc)
          }) (blues,reds,{},v0);
          RETURN (blues, reds, cyc)
        } else do {
          RETURN (blues, reds, NO_CYC)
        }
      }) ({},{},NO_CYC);
    NDFS_SI_Statistics.stop_nres;
    RETURN (extract_res cyc)
  }
  "

concrete_definition blue_dfs_fe uses blue_dfs_def 
  is "blue_dfs G \<equiv> do {
    NDFS_SI_Statistics.start_nres;
    (_,_,cyc) \<leftarrow> ?FE;
    NDFS_SI_Statistics.stop_nres;
    RETURN (extract_res cyc)
  }"

concrete_definition blue_dfs_body uses blue_dfs_fe_def
  is "_ \<equiv> FOREACHc (g_V0 G) (\<lambda>(_,_,cyc). cyc=NO_CYC) 
    (\<lambda>v0 (blues,reds,_). do {
      if v0\<notin>blues then do {
        (blues,reds,_,cyc) \<leftarrow> REC\<^sub>T ?B (blues,reds,{},v0);
        RETURN (blues, reds, cyc)
      } else do {RETURN (blues, reds, NO_CYC)}
    }) ({},{},NO_CYC)"

thm blue_dfs_body_def

subsection "Correctness"

text \<open>Additional invariant to be maintained between calls of red dfs\<close>
definition "red_dfs_inv E U reds onstack \<equiv> 
  E``U \<subseteq> U           \<comment> \<open>Upper bound is closed under transitions\<close>
  \<and> finite U         \<comment> \<open>Upper bound is finite\<close>
  \<and> reds \<subseteq> U         \<comment> \<open>Red set below upper bound\<close>
  \<and> E``reds \<subseteq> reds   \<comment> \<open>Red nodes closed under reachability\<close>
  \<and> E``reds \<inter> onstack = {} \<comment> \<open>No red node with edge to stack\<close>
"

lemma red_dfs_inv_initial:
  assumes "finite (E\<^sup>*``V0)"
  shows "red_dfs_inv E (E\<^sup>*``V0) {} {}"
  using assms unfolding red_dfs_inv_def
  apply (auto intro: rev_ImageI)
  done

text \<open>Correctness of the red DFS.\<close>
theorem red_dfs_correct:
  fixes v0 u0 :: 'v
  assumes PRE: 
    "red_dfs_inv E U reds onstack"
    "u0\<in>U"
    "u0\<notin>reds"
  shows "red_dfs E onstack reds u0 
    \<le> SPEC (\<lambda>(reds',cyc). case cyc of
      Some (p,v) \<Rightarrow> v\<in>onstack \<and> p\<noteq>[] \<and> path E u0 p v
    | None \<Rightarrow> 
        red_dfs_inv E U reds' onstack 
        \<and> u0\<in>reds' 
        \<and> reds' \<subseteq> reds \<union> E\<^sup>* `` {u0}
  )"
proof -
  let ?dfs_red = "
    REC\<^sub>T (\<lambda>D (V,u). do {
      let V=insert u V;
      NDFS_SI_Statistics.vis_red_nres;

      \<comment> \<open>Check whether we have a successor on stack\<close>
      brk \<leftarrow> FOREACH\<^sub>C (E``{u}) (\<lambda>brk. brk=None) 
        (\<lambda>t _. if t\<in>onstack then 
            RETURN (red_init_witness u t) 
          else RETURN None) 
        None;

      \<comment> \<open>Recurse for successors\<close>
      case brk of
        None \<Rightarrow>
          FOREACH\<^sub>C (E``{u}) (\<lambda>(V,brk). brk=None)
            (\<lambda>t (V,_). 
              if t\<notin>V then do {
                (V,brk) \<leftarrow> D (V,t);
                RETURN (V,prep_wit_red u brk)
              } else RETURN (V,None))
            (V,None)
      | _ \<Rightarrow> RETURN (V,brk)
    }) (V,u)
"
  let "REC\<^sub>T ?body ?init" = "?dfs_red"

  define pre where "pre = (\<lambda>S (V,u0). gen_dfs_pre E U S V u0 \<and> E``V \<inter> onstack = {})"
  define post where "post = (\<lambda>S (V0,u0) (V,cyc). gen_dfs_post E U S V0 u0 V (cyc\<noteq>None)
    \<and> (case cyc of None \<Rightarrow> E``V \<inter> onstack = {}
      | Some (p,v) \<Rightarrow> v\<in>onstack \<and> p\<noteq>[] \<and> path E u0 p v))
    "

  define fe_inv where "fe_inv = (\<lambda>S V0 u0 it (V,cyc). 
    gen_dfs_fe_inv E U S V0 u0 it V (cyc\<noteq>None)
    \<and> (case cyc of None \<Rightarrow> E``V \<inter> onstack = {}
      | Some (p,v) \<Rightarrow> v\<in>onstack \<and> p\<noteq>[] \<and> path E u0 p v))
    "


  from PRE have GENPRE: "gen_dfs_pre E U {} reds u0"
    unfolding red_dfs_inv_def gen_dfs_pre_def
    by auto
  with PRE have PRE': "pre {} (reds,u0)"
    unfolding pre_def red_dfs_inv_def
    by auto

  have IMP_POST: "SPEC (post {} (reds,u0)) 
    \<le> SPEC (\<lambda>(reds',cyc). case cyc of
      Some (p,v) \<Rightarrow> v\<in>onstack \<and> p\<noteq>[] \<and> path E u0 p v
    | None \<Rightarrow> 
        red_dfs_inv E U reds' onstack 
        \<and> u0\<in>reds' 
        \<and> reds' \<subseteq> reds \<union> E\<^sup>* `` {u0})"
    apply (clarsimp split: option.split)
    apply (intro impI conjI allI)
    apply simp_all
  proof -
    fix reds' p v
    assume "post {} (reds,u0) (reds',Some (p,v))"
    thus "v\<in>onstack" and "p\<noteq>[]" and "path E u0 p v"
      unfolding post_def by auto
  next
    fix reds'
    assume "post {} (reds, u0) (reds', None)"
    hence GPOST: "gen_dfs_post E U {} reds u0 reds' False"
      and NS: "E``reds' \<inter> onstack = {}"
      unfolding post_def by auto

    from GPOST show "u0\<in>reds'" unfolding gen_dfs_post_def by auto

    show "red_dfs_inv E U reds' onstack"
      unfolding red_dfs_inv_def
      apply (intro conjI)
      using GENPRE[unfolded gen_dfs_pre_def]
      apply (simp_all) [2]
      apply (rule gen_dfs_post_imp_below_U[OF GENPRE GPOST])
      using GPOST[unfolded gen_dfs_post_def] apply simp
      apply fact
      done

    from GPOST show "reds' \<subseteq> reds \<union> E\<^sup>* `` {u0}" 
      unfolding gen_dfs_post_def by auto
  qed

  {
    fix \<sigma> S
    assume INV0: "pre S \<sigma>"
    have "REC\<^sub>T ?body \<sigma>
      \<le> SPEC (post S \<sigma>)"

      apply (rule RECT_rule_arb[where 
        pre="pre" and
        V="gen_dfs_var U <*lex*> {}" and
        arb="S"
        ])

      apply refine_mono

      using INV0[unfolded pre_def] apply (auto intro: gen_dfs_pre_imp_wf) []
      
      apply fact

      apply (rename_tac D S u)
      apply (intro refine_vcg)

      (* First foreach loop, checking for onstack-successor*)
      apply (rule_tac I="\<lambda>it cyc. 
        (case cyc of None \<Rightarrow> (E``{b} - it) \<inter> onstack = {}
          | Some (p,v) \<Rightarrow> (v\<in>onstack \<and> p\<noteq>[] \<and> path E b p v))" 
        in FOREACHc_rule)
      apply (auto simp add: pre_def gen_dfs_pre_imp_fin) []
      apply auto []
      apply (auto 
        split: option.split 
        simp: red_init_witness_def intro: path1) []

      apply (intro refine_vcg)

      (* Second foreach loop, iterating over sucessors *)
      apply (rule_tac I="fe_inv (insert b S) (insert b a) b" in
        FOREACHc_rule
      )
      apply (auto simp add: pre_def gen_dfs_pre_imp_fin) []

      apply (auto simp add: pre_def fe_inv_def gen_dfs_pre_imp_fe) []

      apply (intro refine_vcg)

      (* Recursive call *)
      apply (rule order_trans)
      apply (rprems)
      apply (clarsimp simp add: pre_def fe_inv_def)
      apply (rule gen_dfs_fe_inv_imp_pre, assumption+) []
      apply (auto simp add: pre_def fe_inv_def intro: gen_dfs_fe_inv_imp_var) []

      apply (clarsimp simp add: pre_def post_def fe_inv_def
        split: option.split_asm prod.split_asm
        ) []
        apply (blast intro: gen_dfs_post_imp_fe_inv)
        apply (blast intro: gen_dfs_post_imp_fe_inv path_prepend)

      apply (auto simp add: pre_def post_def fe_inv_def 
        intro: gen_dfs_fe_inv_pres_visited) []

      apply (auto simp add: pre_def post_def fe_inv_def
        intro: gen_dfs_fe_inv_imp_post) []

      apply (auto simp add: pre_def post_def fe_inv_def
        intro: gen_dfs_fe_imp_post_brk) []

      apply (auto simp add: pre_def post_def fe_inv_def
        intro: gen_dfs_pre_imp_post_brk) []

      apply (auto simp add: pre_def post_def fe_inv_def
        intro: gen_dfs_pre_imp_post_brk) []

      done
  } note GEN=this

  note GEN[OF PRE']
  also note IMP_POST
  finally show ?thesis
    unfolding red_dfs_def .
qed

text \<open>Main theorem: Correctness of the blue DFS\<close>
theorem blue_dfs_correct:
  fixes G :: "('v,_) b_graph_rec_scheme"
  assumes "b_graph G"
  assumes finitely_reachable: "finite ((g_E G)\<^sup>* `` g_V0 G)"
  shows "blue_dfs G \<le> SPEC (\<lambda>r. 
    case r of None \<Rightarrow> (\<forall>L. \<not>b_graph.is_lasso_prpl G L)
  | Some L \<Rightarrow> b_graph.is_lasso_prpl G L)"
proof -
  interpret b_graph G by fact

  let ?A = "bg_F G"
  let ?E = "g_E G"
  let ?V0 = "g_V0 G"

  let ?U = "?E\<^sup>*``?V0"

  define add_inv where "add_inv = (\<lambda>blues reds onstack. 
    \<not>(\<exists>v\<in>(blues-onstack)\<inter>?A. (v,v)\<in>?E\<^sup>+)  \<comment> \<open>No cycles over finished, accepting states\<close>
    \<and> reds \<subseteq> blues                     \<comment> \<open>Red nodes are also blue\<close>
    \<and> reds \<inter> onstack = {}              \<comment> \<open>No red nodes on stack\<close>
    \<and> red_dfs_inv ?E ?U reds onstack)"

  define cyc_post where "cyc_post = (\<lambda>blues reds onstack u0 cyc. (case cyc of 
      NO_CYC \<Rightarrow> add_inv blues reds onstack
    | REACH u p \<Rightarrow> 
          path ?E u0 p u 
        \<and> u \<in> onstack-{u0} 
        \<and> insert u (set p) \<inter> ?A \<noteq> {}
    | CIRC pr pl \<Rightarrow> \<exists>v. 
          pl\<noteq>[] 
        \<and> path ?E v pl v 
        \<and> path ?E u0 pr v 
        \<and> set pl \<inter> ?A \<noteq> {}
    ))"

  define pre where "pre = (\<lambda>(blues,reds,onstack,u::'v).  
    gen_dfs_pre ?E ?U onstack blues u \<and> add_inv blues reds onstack)"

  define post where "post = (\<lambda>(blues0,reds0::'v set,onstack0,u0) (blues,reds,onstack,cyc). 
    onstack = onstack0
    \<and> gen_dfs_post ?E ?U onstack0 blues0 u0 blues (cyc\<noteq>NO_CYC)
    \<and> cyc_post blues reds onstack u0 cyc)"

  define fe_inv where "fe_inv = (\<lambda>blues0 u0 onstack0 it (blues,reds,onstack,cyc). 
    onstack=onstack0 
    \<and> gen_dfs_fe_inv ?E ?U onstack0 blues0 u0 it blues (cyc\<noteq>NO_CYC)
    \<and> cyc_post blues reds onstack u0 cyc)"

  define outer_inv where "outer_inv = (\<lambda>it (blues,reds,cyc).
    case cyc of 
      NO_CYC \<Rightarrow> 
        add_inv blues reds {}
      \<and> gen_dfs_outer ?E ?U ?V0 it blues False
    | CIRC pr pl \<Rightarrow> \<exists>v0\<in>?V0. \<exists>v. 
        pl\<noteq>[] 
      \<and> path ?E v pl v 
      \<and> path ?E v0 pr v 
      \<and> set pl \<inter> ?A \<noteq> {}
    | _ \<Rightarrow> False)"

  have OUTER_INITIAL: "outer_inv V0 ({}, {}, NO_CYC)"
    unfolding outer_inv_def add_inv_def
    using finitely_reachable
    apply (auto intro: red_dfs_inv_initial gen_dfs_outer_initial)
    done

  {
    fix onstack blues u0 reds
    assume "pre (blues,reds,onstack,u0)"
    hence "fe_inv (insert u0 blues) u0 (insert u0 onstack) (?E``{u0}) 
      (insert u0 blues,reds,insert u0 onstack,NO_CYC)"
      unfolding fe_inv_def add_inv_def cyc_post_def
      apply clarsimp
      apply (intro conjI)
      apply (simp add: pre_def gen_dfs_pre_imp_fe)
      apply (auto simp: pre_def add_inv_def) []
      apply (auto simp: pre_def add_inv_def) []
      apply (auto simp: pre_def add_inv_def gen_dfs_pre_def) []
      apply (auto simp: pre_def add_inv_def) []

      apply (unfold pre_def add_inv_def red_dfs_inv_def gen_dfs_pre_def) []
      apply clarsimp
      apply blast
      done
  } note PRE_IMP_FE = this

  have [simp]: "\<And>u cyc. prep_wit_blue u cyc = NO_CYC \<longleftrightarrow> cyc=NO_CYC"
    by (case_tac cyc) auto

  {
    fix blues0 reds0 onstack0 and u0::'v  and
      blues reds onstack blues' reds' onstack' 
      cyc it t
    assume PRE: "pre (blues0,reds0,onstack0,u0)"
    assume FEI: "fe_inv (insert u0 blues0) u0 (insert u0 onstack0) 
        it (blues,reds,onstack,NO_CYC)"
    assume IT: "t\<in>it" "it\<subseteq>?E``{u0}" "t\<notin>blues"
    assume POST: "post (blues,reds,onstack, t) (blues',reds',onstack',cyc)"
    note [simp del] = path_simps
    have "fe_inv (insert u0 blues0) u0 (insert u0 onstack0) (it-{t}) 
      (blues',reds',onstack',prep_wit_blue u0 cyc)"
      unfolding fe_inv_def
      using PRE FEI IT POST
      unfolding fe_inv_def post_def pre_def
      apply (clarsimp)
      apply (intro allI impI conjI)
      apply (blast intro: gen_dfs_post_imp_fe_inv)
      unfolding cyc_post_def
      apply (auto split: blue_witness.split_asm simp: path_simps)
      done
  } note FE_INV_PRES=this


  {
    fix blues reds onstack u0
    assume "pre (blues,reds,onstack,u0)"
    hence "u0\<in>?E\<^sup>*``?V0"
      unfolding pre_def gen_dfs_pre_def by auto
  } note PRE_IMP_REACH = this

  {
    fix blues0 reds0 onstack0 u0 blues reds onstack 
    assume A: "pre (blues0,reds0,onstack0,u0)"
       "fe_inv (insert u0 blues0) u0 (insert u0 onstack0) 
        {} (blues,reds,onstack,NO_CYC)"
       "u0\<in>?A"
    have "u0\<notin>reds" using A
      unfolding fe_inv_def add_inv_def pre_def cyc_post_def
      apply auto
      done
  } note FE_IMP_RED_PRE = this

  {
    fix blues0 reds0 onstack0 u0 blues reds onstack rcyc reds'
    assume PRE: "pre (blues0,reds0,onstack0,u0)"
    assume FEI: "fe_inv (insert u0 blues0) u0 (insert u0 onstack0) 
        {} (blues,reds,onstack,NO_CYC)"
    assume ACC: "u0\<in>?A" 
    assume SPECR: "case rcyc of
      Some (p,v) \<Rightarrow> v\<in>onstack \<and> p\<noteq>[] \<and> path ?E u0 p v
    | None \<Rightarrow> 
        red_dfs_inv ?E ?U reds' onstack 
        \<and> u0\<in>reds' 
        \<and> reds' \<subseteq> reds \<union> ?E\<^sup>* `` {u0}"
    have "post (blues0,reds0,onstack0,u0) 
      (blues,reds',onstack - {u0},init_wit_blue u0 rcyc)"
      unfolding post_def add_inv_def cyc_post_def
      apply (clarsimp)
      apply (intro conjI)
    proof goal_cases
      from PRE FEI show OS0[symmetric]: "onstack - {u0} = onstack0"
        by (auto simp: pre_def fe_inv_def add_inv_def gen_dfs_pre_def)

      from PRE FEI have "u0\<in>onstack"
        unfolding pre_def gen_dfs_pre_def fe_inv_def gen_dfs_fe_inv_def
        by auto

      from PRE FEI 
      show POST: "gen_dfs_post ?E (?E\<^sup>* `` ?V0) onstack0 blues0 u0 blues 
        (init_wit_blue u0 rcyc \<noteq> NO_CYC)" 
        by (auto simp: pre_def fe_inv_def intro: gen_dfs_fe_inv_imp_post)

      case 3

      from FEI have [simp]: "onstack=insert u0 onstack0" 
        unfolding fe_inv_def by auto
      from FEI have "u0\<in>blues" unfolding fe_inv_def gen_dfs_fe_inv_def by auto

      show ?case
        apply (cases rcyc)
        apply (simp_all add: split_paired_all)
      proof -
        assume [simp]: "rcyc=None"
        show "(\<forall>v\<in>(blues - (onstack0 - {u0})) \<inter> ?A. (v, v) \<notin> ?E\<^sup>+) \<and>
          reds' \<subseteq> blues \<and>
          reds' \<inter> (onstack0 - {u0}) = {} \<and>
          red_dfs_inv ?E (?E\<^sup>* `` ?V0) reds' (onstack0 - {u0})"
        proof (intro conjI)
          from SPECR have RINV: "red_dfs_inv ?E ?U reds' onstack" 
            and "u0\<in>reds'" 
            and REDS'R: "reds' \<subseteq> reds \<union> ?E\<^sup>*``{u0}"
            by auto

          from RINV show 
            RINV': "red_dfs_inv ?E (?E\<^sup>* `` ?V0) reds' (onstack0 - {u0})"
            unfolding red_dfs_inv_def by auto

          from RINV'[unfolded red_dfs_inv_def] have 
            REDS'CL: "?E``reds' \<subseteq> reds'" 
            and DJ': "?E `` reds' \<inter> (onstack0 - {u0}) = {}" by auto

          from RINV[unfolded red_dfs_inv_def] have 
            DJ: "?E `` reds' \<inter> (onstack) = {}" by auto

          show "reds' \<subseteq> blues" 
          proof 
            fix v assume "v\<in>reds'"
            with REDS'R have "v\<in>reds \<or> (u0,v)\<in>?E\<^sup>*" by blast
            thus "v\<in>blues" proof
              assume "v\<in>reds" 
              moreover with FEI have "reds\<subseteq>blues" 
                unfolding fe_inv_def add_inv_def cyc_post_def by auto
              ultimately show ?thesis ..
            next
              from POST[unfolded gen_dfs_post_def OS0] have 
                CL: "?E `` (blues - (onstack0 - {u0})) \<subseteq> blues" and "u0\<in>blues" 
                by auto
              from PRE FEI have "onstack0 \<subseteq> blues"
                unfolding pre_def fe_inv_def gen_dfs_pre_def gen_dfs_fe_inv_def
                by auto

              assume "(u0,v)\<in>?E\<^sup>*"
              thus "v\<in>blues"
              proof (cases rule: rtrancl_last_visit[where S="onstack - {u0}"])
                case no_visit
                thus "v\<in>blues" using \<open>u0\<in>blues\<close> CL 
                  by induct (auto elim: rtranclE)
              next
                case (last_visit_point u)
                then obtain uh where "(u0,uh)\<in>?E\<^sup>*" and "(uh,u)\<in>?E"
                  by (metis tranclD2) 
                with REDS'CL DJ' \<open>u0\<in>reds'\<close> have "uh\<in>reds'" 
                  by (auto dest: Image_closed_trancl)
                with DJ' \<open>(uh,u)\<in>?E\<close> \<open>u \<in> onstack - {u0}\<close> have False 
                  by simp blast
                thus ?thesis ..
              qed
            qed
          qed

          show "\<forall>v\<in>(blues - (onstack0 - {u0})) \<inter> ?A. (v, v) \<notin> ?E\<^sup>+"
          proof 
            fix v
            assume A: "v \<in> (blues - (onstack0 - {u0})) \<inter> ?A"
            show "(v,v)\<notin>?E\<^sup>+" proof (cases "v=u0")
              assume "v\<noteq>u0" 
              with A have "v\<in>(blues - (insert u0 onstack)) \<inter> ?A" by auto
              with FEI show ?thesis 
                unfolding fe_inv_def add_inv_def cyc_post_def by auto
            next
              assume [simp]: "v=u0"
              show ?thesis proof
                assume "(v,v)\<in>?E\<^sup>+"
                then obtain uh where "(u0,uh)\<in>?E\<^sup>*" and "(uh,u0)\<in>?E" 
                  by (auto dest: tranclD2)
                with REDS'CL DJ \<open>u0\<in>reds'\<close> have "uh\<in>reds'" 
                  by (auto dest: Image_closed_trancl)
                with DJ \<open>(uh,u0)\<in>?E\<close> \<open>u0 \<in> onstack\<close> show False by blast
              qed
            qed
          qed

          show "reds' \<inter> (onstack0 - {u0}) = {}" 
          proof (rule ccontr)
            assume "reds' \<inter> (onstack0 - {u0}) \<noteq> {}"
            then obtain v where "v\<in>reds'" and "v\<in>onstack0" and "v\<noteq>u0" by auto
          
            from \<open>v\<in>reds'\<close> REDS'R have "v\<in>reds \<or> (u0,v)\<in>?E\<^sup>*"
              by auto
            thus False proof
              assume "v\<in>reds" 
              with FEI[unfolded fe_inv_def add_inv_def cyc_post_def] 
                \<open>v\<in>onstack0\<close>
              show False by auto
            next
              assume "(u0,v)\<in>?E\<^sup>*"
              with \<open>v\<noteq>u0\<close> obtain uh where "(u0,uh)\<in>?E\<^sup>*" and "(uh,v)\<in>?E"
                by (auto elim: rtranclE)
              with REDS'CL DJ \<open>u0\<in>reds'\<close> have "uh\<in>reds'" 
                by (auto dest: Image_closed_trancl)
              with DJ \<open>(uh,v)\<in>?E\<close> \<open>v \<in> onstack0\<close> show False by simp blast
            qed
          qed
        qed
      next
        fix u p
        assume [simp]: "rcyc = Some (p,u)"
        show "
          (u = u0 \<longrightarrow> p \<noteq> [] \<and> path ?E u0 p u0 \<and> set p \<inter> ?A \<noteq> {}) \<and>
          (u \<noteq> u0 \<longrightarrow> 
              path ?E u0 p u \<and> u \<in> onstack0 \<and> (u \<in> ?A \<or> set p \<inter> ?A \<noteq> {}))"
        proof (intro conjI impI)
          from SPECR \<open>u0\<in>?A\<close> show 
            "u\<noteq>u0 \<Longrightarrow> u\<in>onstack0" 
            "p\<noteq>[]" 
            "path ?E u0 p u" 
            "u=u0 \<Longrightarrow> path ?E u0 p u0"
            "set p \<inter> F \<noteq> {}"
            "u \<in> F \<or> set p \<inter> F \<noteq> {}"
            by (auto simp: neq_Nil_conv path_simps)
        qed
      qed
    qed
  } note RED_IMP_POST = this

  {
    fix blues0 reds0 onstack0 u0 blues reds onstack and cyc :: "'v blue_witness"
    assume PRE: "pre (blues0,reds0,onstack0,u0)"
    and FEI: "fe_inv (insert u0 blues0) u0 (insert u0 onstack0) 
        {} (blues,reds,onstack,NO_CYC)"
    and FC[simp]: "cyc=NO_CYC"
    and NCOND: "u0\<notin>?A"

    from PRE FEI have OS0: "onstack0 = onstack - {u0}" 
      by (auto simp: pre_def fe_inv_def add_inv_def gen_dfs_pre_def) []

    from PRE FEI have "u0\<in>onstack"
      unfolding pre_def gen_dfs_pre_def fe_inv_def gen_dfs_fe_inv_def
      by auto
    with OS0 have OS1: "onstack = insert u0 onstack0" by auto
    
    have "post (blues0,reds0,onstack0,u0) (blues,reds,onstack - {u0},NO_CYC)"
      apply (clarsimp simp: post_def cyc_post_def) []
      apply (intro conjI impI)
      apply (simp add: OS0)
      using PRE FEI apply (auto 
        simp: pre_def fe_inv_def intro: gen_dfs_fe_inv_imp_post) []
      
      using FEI[unfolded fe_inv_def cyc_post_def] unfolding add_inv_def
      apply clarsimp
      apply (intro conjI)
      using NCOND apply auto []
      apply auto []
      apply (clarsimp simp: red_dfs_inv_def, blast) []
      done
  } note NCOND_IMP_POST=this

  {
    fix blues0 reds0 onstack0 u0 blues reds onstack it 
      and cyc :: "'v blue_witness"
    assume PRE: "pre (blues0,reds0,onstack0,u0)"
    and FEI: "fe_inv (insert u0 blues0) u0 (insert u0 onstack0) 
        it (blues,reds,onstack,cyc)"
    and NC: "cyc\<noteq>NO_CYC"
    and IT: "it\<subseteq>?E``{u0}"
    from PRE FEI have OS0: "onstack0 = onstack - {u0}"
      by (auto simp: pre_def fe_inv_def add_inv_def gen_dfs_pre_def) []

    from PRE FEI have "u0\<in>onstack"
      unfolding pre_def gen_dfs_pre_def fe_inv_def gen_dfs_fe_inv_def
      by auto
    with OS0 have OS1: "onstack = insert u0 onstack0" by auto

    have "post (blues0,reds0,onstack0,u0) (blues,reds,onstack - {u0},cyc)"
      apply (clarsimp simp: post_def) []
      apply (intro conjI impI)
      apply (simp add: OS0)
      using PRE FEI IT NC apply (auto 
        simp: pre_def fe_inv_def intro: gen_dfs_fe_imp_post_brk) []
      using FEI[unfolded fe_inv_def] NC 
      unfolding cyc_post_def 
      apply (auto split: blue_witness.split simp: OS1) []
      done
  } note BREAK_IMP_POST = this


  {
    fix blues0 reds0 onstack0 and u0::'v  and
      blues reds onstack cyc it t
    assume PRE: "pre (blues0,reds0,onstack0,u0)"
    assume FEI: "fe_inv (insert u0 blues0) u0 (insert u0 onstack0) 
        it (blues,reds,onstack,NO_CYC)"
    assume IT: "it\<subseteq>?E``{u0}" "t\<in>it"
    assume T_OS: "t \<in> onstack"
    assume U0ACC: "u0\<in>F \<or> t\<in>F"


    from T_OS have TIB: "t \<in> blues" using PRE FEI 
      by (auto simp add: fe_inv_def pre_def gen_dfs_fe_inv_def gen_dfs_pre_def)

    have "fe_inv (insert u0 blues0) u0 (insert u0 onstack0) (it - {t}) 
      (blues,reds,onstack,init_wit_blue_early u0 t)"
      unfolding fe_inv_def
      apply (clarsimp simp: it_step_insert_iff[OF IT])
      apply (intro conjI)

      using PRE FEI apply (simp add: fe_inv_def pre_def)

      (* TODO: This is a generic early-break condition. However, it requires
        t \<in> V. Do we really need such a strict invar in case of break? *)
      using FEI TIB apply (auto simp add: fe_inv_def gen_dfs_fe_inv_def) []

      unfolding cyc_post_def init_wit_blue_early_def
      using IT T_OS U0ACC apply (auto simp: path_simps) []
      done
  } note EARLY_DET_OPT = this


  {
    fix \<sigma>
    assume INV0: "pre \<sigma>"

    have "REC\<^sub>T (blue_dfs_body G) \<sigma> \<le> SPEC (post \<sigma>)"
      apply (intro refine_vcg
        RECT_rule[where pre="pre"
        and V="gen_dfs_var ?U <*lex*> {}"]
      )
      apply (unfold blue_dfs_body_def, refine_mono) []
      apply (blast intro!: fin_U_imp_wf finitely_reachable)
      apply (rule INV0)

      (* Body *)
      apply (simp (no_asm) only: blue_dfs_body_def)
      apply (refine_rcg refine_vcg)


      (* Foreach loop *)
      apply (rule_tac 
        I="fe_inv (insert bb a) bb (insert bb ab)" 
        in FOREACHc_rule')

      apply (auto simp add: pre_def gen_dfs_pre_imp_fin) []

      apply (blast intro: PRE_IMP_FE)

      apply (intro refine_vcg)

      (* Early detection of cycles *)
      apply (blast intro: EARLY_DET_OPT)

      (* Recursive call *)
      apply (rule order_trans)
      apply (rprems)
      apply (clarsimp simp add: pre_def fe_inv_def cyc_post_def)
      apply (rule gen_dfs_fe_inv_imp_pre, assumption+) []
      apply (auto simp add: pre_def fe_inv_def intro: gen_dfs_fe_inv_imp_var) []

      apply (auto intro: FE_INV_PRES) []

      apply (auto simp add: pre_def post_def fe_inv_def 
        intro: gen_dfs_fe_inv_pres_visited) []

      apply (intro refine_vcg)

      (* Nested DFS call *)
      apply (rule order_trans)
      apply (rule red_dfs_correct[where U="?E\<^sup>* `` ?V0"])
      apply (auto simp add: fe_inv_def add_inv_def cyc_post_def) []
      apply (auto intro: PRE_IMP_REACH) []
      apply (auto dest: FE_IMP_RED_PRE) []

      apply (intro refine_vcg)
      apply clarsimp
      apply (rule RED_IMP_POST, assumption+) []

      apply (clarsimp, blast intro: NCOND_IMP_POST) []

      apply (intro refine_vcg)
      apply simp

      apply (clarsimp, blast intro: BREAK_IMP_POST) []
      done
  } note GEN=this

  {
    fix v0 it blues reds
    assume "v0 \<in> it" "it \<subseteq> V0" "v0 \<notin> blues" 
      "outer_inv it (blues, reds, NO_CYC)" 
    hence "pre (blues, reds, {}, v0)"
      unfolding pre_def outer_inv_def
      by (auto intro: gen_dfs_pre_initial)
  } note OUTER_IMP_PRE = this

  {
    fix v0 it blues0 reds0 blues reds onstack cyc
    assume "v0 \<in> it" "it \<subseteq> V0" "v0 \<notin> blues0"
      "outer_inv it (blues0, reds0, NO_CYC)"
      "post (blues0, reds0, {}, v0) (blues, reds, onstack, cyc)"
    hence "outer_inv (it - {v0}) (blues, reds, cyc)"
      unfolding post_def outer_inv_def cyc_post_def
      by (fastforce split: blue_witness.split intro: gen_dfs_post_imp_outer)
  } note POST_IMP_OUTER = this

  {
    fix v0 it blues reds
    assume "v0 \<in> it" "it \<subseteq> V0" "outer_inv it (blues, reds, NO_CYC)" 
      "v0 \<in> blues"
    hence "outer_inv (it - {v0}) (blues, reds, NO_CYC)"
      unfolding outer_inv_def
      by (auto intro: gen_dfs_outer_already_vis)
  } note OUTER_ALREX = this


  {
    fix it blues reds cyc
    assume "outer_inv it (blues, reds, cyc)" "cyc \<noteq> NO_CYC"
    hence "case extract_res cyc of 
        None \<Rightarrow> \<forall>L. \<not> is_lasso_prpl L 
      | Some x \<Rightarrow> is_lasso_prpl x"
      unfolding outer_inv_def extract_res_def is_lasso_prpl_def
        is_lasso_prpl_pre_def
      apply (cases cyc)
      apply auto
      done
  } note IMP_POST_CYC = this

  { fix "pr" pl blues reds
    assume ADD_INV: "add_inv blues reds {}" 
    assume GEN_INV: "gen_dfs_outer E (E\<^sup>* `` V0) V0 {} blues False"
    assume LASSO: "is_lasso_prpl (pr, pl)"
    
    from LASSO[unfolded is_lasso_prpl_def is_lasso_prpl_pre_def] 
    obtain v0 va where
      "v0\<in>V0" "pl\<noteq>[]" and
      PR: "path E v0 pr va" and PL: "path E va pl va" and
      F: "set pl \<inter> F \<noteq> {}" 
      by auto

    from F obtain pl1 vf pl2 where [simp]: "pl=pl1@vf#pl2" and "vf\<in>F" 
      by (fastforce simp: in_set_conv_decomp)

    from PR PL have "path E v0 (pr@pl1) vf" "path E vf (vf#pl2@pl1) vf"
      by (auto simp: path_simps)
    hence "(v0,vf)\<in>E\<^sup>*" and "(vf,vf)\<in>E\<^sup>+" 
      by (auto dest: path_is_rtrancl path_is_trancl)

    from GEN_INV \<open>v0\<in>V0\<close> \<open>(v0,vf)\<in>E\<^sup>*\<close> have "vf\<in>blues" 
      unfolding gen_dfs_outer_def
      apply (clarsimp)
      by (metis Image_closed_trancl rev_ImageI rev_subsetD)

    from ADD_INV[unfolded add_inv_def] \<open>vf\<in>blues\<close> \<open>vf\<in>F\<close> \<open>(vf,vf)\<in>E\<^sup>+\<close> 
    have False by auto
  } note IMP_POST_NOCYC_AUX = this
    
  {
    fix blues reds cyc
    assume "outer_inv {} (blues, reds, cyc)"
    hence "case extract_res cyc of 
        None \<Rightarrow> \<forall>L. \<not> is_lasso_prpl L 
      | Some x \<Rightarrow> is_lasso_prpl x"
      apply (cases cyc)
      apply (simp_all add: IMP_POST_CYC)
      unfolding outer_inv_def extract_res_def
      apply (auto intro: IMP_POST_NOCYC_AUX)
      done
  } note IMP_POST_NOCYC = this


  show ?thesis
    unfolding blue_dfs_fe.refine blue_dfs_body.refine
    apply (refine_rcg 
      FOREACHc_rule[where I=outer_inv]
      refine_vcg
    )

    apply (simp add: finitely_reachable finite_V0)

    apply (rule OUTER_INITIAL)
    
    apply (rule order_trans[OF GEN])
    apply (clarsimp, blast intro: OUTER_IMP_PRE)

    apply (clarsimp, blast intro: POST_IMP_OUTER)

    apply (clarsimp, blast intro: OUTER_ALREX)

    apply (clarsimp, blast intro: IMP_POST_NOCYC)

    apply (clarsimp, blast intro: IMP_POST_CYC)
    done
qed


subsection "Refinement"

subsubsection \<open>Setup for Custom Datatypes\<close>
text \<open>This effort can be automated, but currently, such an automation is
  not yet implemented\<close>
abbreviation "red_wit_rel R \<equiv> \<langle>\<langle>\<langle>R\<rangle>list_rel,R\<rangle>prod_rel\<rangle>option_rel"
abbreviation "i_red_wit I \<equiv> \<langle>\<langle>\<langle>I\<rangle>\<^sub>ii_list,I\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_option"

abbreviation "blue_wit_rel \<equiv> (Id::(_ blue_witness \<times> _) set)"
consts i_blue_wit :: interface

lemmas [autoref_rel_intf] = REL_INTFI[of blue_wit_rel i_blue_wit]

term init_wit_blue_early

lemma [autoref_itype]:
  "NO_CYC ::\<^sub>i i_blue_wit"
  "(=) ::\<^sub>i i_blue_wit \<rightarrow>\<^sub>i i_blue_wit \<rightarrow>\<^sub>i i_bool"
  "init_wit_blue ::\<^sub>i I \<rightarrow>\<^sub>i i_red_wit I \<rightarrow>\<^sub>i i_blue_wit"
  "init_wit_blue_early ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i i_blue_wit"
  "prep_wit_blue ::\<^sub>i I \<rightarrow>\<^sub>i i_blue_wit \<rightarrow>\<^sub>i i_blue_wit"
  "red_init_witness ::\<^sub>i I \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i i_red_wit I"
  "prep_wit_red ::\<^sub>i I \<rightarrow>\<^sub>i i_red_wit I \<rightarrow>\<^sub>i i_red_wit I"
  "extract_res ::\<^sub>i i_blue_wit \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>I\<rangle>\<^sub>ii_list, \<langle>I\<rangle>\<^sub>ii_list\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_option"
  "red_dfs ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i I 
    \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>I\<rangle>\<^sub>ii_set, i_red_wit I\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  "blue_dfs ::\<^sub>i i_bg i_unit I 
    \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>\<langle>I\<rangle>\<^sub>ii_list, \<langle>I\<rangle>\<^sub>ii_list\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_option\<rangle>\<^sub>ii_nres"
  by auto

context begin interpretation autoref_syn .  
lemma [autoref_op_pat]: "NO_CYC \<equiv> OP NO_CYC :::\<^sub>i i_blue_wit" by simp
end

term lasso_rel_ext


lemma autoref_wit[autoref_rules_raw]:
  "(NO_CYC,NO_CYC)\<in>blue_wit_rel"
  "((=), (=)) \<in> blue_wit_rel \<rightarrow> blue_wit_rel \<rightarrow> bool_rel"
  "\<And>R. PREFER_id R 
    \<Longrightarrow> (init_wit_blue, init_wit_blue) \<in> R \<rightarrow> red_wit_rel R \<rightarrow> blue_wit_rel"
  "\<And>R. PREFER_id R 
    \<Longrightarrow> (init_wit_blue_early, init_wit_blue_early) \<in> R \<rightarrow> R \<rightarrow> blue_wit_rel"
  "\<And>R. PREFER_id R 
    \<Longrightarrow> (prep_wit_blue,prep_wit_blue)\<in>R \<rightarrow> blue_wit_rel \<rightarrow> blue_wit_rel"
  "\<And>R. PREFER_id R 
    \<Longrightarrow> (red_init_witness, red_init_witness) \<in> R\<rightarrow>R\<rightarrow>red_wit_rel R"
  "\<And>R. PREFER_id R 
    \<Longrightarrow> (prep_wit_red,prep_wit_red) \<in> R \<rightarrow> red_wit_rel R \<rightarrow> red_wit_rel R"
  "\<And>R. PREFER_id R 
    \<Longrightarrow> (extract_res,extract_res) 
        \<in> blue_wit_rel \<rightarrow> \<langle>\<langle>R\<rangle>list_rel\<times>\<^sub>r\<langle>R\<rangle>list_rel\<rangle>option_rel"
  by (simp_all)

subsubsection \<open>Actual Refinement\<close>

term red_dfs

term "map2set_rel (rbt_map_rel ord)"

term rbt_set_rel

schematic_goal red_dfs_refine_aux: "(?f::?'c, red_dfs::(('a::linorder \<times> _) set\<Rightarrow>_)) \<in> ?R"
  supply [autoref_tyrel] = ty_REL[where 'a="'a set" and R="\<langle>Id\<rangle>dflt_rs_rel"]
  unfolding red_dfs_def[abs_def]
  apply (autoref (trace,keep_goal))
  done
concrete_definition impl_red_dfs uses red_dfs_refine_aux

lemma impl_red_dfs_autoref[autoref_rules]:
  fixes R :: "('a\<times>'a::linorder) set"
  assumes "PREFER_id R"
  shows "(impl_red_dfs, red_dfs) \<in> 
    \<langle>R\<rangle>slg_rel \<rightarrow> \<langle>R\<rangle>dflt_rs_rel \<rightarrow> \<langle>R\<rangle>dflt_rs_rel \<rightarrow> R 
    \<rightarrow> \<langle>\<langle>R\<rangle>dflt_rs_rel \<times>\<^sub>r red_wit_rel R\<rangle>nres_rel"
  using assms impl_red_dfs.refine by simp

thm autoref_itype(1-10)

schematic_goal code_red_dfs_aux:
  shows "RETURN ?c \<le> impl_red_dfs E onstack V u"
  unfolding impl_red_dfs_def
  by (refine_transfer (post) the_resI)
concrete_definition code_red_dfs uses code_red_dfs_aux
prepare_code_thms code_red_dfs_def
declare code_red_dfs.refine[refine_transfer]

export_code code_red_dfs checking SML

schematic_goal red_dfs_hash_refine_aux: "(?f::?'c, red_dfs::(('a::hashable \<times> _) set\<Rightarrow>_)) \<in> ?R"
  supply [autoref_tyrel] = ty_REL[where 'a="'a set" and R="\<langle>Id\<rangle>hs.rel"] 
  unfolding red_dfs_def[abs_def]
  apply (autoref (trace,keep_goal))
  done
concrete_definition impl_red_dfs_hash uses red_dfs_hash_refine_aux

thm impl_red_dfs_hash.refine

lemma impl_red_dfs_hash_autoref[autoref_rules]:
  fixes R :: "('a\<times>'a::hashable) set"
  assumes "PREFER_id R"
  shows "(impl_red_dfs_hash, red_dfs) \<in> 
    \<langle>R\<rangle>slg_rel \<rightarrow> \<langle>R\<rangle>hs.rel \<rightarrow> \<langle>R\<rangle>hs.rel \<rightarrow> R 
    \<rightarrow> \<langle>\<langle>R\<rangle>hs.rel \<times>\<^sub>r red_wit_rel R\<rangle>nres_rel"
  using assms impl_red_dfs_hash.refine by simp

schematic_goal code_red_dfs_hash_aux:
  shows "RETURN ?c \<le> impl_red_dfs_hash E onstack V u"
  unfolding impl_red_dfs_hash_def
  by (refine_transfer (post) the_resI)
concrete_definition code_red_dfs_hash uses code_red_dfs_hash_aux
prepare_code_thms code_red_dfs_hash_def
declare code_red_dfs_hash.refine[refine_transfer]

export_code code_red_dfs_hash checking SML

schematic_goal red_dfs_ahs_refine_aux: "(?f::?'c, red_dfs::(('a::hashable \<times> _) set\<Rightarrow>_)) \<in> ?R"
  supply [autoref_tyrel] = ty_REL[where 'a="'a::hashable set" and R="\<langle>Id\<rangle>ahs.rel"]
  unfolding red_dfs_def[abs_def]
  apply (autoref (trace,keep_goal))
  done
concrete_definition impl_red_dfs_ahs uses red_dfs_ahs_refine_aux

lemma impl_red_dfs_ahs_autoref[autoref_rules]:
  fixes R :: "('a\<times>'a::hashable) set"
  assumes "PREFER_id R"
  shows "(impl_red_dfs_ahs, red_dfs) \<in> 
    \<langle>R\<rangle>slg_rel \<rightarrow> \<langle>R\<rangle>ahs.rel \<rightarrow> \<langle>R\<rangle>ahs.rel \<rightarrow> R 
    \<rightarrow> \<langle>\<langle>R\<rangle>ahs.rel \<times>\<^sub>r red_wit_rel R\<rangle>nres_rel"
  using assms impl_red_dfs_ahs.refine by simp

schematic_goal code_red_dfs_ahs_aux:
  shows "RETURN ?c \<le> impl_red_dfs_ahs E onstack V u"
  unfolding impl_red_dfs_ahs_def
  by (refine_transfer the_resI)
concrete_definition code_red_dfs_ahs uses code_red_dfs_ahs_aux
prepare_code_thms code_red_dfs_ahs_def
declare code_red_dfs_ahs.refine[refine_transfer]

export_code code_red_dfs_ahs checking SML

(*abbreviation "blue_dfs_annot E A u \<equiv> blue_dfs E (A:::\<^sub>r\<langle>Id\<rangle>fun_set_rel) u"*)

schematic_goal blue_dfs_refine_aux: "(?f::?'c, blue_dfs::('a::linorder b_graph_rec\<Rightarrow>_)) \<in> ?R"
  supply [autoref_tyrel] =
    ty_REL[where 'a="'a" and R="Id"]
    ty_REL[where 'a="'a set" and R="\<langle>Id\<rangle>dflt_rs_rel"]
  unfolding blue_dfs_def[abs_def]
  apply (autoref (trace,keep_goal))
  done
concrete_definition impl_blue_dfs uses blue_dfs_refine_aux

thm impl_blue_dfs.refine

lemma impl_blue_dfs_autoref[autoref_rules]:
  fixes R :: "('a \<times> 'a::linorder) set"
  assumes "PREFER_id R"
  shows "(impl_blue_dfs, blue_dfs) 
  \<in> bg_impl_rel_ext unit_rel R 
   \<rightarrow> \<langle>\<langle>\<langle>R\<rangle>list_rel \<times>\<^sub>r \<langle>R\<rangle>list_rel\<rangle>Relators.option_rel\<rangle>nres_rel"
  using assms impl_blue_dfs.refine by simp

schematic_goal code_blue_dfs_aux:
  shows "RETURN ?c \<le> impl_blue_dfs G"
  unfolding impl_blue_dfs_def
  apply (refine_transfer (post) the_resI
    order_trans[OF det_RETURN code_red_dfs.refine])
  done
concrete_definition code_blue_dfs uses code_blue_dfs_aux
prepare_code_thms code_blue_dfs_def
declare code_blue_dfs.refine[refine_transfer]

export_code code_blue_dfs checking SML

schematic_goal blue_dfs_hash_refine_aux: "(?f::?'c, blue_dfs::('a::hashable b_graph_rec\<Rightarrow>_)) \<in> ?R"
  supply [autoref_tyrel] =
    ty_REL[where 'a="'a" and R="Id"]
    ty_REL[where 'a="'a::hashable set" and R="\<langle>Id\<rangle>hs.rel"]
  unfolding blue_dfs_def[abs_def]
  using [[autoref_trace_failed_id]]
  apply (autoref (trace,keep_goal))
  done
concrete_definition impl_blue_dfs_hash uses blue_dfs_hash_refine_aux

lemma impl_blue_dfs_hash_autoref[autoref_rules]:
  fixes R :: "('a \<times> 'a::hashable) set"
  assumes "PREFER_id R"
  shows "(impl_blue_dfs_hash, blue_dfs) \<in> bg_impl_rel_ext unit_rel R 
    \<rightarrow> \<langle>\<langle>\<langle>R\<rangle>list_rel \<times>\<^sub>r \<langle>R\<rangle>list_rel\<rangle>Relators.option_rel\<rangle>nres_rel"
  using assms impl_blue_dfs_hash.refine by simp

schematic_goal code_blue_dfs_hash_aux:
  shows "RETURN ?c \<le> impl_blue_dfs_hash G"
  unfolding impl_blue_dfs_hash_def
  apply (refine_transfer the_resI
    order_trans[OF det_RETURN code_red_dfs_hash.refine])
  done
concrete_definition code_blue_dfs_hash uses code_blue_dfs_hash_aux
prepare_code_thms code_blue_dfs_hash_def
declare code_blue_dfs_hash.refine[refine_transfer]

export_code code_blue_dfs_hash checking SML

schematic_goal blue_dfs_ahs_refine_aux: "(?f::?'c, blue_dfs::('a::hashable b_graph_rec\<Rightarrow>_)) \<in> ?R"
  supply [autoref_tyrel] =
    ty_REL[where 'a="'a" and R="Id"]
    ty_REL[where 'a="'a::hashable set" and R="\<langle>Id\<rangle>ahs.rel"]
  unfolding blue_dfs_def[abs_def]
  apply (autoref (trace,keep_goal))
  done
concrete_definition impl_blue_dfs_ahs uses blue_dfs_ahs_refine_aux

lemma impl_blue_dfs_ahs_autoref[autoref_rules]:
  fixes R :: "('a \<times> 'a::hashable) set"
  assumes "MINOR_PRIO_TAG 5"
  assumes "PREFER_id R"
  shows "(impl_blue_dfs_ahs, blue_dfs) \<in> bg_impl_rel_ext unit_rel R 
    \<rightarrow> \<langle>\<langle>\<langle>R\<rangle>list_rel \<times>\<^sub>r \<langle>R\<rangle>list_rel\<rangle>Relators.option_rel\<rangle>nres_rel"
  using assms impl_blue_dfs_ahs.refine by simp

thm impl_blue_dfs_ahs_def

schematic_goal code_blue_dfs_ahs_aux:
  shows "RETURN ?c \<le> impl_blue_dfs_ahs G"
  unfolding impl_blue_dfs_ahs_def
  apply (refine_transfer the_resI
    order_trans[OF det_RETURN code_red_dfs_ahs.refine])
  done
concrete_definition code_blue_dfs_ahs uses code_blue_dfs_ahs_aux
prepare_code_thms code_blue_dfs_ahs_def
declare code_blue_dfs_ahs.refine[refine_transfer]

export_code code_blue_dfs_ahs checking SML

text \<open>Correctness theorem\<close>
theorem code_blue_dfs_correct:
  assumes G: "b_graph G" "finite ((g_E G)\<^sup>* `` g_V0 G)"
  assumes REL: "(Gi,G)\<in>bg_impl_rel_ext unit_rel Id"
  shows "RETURN (code_blue_dfs Gi) \<le> SPEC (\<lambda>r. 
    case r of None \<Rightarrow> \<forall>prpl. \<not>b_graph.is_lasso_prpl G prpl
  | Some L \<Rightarrow> b_graph.is_lasso_prpl G L)"
proof -
  note code_blue_dfs.refine
  also note impl_blue_dfs.refine[param_fo, OF REL, THEN nres_relD]
  also note blue_dfs_correct[OF G]
  finally show ?thesis by (simp cong: option.case_cong)
qed

theorem code_blue_dfs_correct':
  assumes G: "b_graph G" "finite ((g_E G)\<^sup>* `` g_V0 G)"
  assumes REL: "(Gi,G)\<in>bg_impl_rel_ext unit_rel Id"
  shows "case code_blue_dfs Gi of
      None \<Rightarrow> \<forall>prpl. \<not>b_graph.is_lasso_prpl G prpl
    | Some L \<Rightarrow> b_graph.is_lasso_prpl G L"
  using code_blue_dfs_correct[OF G REL]
  by simp

theorem code_blue_dfs_hash_correct:
  assumes G: "b_graph G" "finite ((g_E G)\<^sup>* `` g_V0 G)"
  assumes REL: "(Gi,G)\<in>bg_impl_rel_ext unit_rel Id"
  shows "RETURN (code_blue_dfs_hash Gi) \<le> SPEC (\<lambda>r.
    case r of None \<Rightarrow> \<forall>prpl. \<not>b_graph.is_lasso_prpl G prpl
  | Some L \<Rightarrow> b_graph.is_lasso_prpl G L)"
proof -
  note code_blue_dfs_hash.refine
  also note impl_blue_dfs_hash.refine[param_fo, OF REL, THEN nres_relD]
  also note blue_dfs_correct[OF G]
  finally show ?thesis by (simp cong: option.case_cong)
qed

theorem code_blue_dfs_hash_correct':
  assumes G: "b_graph G" "finite ((g_E G)\<^sup>* `` g_V0 G)"
  assumes REL: "(Gi,G)\<in>bg_impl_rel_ext unit_rel Id"
  shows "case code_blue_dfs_hash Gi of
      None \<Rightarrow> \<forall>prpl. \<not>b_graph.is_lasso_prpl G prpl
    | Some L \<Rightarrow> b_graph.is_lasso_prpl G L"
  using code_blue_dfs_hash_correct[OF G REL]
  by simp

theorem code_blue_dfs_ahs_correct:
  assumes G: "b_graph G" "finite ((g_E G)\<^sup>* `` g_V0 G)"
  assumes REL: "(Gi,G)\<in>bg_impl_rel_ext unit_rel Id"
  shows "RETURN (code_blue_dfs_ahs Gi) \<le> SPEC (\<lambda>r. 
    case r of None \<Rightarrow> \<forall>prpl. \<not>b_graph.is_lasso_prpl G prpl
  | Some L \<Rightarrow> b_graph.is_lasso_prpl G L)"
proof -
  note code_blue_dfs_ahs.refine
  also note impl_blue_dfs_ahs.refine[param_fo, OF REL, THEN nres_relD]
  also note blue_dfs_correct[OF G]
  finally show ?thesis by (simp cong: option.case_cong)
qed

theorem code_blue_dfs_ahs_correct':
  assumes G: "b_graph G" "finite ((g_E G)\<^sup>* `` g_V0 G)"
  assumes REL: "(Gi,G)\<in>bg_impl_rel_ext unit_rel Id"
  shows "case code_blue_dfs_ahs Gi of
      None \<Rightarrow> \<forall>prpl. \<not>b_graph.is_lasso_prpl G prpl
    | Some L \<Rightarrow> b_graph.is_lasso_prpl G L"
  using code_blue_dfs_ahs_correct[OF G REL]
  by simp

text \<open>Export for benchmarking\<close>

schematic_goal acc_of_list_impl_hash:
  notes [autoref_tyrel] = 
    ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>iam_set_rel"]

  shows "(?f::?'c,\<lambda>l::nat list. 
    let s=(set l):::\<^sub>r\<langle>nat_rel\<rangle>iam_set_rel 
    in (\<lambda>x::nat. x\<in>s)
  ) \<in> ?R"
  apply (autoref (keep_goal))
  done

concrete_definition acc_of_list_impl_hash uses acc_of_list_impl_hash
export_code acc_of_list_impl_hash checking SML

definition "code_blue_dfs_nat 
  \<equiv> code_blue_dfs :: _ \<Rightarrow> (nat list \<times> _) option"
definition "code_blue_dfs_hash_nat 
  \<equiv> code_blue_dfs_hash :: _ \<Rightarrow> (nat list \<times> _) option"
definition "code_blue_dfs_ahs_nat 
  \<equiv> code_blue_dfs_ahs :: _ \<Rightarrow> (nat list \<times> _) option"

definition "succ_of_list_impl_int \<equiv> 
  succ_of_list_impl o map (\<lambda>(u,v). (nat_of_integer u, nat_of_integer v))"

definition "acc_of_list_impl_hash_int \<equiv> 
  acc_of_list_impl_hash o map nat_of_integer"

export_code 
  code_blue_dfs_nat 
  code_blue_dfs_hash_nat
  code_blue_dfs_ahs_nat
  succ_of_list_impl_int
  acc_of_list_impl_hash_int
  nat_of_integer
  integer_of_nat
  lasso_ext
  in SML module_name HPY_new_hash
  file \<open>nested_dfs_hash.sml\<close>

end
