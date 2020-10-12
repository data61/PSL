section \<open>\isaheader{Nested DFS (HPY improvement)}\<close>
theory Nested_DFS
imports 
  Collections.Refine_Dflt
  Succ_Graph
  Collections.Code_Target_ICF
  CAVA_Automata.Digraph_Basic
begin

text \<open>
  Implementation of a nested DFS algorithm for accepting cycle detection
  using the refinement framework. The algorithm uses the improvement of 
  [HPY96], i.e., it reports a cycle if the inner DFS finds a path back to 
  the stack of the outer DFS.

  The algorithm returns a witness in case that an accepting cycle is detected.
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

subsubsection "Invariant Preservation"
lemma gen_dfs_pre_initial: 
  assumes "finite (E\<^sup>*``{v0})"
  assumes "v0\<in>U"
  shows "gen_dfs_pre E (E\<^sup>*``{v0}) {} {} v0"
  using assms unfolding gen_dfs_pre_def 
  apply auto
  done

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

      \<comment> \<open>Check whether we have a successor on stack\<close>
      brk \<leftarrow> FOREACH\<^sub>C (E``{u}) (\<lambda>brk. brk=None) 
        (\<lambda>t _. if t\<in>onstack then RETURN (red_init_witness u t) else RETURN None)
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

text \<open>
  A witness of the blue DFS may be in two different phases, the \<open>REACH\<close>
  phase is before the node on the stack has actually been popped, and the
  \<open>CIRC\<close> phase is after the node on the stack has been popped.

  \<open>REACH v p u p'\<close>: \begin{description}
  \item[\<open>v\<close>] accepting node 
  \item[\<open>p\<close>] path from \<open>v\<close> to \<open>u\<close>
  \item[\<open>u\<close>] node on stack
  \item[\<open>p'\<close>] path from current node to \<open>v\<close>
  \end{description}

  \<open>CIRC v pc pr\<close>: \begin{description}
  \item[\<open>v\<close>] accepting node 
  \item[\<open>pc\<close>] path from \<open>v\<close> to \<open>v\<close>
  \item[\<open>pr\<close>] path from current node to \<open>v\<close>
  \end{description}
\<close>
datatype 'v blue_witness = 
  NO_CYC
| REACH "'v" "'v list" "'v" "'v list"
| CIRC "'v" "'v list" "'v list"

text \<open>Prepend node to witness\<close>
primrec prep_wit_blue :: "'v \<Rightarrow> 'v blue_witness \<Rightarrow> 'v blue_witness" where
  "prep_wit_blue u0 NO_CYC = NO_CYC"
| "prep_wit_blue u0 (REACH v p u p') = (
  if u0=u then
    CIRC v (p@u#p') (u0#p')
  else
    REACH v p u (u0#p')
  )"
| "prep_wit_blue u0 (CIRC v pc pr) = CIRC v pc (u0#pr)"

text \<open>Initialize blue witness\<close>
fun init_wit_blue :: "'v \<Rightarrow> 'v red_witness \<Rightarrow> 'v blue_witness" where
  "init_wit_blue u0 None = NO_CYC"
| "init_wit_blue u0 (Some (p,u)) = (
  if u=u0 then
    CIRC u0 p []
  else REACH u0 p u [])"

text \<open>Extract result from witness\<close>
definition "extract_res cyc 
  \<equiv> (case cyc of CIRC v pc pr \<Rightarrow> Some (v,pc,pr) | _ \<Rightarrow> None)"

subsubsection \<open>Outer (Blue) DFS\<close>
definition blue_dfs 
  :: "('a\<times>'a) set \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ('a\<times>'a list\<times>'a list) option nres" 
  where
  "blue_dfs E A s \<equiv> do {
    (_,_,_,cyc) \<leftarrow> REC\<^sub>T (\<lambda>D (blues,reds,onstack,s). do {
      let blues=insert s blues;
      let onstack=insert s onstack;
      (blues,reds,onstack,cyc) \<leftarrow> 
      FOREACH\<^sub>C (E``{s}) (\<lambda>(_,_,_,cyc). cyc=NO_CYC) 
        (\<lambda>t (blues,reds,onstack,cyc). 
          if t\<notin>blues then do {
            (blues,reds,onstack,cyc) \<leftarrow> D (blues,reds,onstack,t);
            RETURN (blues,reds,onstack,(prep_wit_blue s cyc))
          } else RETURN (blues,reds,onstack,cyc))
        (blues,reds,onstack,NO_CYC);

      (reds,cyc) \<leftarrow> 
      if cyc=NO_CYC \<and> s\<in>A then do {
        (reds,rcyc) \<leftarrow> red_dfs E onstack reds s;
        RETURN (reds, init_wit_blue s rcyc)
      } else RETURN (reds,cyc);

      let onstack=onstack - {s};
      RETURN (blues,reds,onstack,cyc)
    }) ({},{},{},s);
    RETURN (extract_res cyc)
  }
  "


subsection "Correctness"

subsubsection "Specification"

text \<open>Specification of a reachable accepting cycle:\<close>
definition "has_acc_cycle E A v0 \<equiv> \<exists>v\<in>A. (v0,v)\<in>E\<^sup>* \<and> (v,v)\<in>E\<^sup>+"

text \<open>Specification of witness for accepting cycle\<close>
definition "is_acc_cycle E A v0 v r c 
  \<equiv> v\<in>A \<and> path E v0 r v \<and> path E v c v \<and> c\<noteq>[]"

text \<open>Specification is compatible with existence of accepting cycle\<close>
lemma is_acc_cycle_eq:
  "has_acc_cycle E A v0 \<longleftrightarrow> (\<exists>v r c. is_acc_cycle E A v0 v r c)"
  unfolding has_acc_cycle_def is_acc_cycle_def
  by (auto elim!: rtrancl_is_path trancl_is_path
    intro: path_is_rtrancl path_is_trancl) 

subsubsection "Correctness Proofs"

text \<open>Additional invariant to be maintained between calls of red dfs\<close>
definition "red_dfs_inv E U reds onstack \<equiv> 
  E``U \<subseteq> U           \<comment> \<open>Upper bound is closed under transitions\<close>
  \<and> finite U         \<comment> \<open>Upper bound is finite\<close>
  \<and> reds \<subseteq> U         \<comment> \<open>Red set below upper bound\<close>
  \<and> E``reds \<subseteq> reds   \<comment> \<open>Red nodes closed under reachability\<close>
  \<and> E``reds \<inter> onstack = {} \<comment> \<open>No red node with edge to stack\<close>
"

lemma red_dfs_inv_initial:
  assumes "finite (E\<^sup>*``{v0})"
  shows "red_dfs_inv E (E\<^sup>*``{v0}) {} {}"
  using assms unfolding red_dfs_inv_def
  apply auto
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

      \<comment> \<open>First foreach loop, checking for onstack-successor\<close>
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

      \<comment> \<open>Second foreach loop, iterating over sucessors\<close>
      apply (rule_tac I="fe_inv (insert b S) (insert b a) b" in
        FOREACHc_rule
      )
      apply (auto simp add: pre_def gen_dfs_pre_imp_fin) []

      apply (auto simp add: pre_def fe_inv_def gen_dfs_pre_imp_fe) []

      apply (intro refine_vcg)

      \<comment> \<open>Recursive call\<close>
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
  fixes v0 :: 'v
  assumes FIN[simp,intro!]: "finite (E\<^sup>*``{v0})"
  shows "blue_dfs E A v0 \<le> SPEC (\<lambda>r. 
    case r of None \<Rightarrow> \<not>has_acc_cycle E A v0
  | Some (v,pc,pv) \<Rightarrow> is_acc_cycle E A v0 v pv pc)"
proof -
  let ?ndfs = "
  do {
    (_,_,_,cyc) \<leftarrow> REC\<^sub>T (\<lambda>D (blues,reds,onstack,s). do {
      let blues=insert s blues;
      let onstack=insert s onstack;
      (blues,reds,onstack,cyc) \<leftarrow> 
      FOREACH\<^sub>C (E``{s}) (\<lambda>(_,_,_,cyc). cyc=NO_CYC) 
        (\<lambda>t (blues,reds,onstack,cyc). 
          if t\<notin>blues then do {
            (blues,reds,onstack,cyc) \<leftarrow> D (blues,reds,onstack,t);
            RETURN (blues,reds,onstack,(prep_wit_blue s cyc))
          } else RETURN (blues,reds,onstack,cyc))
        (blues,reds,onstack,NO_CYC);

      (reds,cyc) \<leftarrow> 
      if cyc=NO_CYC \<and> s\<in>A then do {
        (reds,rcyc) \<leftarrow> red_dfs E onstack reds s;
        RETURN (reds, init_wit_blue s rcyc)
      } else RETURN (reds,cyc);

      let onstack=onstack - {s};
      RETURN (blues,reds,onstack,cyc)
    }) ({},{},{},s);
    RETURN (case cyc of NO_CYC \<Rightarrow> None | CIRC v pc pr \<Rightarrow> Some (v,pc,pr))
  }" 
  let "do {_ \<leftarrow> REC\<^sub>T ?body ?init; _}" = "?ndfs"

  let ?U = "E\<^sup>*``{v0}"

  define add_inv where "add_inv = (\<lambda>blues reds onstack. 
    \<not>(\<exists>v\<in>(blues-onstack)\<inter>A. (v,v)\<in>E\<^sup>+)  \<comment> \<open>No cycles over finished, accepting states\<close>
    \<and> reds \<subseteq> blues                     \<comment> \<open>Red nodes are also blue\<close>
    \<and> reds \<inter> onstack = {}              \<comment> \<open>No red nodes on stack\<close>
    \<and> red_dfs_inv E ?U reds onstack)"

  define cyc_post where "cyc_post = (\<lambda>blues reds onstack u0 cyc. (case cyc of 
      NO_CYC \<Rightarrow> add_inv blues reds onstack
    | REACH v p u p' \<Rightarrow> v\<in>A \<and> u\<in>onstack-{u0} \<and> p\<noteq>[] 
      \<and> path E v p u \<and> path E u0 p' v
    | CIRC v pc pr \<Rightarrow> v\<in>A \<and> pc\<noteq>[] \<and> path E v pc v \<and> path E u0 pr v
    ))"

  define pre where "pre = (\<lambda>(blues,reds,onstack,u).  
    gen_dfs_pre E ?U onstack blues u \<and> add_inv blues reds onstack)"

  define post where "post = (\<lambda>(blues0,reds0::'v set,onstack0,u0) (blues,reds,onstack,cyc). 
    onstack = onstack0
    \<and> gen_dfs_post E ?U onstack0 blues0 u0 blues (cyc\<noteq>NO_CYC)
    \<and> cyc_post blues reds onstack u0 cyc)"

  define fe_inv where "fe_inv = (\<lambda>blues0 u0 onstack0 it (blues,reds,onstack,cyc). 
    onstack=onstack0 
    \<and> gen_dfs_fe_inv E ?U onstack0 blues0 u0 it blues (cyc\<noteq>NO_CYC)
    \<and> cyc_post blues reds onstack u0 cyc)"

  have GENPRE: "gen_dfs_pre E ?U {} {} v0"
    apply (auto intro: gen_dfs_pre_initial)
    done
  hence PRE': "pre ({},{},{},v0)"
    unfolding pre_def add_inv_def
    apply (auto intro: red_dfs_inv_initial)
    done

  {
    fix blues reds onstack cyc
    assume "post ({},{},{},v0) (blues,reds,onstack,cyc)"
    hence "case cyc of NO_CYC \<Rightarrow> \<not>has_acc_cycle E A v0
      | REACH _ _ _ _ \<Rightarrow> False
      | CIRC v pc pr \<Rightarrow> is_acc_cycle E A v0 v pr pc"
      unfolding post_def cyc_post_def
      apply (cases cyc)
      using gen_dfs_post_imp_eq[OF GENPRE, of blues] 
      apply (auto simp: add_inv_def has_acc_cycle_def) []
      apply auto []
      apply (auto simp: is_acc_cycle_def) []
      done
  } note IMP_POST = this

  {
    fix onstack blues u0 reds
    assume "pre (blues,reds,onstack,u0)"
    hence "fe_inv (insert u0 blues) u0 (insert u0 onstack) (E``{u0}) 
      (insert u0 blues,reds,insert u0 onstack,NO_CYC)"
      unfolding fe_inv_def add_inv_def cyc_post_def
      apply clarsimp
      apply (intro conjI)
      apply (simp add: pre_def gen_dfs_pre_imp_fe)
      apply (auto simp: pre_def add_inv_def) []
      apply (auto simp: pre_def add_inv_def) []
      defer
      apply (auto simp: pre_def add_inv_def) []
      apply (unfold pre_def add_inv_def red_dfs_inv_def gen_dfs_pre_def) []
      apply clarsimp
      apply blast

      apply (auto simp: pre_def add_inv_def gen_dfs_pre_def) []
      done
  } note PRE_IMP_FE = this

  have [simp]: "\<And>u cyc. prep_wit_blue u cyc = NO_CYC \<longleftrightarrow> cyc=NO_CYC"
    by (case_tac cyc) auto

  {
    fix blues0 reds0 onstack0 u0 
      blues reds onstack blues' reds' onstack' 
      cyc it t
    assume PRE: "pre (blues0,reds0,onstack0,u0)"
    assume FEI: "fe_inv (insert u0 blues0) u0 (insert u0 onstack0) 
        it (blues,reds,onstack,NO_CYC)"
    assume IT: "t\<in>it" "it\<subseteq>E``{u0}" "t\<notin>blues"
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
      apply (auto split: blue_witness.split_asm intro: path_conc path_prepend)
      done
  } note FE_INV_PRES=this

  {
    fix blues reds onstack u0
    assume "pre (blues,reds,onstack,u0)"
    hence "(v0,u0)\<in>E\<^sup>*"
      unfolding pre_def gen_dfs_pre_def by auto
  } note PRE_IMP_REACH = this

  {
    fix blues0 reds0 onstack0 u0 blues reds onstack 
    assume A: "pre (blues0,reds0,onstack0,u0)"
       "fe_inv (insert u0 blues0) u0 (insert u0 onstack0) 
        {} (blues,reds,onstack,NO_CYC)"
       "u0\<in>A"
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
    assume ACC: "u0\<in>A" 
    assume SPECR: "case rcyc of
      Some (p,v) \<Rightarrow> v\<in>onstack \<and> p\<noteq>[] \<and> path E u0 p v
    | None \<Rightarrow> 
        red_dfs_inv E ?U reds' onstack 
        \<and> u0\<in>reds' 
        \<and> reds' \<subseteq> reds \<union> E\<^sup>* `` {u0}"
    have "post (blues0,reds0,onstack0,u0) 
      (blues,reds',onstack - {u0},init_wit_blue u0 rcyc)"
      unfolding post_def add_inv_def cyc_post_def
      apply (clarsimp)
      apply (intro conjI)
    proof goal_cases
      from PRE FEI show OS0[symmetric]: "onstack - {u0} = onstack0"
        by (auto simp: pre_def fe_inv_def add_inv_def gen_dfs_pre_def) []

      from PRE FEI have "u0\<in>onstack"
        unfolding pre_def gen_dfs_pre_def fe_inv_def gen_dfs_fe_inv_def
        by auto

      from PRE FEI 
      show POST: "gen_dfs_post E (E\<^sup>* `` {v0}) onstack0 blues0 u0 blues 
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
        show "(\<forall>v\<in>(blues - (onstack0 - {u0})) \<inter> A. (v, v) \<notin> E\<^sup>+) \<and>
          reds' \<subseteq> blues \<and>
          reds' \<inter> (onstack0 - {u0}) = {} \<and>
          red_dfs_inv E (E\<^sup>* `` {v0}) reds' (onstack0 - {u0})"
        proof (intro conjI)
          from SPECR have RINV: "red_dfs_inv E ?U reds' onstack" 
            and "u0\<in>reds'" 
            and REDS'R: "reds' \<subseteq> reds \<union> E\<^sup>*``{u0}"
            by auto

          from RINV show 
            RINV': "red_dfs_inv E (E\<^sup>* `` {v0}) reds' (onstack0 - {u0})"
            unfolding red_dfs_inv_def by auto

          from RINV'[unfolded red_dfs_inv_def] have 
            REDS'CL: "E``reds' \<subseteq> reds'" 
            and DJ': "E `` reds' \<inter> (onstack0 - {u0}) = {}" by auto

          from RINV[unfolded red_dfs_inv_def] have 
            DJ: "E `` reds' \<inter> (onstack) = {}" by auto

          show "reds' \<subseteq> blues" 
          proof 
            fix v assume "v\<in>reds'"
            with REDS'R have "v\<in>reds \<or> (u0,v)\<in>E\<^sup>*" by blast
            thus "v\<in>blues" proof
              assume "v\<in>reds" 
              moreover with FEI have "reds\<subseteq>blues" 
                unfolding fe_inv_def add_inv_def cyc_post_def by auto
              ultimately show ?thesis ..
            next
              from POST[unfolded gen_dfs_post_def OS0] have 
                CL: "E `` (blues - (onstack0 - {u0})) \<subseteq> blues" and "u0\<in>blues" 
                by auto
              from PRE FEI have "onstack0 \<subseteq> blues"
                unfolding pre_def fe_inv_def gen_dfs_pre_def gen_dfs_fe_inv_def
                by auto

              assume "(u0,v)\<in>E\<^sup>*"
              thus "v\<in>blues"
              proof (cases rule: rtrancl_last_visit[where S="onstack - {u0}"])
                case no_visit
                thus "v\<in>blues" using \<open>u0\<in>blues\<close> CL 
                  by induct (auto elim: rtranclE)
              next
                case (last_visit_point u)
                then obtain uh where "(u0,uh)\<in>E\<^sup>*" and "(uh,u)\<in>E"
                  by (metis tranclD2) 
                with REDS'CL DJ' \<open>u0\<in>reds'\<close> have "uh\<in>reds'" 
                  by (auto dest: Image_closed_trancl)
                with DJ' \<open>(uh,u)\<in>E\<close> \<open>u \<in> onstack - {u0}\<close> have False 
                  by simp blast
                thus ?thesis ..
              qed
            qed
          qed

          show "\<forall>v\<in>(blues - (onstack0 - {u0})) \<inter> A. (v, v) \<notin> E\<^sup>+"
          proof 
            fix v
            assume A: "v \<in> (blues - (onstack0 - {u0})) \<inter> A"
            show "(v,v)\<notin>E\<^sup>+" proof (cases "v=u0")
              assume "v\<noteq>u0" 
              with A have "v\<in>(blues - (insert u0 onstack)) \<inter> A" by auto
              with FEI show ?thesis 
                unfolding fe_inv_def add_inv_def cyc_post_def by auto
            next
              assume [simp]: "v=u0"
              show ?thesis proof
                assume "(v,v)\<in>E\<^sup>+"
                then obtain uh where "(u0,uh)\<in>E\<^sup>*" and "(uh,u0)\<in>E" 
                  by (auto dest: tranclD2)
                with REDS'CL DJ \<open>u0\<in>reds'\<close> have "uh\<in>reds'" 
                  by (auto dest: Image_closed_trancl)
                with DJ \<open>(uh,u0)\<in>E\<close> \<open>u0 \<in> onstack\<close> show False by blast
              qed
            qed
          qed

          show "reds' \<inter> (onstack0 - {u0}) = {}" 
          proof (rule ccontr)
            assume "reds' \<inter> (onstack0 - {u0}) \<noteq> {}"
            then obtain v where "v\<in>reds'" and "v\<in>onstack0" and "v\<noteq>u0" by auto
          
            from \<open>v\<in>reds'\<close> REDS'R have "v\<in>reds \<or> (u0,v)\<in>E\<^sup>*"
              by auto
            thus False proof
              assume "v\<in>reds" 
              with FEI[unfolded fe_inv_def add_inv_def cyc_post_def] 
                \<open>v\<in>onstack0\<close>
              show False by auto
            next
              assume "(u0,v)\<in>E\<^sup>*"
              with \<open>v\<noteq>u0\<close> obtain uh where "(u0,uh)\<in>E\<^sup>*" and "(uh,v)\<in>E"
                by (auto elim: rtranclE)
              with REDS'CL DJ \<open>u0\<in>reds'\<close> have "uh\<in>reds'" 
                by (auto dest: Image_closed_trancl)
              with DJ \<open>(uh,v)\<in>E\<close> \<open>v \<in> onstack0\<close> show False by simp blast
            qed
          qed
        qed
      next
        fix u p
        assume [simp]: "rcyc = Some (p,u)"
        show "(u = u0 \<longrightarrow> u0 \<in> A \<and> p \<noteq> [] \<and> path E u0 p u0) \<and>
          (u \<noteq> u0 \<longrightarrow> u0 \<in> A \<and> u \<in> onstack0 \<and> p \<noteq> [] \<and> path E u0 p u)"
        proof (intro conjI impI)
          show "u0\<in>A" by fact
          show "u0\<in>A" by fact
          from SPECR show 
            "u\<noteq>u0 \<Longrightarrow> u\<in>onstack0" 
            "p\<noteq>[]" 
            "p\<noteq>[]" 
            "path E u0 p u" 
            "u=u0 \<Longrightarrow> path E u0 p u0"
            by auto
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
    and NCOND: "u0\<notin>A"

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
    and IT: "it\<subseteq>E``{u0}"
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
    fix \<sigma>
    assume INV0: "pre \<sigma>"
    have "REC\<^sub>T ?body \<sigma> 
      \<le> SPEC (post \<sigma>)"

      apply (intro refine_vcg
        RECT_rule[where pre="pre"
        and V="gen_dfs_var ?U <*lex*> {}"]
      )
      apply refine_mono
      apply (blast intro!: gen_dfs_pre_imp_wf[OF GENPRE])
      apply (rule INV0)

      \<comment> \<open>Foreach loop\<close>
      apply (rule_tac 
        I="fe_inv (insert bb a) bb (insert bb ab)" 
        in FOREACHc_rule')

      apply (auto simp add: pre_def gen_dfs_pre_imp_fin) []

      apply (blast intro: PRE_IMP_FE)

      apply (intro refine_vcg)

      \<comment> \<open>Recursive call\<close>
      apply (rule order_trans)
      apply (rprems)
      apply (clarsimp simp add: pre_def fe_inv_def cyc_post_def)
      apply (rule gen_dfs_fe_inv_imp_pre, assumption+) []
      apply (auto simp add: pre_def fe_inv_def intro: gen_dfs_fe_inv_imp_var) []

      apply (auto intro: FE_INV_PRES) []

      apply (auto simp add: pre_def post_def fe_inv_def 
        intro: gen_dfs_fe_inv_pres_visited) []

      apply (intro refine_vcg)

      \<comment> \<open>Nested DFS call\<close>
      apply (rule order_trans)
      apply (rule red_dfs_correct[where U="E\<^sup>* `` {v0}"])
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

  show ?thesis
    unfolding blue_dfs_def extract_res_def
    apply (intro refine_vcg)
    apply (rule order_trans)
    apply (rule GEN)
    apply fact
    apply (intro refine_vcg)
    apply clarsimp
    apply (drule IMP_POST)
    apply (simp split: blue_witness.split_asm)
    done
qed

subsection "Refinement"

subsubsection \<open>Setup for Custom Datatypes\<close>
text \<open>This effort can be automated, but currently, such an automation is
  not yet implemented\<close>
abbreviation "red_wit_rel \<equiv> \<langle>\<langle>\<langle>nat_rel\<rangle>list_rel,nat_rel\<rangle>prod_rel\<rangle>option_rel"
abbreviation "wit_res_rel \<equiv> 
  \<langle>\<langle>nat_rel,\<langle>\<langle>nat_rel\<rangle>list_rel,\<langle>nat_rel\<rangle>list_rel\<rangle>prod_rel\<rangle>prod_rel\<rangle>option_rel"
abbreviation "i_red_wit \<equiv> \<langle>\<langle>\<langle>i_nat\<rangle>\<^sub>ii_list,i_nat\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_option"
abbreviation "i_res \<equiv> 
  \<langle>\<langle>i_nat,\<langle>\<langle>i_nat\<rangle>\<^sub>ii_list,\<langle>i_nat\<rangle>\<^sub>ii_list\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_option"

abbreviation "blue_wit_rel \<equiv> (Id::(nat blue_witness \<times> _) set)"
consts i_blue_wit :: interface

term extract_res

lemma [autoref_itype]:
  "NO_CYC ::\<^sub>i i_blue_wit"
  "(=) ::\<^sub>i i_blue_wit \<rightarrow>\<^sub>i i_blue_wit \<rightarrow>\<^sub>i i_bool"
  "init_wit_blue ::\<^sub>i i_nat \<rightarrow>\<^sub>i i_red_wit \<rightarrow>\<^sub>i i_blue_wit"
  "prep_wit_blue ::\<^sub>i i_nat \<rightarrow>\<^sub>i i_blue_wit \<rightarrow>\<^sub>i i_blue_wit"
  "red_init_witness ::\<^sub>i i_nat \<rightarrow>\<^sub>i i_nat \<rightarrow>\<^sub>i i_red_wit"
  "prep_wit_red ::\<^sub>i i_nat \<rightarrow>\<^sub>i i_red_wit \<rightarrow>\<^sub>i i_red_wit"
  "extract_res ::\<^sub>i i_blue_wit \<rightarrow>\<^sub>i i_res"
  by auto

context begin interpretation autoref_syn .  
lemma [autoref_op_pat]: "NO_CYC \<equiv> OP NO_CYC :::\<^sub>i i_blue_wit" by simp
end

lemma autoref_wit[autoref_rules_raw]:
  "(NO_CYC,NO_CYC)\<in>blue_wit_rel"
  "((=), (=)) \<in> blue_wit_rel \<rightarrow> blue_wit_rel \<rightarrow> bool_rel"
  "(init_wit_blue, init_wit_blue) \<in> nat_rel \<rightarrow> red_wit_rel \<rightarrow> blue_wit_rel"
  "(prep_wit_blue,prep_wit_blue)\<in>nat_rel \<rightarrow> blue_wit_rel \<rightarrow> blue_wit_rel"
  "(red_init_witness, red_init_witness) \<in> nat_rel\<rightarrow>nat_rel\<rightarrow>red_wit_rel"
  "(prep_wit_red,prep_wit_red) \<in> nat_rel \<rightarrow> red_wit_rel \<rightarrow> red_wit_rel"
  "(extract_res,extract_res) \<in> blue_wit_rel \<rightarrow> wit_res_rel"
  by simp_all

subsubsection \<open>Actual Refinement\<close>



schematic_goal red_dfs_impl_refine_aux:
  (*notes [[goals_limit = 1]]*)
  fixes u'::"nat" and V'::"nat set"
  notes [autoref_tyrel] = 
    ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>iam_set_rel"]
  assumes [autoref_rules]:
    "(u,u')\<in>nat_rel" 
    "(V,V')\<in>\<langle>nat_rel\<rangle>iam_set_rel" 
    "(onstack,onstack')\<in>\<langle>nat_rel\<rangle>iam_set_rel" 
    "(E,E')\<in>\<langle>nat_rel\<rangle>slg_rel"
  shows "(RETURN (?f::?'c), red_dfs E' onstack' V' u') \<in> ?R"
  apply -
  unfolding red_dfs_def
  apply (autoref_monadic)
  done

concrete_definition red_dfs_impl uses red_dfs_impl_refine_aux
prepare_code_thms red_dfs_impl_def
declare red_dfs_impl.refine[autoref_higher_order_rule, autoref_rules]

schematic_goal ndfs_impl_refine_aux:
  fixes s::"nat"
  notes [autoref_tyrel] = 
    ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>iam_set_rel"]
  assumes [autoref_rules]: 
    "(succi,E)\<in>\<langle>nat_rel\<rangle>slg_rel"
    "(Ai,A)\<in>\<langle>nat_rel\<rangle>iam_set_rel"
  notes [autoref_rules] = IdI[of s]
  shows "(RETURN (?f::?'c), blue_dfs E A s) \<in> \<langle>?R\<rangle>nres_rel"
  unfolding blue_dfs_def
  apply (autoref_monadic (trace))
  done

concrete_definition ndfs_impl for succi Ai s uses ndfs_impl_refine_aux 
prepare_code_thms ndfs_impl_def
export_code ndfs_impl checking SML

term "\<lambda>E A v0. ndfs_impl (succ_of_list_impl E) (acc_of_list_impl A) v0"

term nat_of_integer

definition "succ_of_list_impl_int \<equiv> 
  succ_of_list_impl o map (\<lambda>(u,v). (nat_of_integer u, nat_of_integer v))"

definition "acc_of_list_impl_int \<equiv> 
  acc_of_list_impl o map nat_of_integer"

export_code 
  ndfs_impl 
  succ_of_list_impl_int
  acc_of_list_impl_int
  nat_of_integer
  integer_of_nat
  in SML module_name HPY_new

ML_val \<open>
  @{code ndfs_impl} (@{code succ_of_list_impl_int} [(1,2),(2,3),(2,7),(7,1)])
    (@{code acc_of_list_impl_int} [7]) (@{code nat_of_integer} 1)

\<close>


schematic_goal ndfs_impl_refine_aux_old:
  fixes s::"nat"
  assumes [autoref_rules]: 
    "(succi,E)\<in>\<langle>nat_rel\<rangle>slg_rel"
    "(Ai,A)\<in>\<langle>nat_rel\<rangle>dflt_rs_rel"
  notes [autoref_rules] = IdI[of s]
  shows "(RETURN (?f::?'c), blue_dfs E A s) \<in> \<langle>?R\<rangle>nres_rel"
  unfolding blue_dfs_def red_dfs_def 
  using [[autoref_trace]]
  apply (autoref_monadic)
  done

end
