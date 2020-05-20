section \<open>General DFS with Hooks\<close>
theory Param_DFS
imports 
  CAVA_Base.CAVA_Base
  CAVA_Automata.Digraph
  "Misc/DFS_Framework_Refine_Aux"
begin

text \<open>
  We define a general DFS algorithm, which is parameterized over
  hook functions at certain events during the DFS.
\<close>

subsection \<open>State and Parameterization\<close>
(* A DFS with timing and a stack, phrased iteratively *)
text \<open>The state of the general DFS. 
  Users may inherit from this state using the record package's 
  inheritance support.
\<close>
record 'v state =
  counter :: nat               \<comment> \<open>Node counter (timer)\<close>
  discovered :: "'v \<rightharpoonup> nat"    \<comment> \<open>Discovered times of nodes\<close>
  finished :: "'v \<rightharpoonup> nat"      \<comment> \<open>Finished times of nodes\<close>
  pending :: "('v \<times> 'v) set"  \<comment> \<open>Edges to be processed next\<close>
  stack :: "'v list"          \<comment> \<open>Current DFS stack\<close>
  tree_edges :: "'v rel"      \<comment> \<open>Tree edges\<close>
  back_edges :: "'v rel"      \<comment> \<open>Back edges\<close>
  cross_edges :: "'v rel"     \<comment> \<open>Cross edges\<close>

abbreviation "NOOP s \<equiv> RETURN (state.more s)"

text \<open>Record holding the parameterization.\<close>
record ('v,'s,'es) gen_parameterization =
  on_init :: "'es nres"
  on_new_root :: "'v \<Rightarrow> 's \<Rightarrow> 'es nres"
  on_discover :: "'v \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 'es nres"
  on_finish :: "'v \<Rightarrow> 's \<Rightarrow> 'es nres"
  on_back_edge :: "'v \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 'es nres"
  on_cross_edge :: "'v \<Rightarrow> 'v \<Rightarrow> 's \<Rightarrow> 'es nres"
  is_break :: "'s \<Rightarrow> bool"

text \<open>Default type restriction for parameterizations.
  The event handler functions go from a complete state to
  the user-defined part of the state (i.e. the fields added by inheritance).
\<close>
type_synonym ('v,'es) parameterization 
  = "('v,('v,'es) state_scheme,'es) gen_parameterization"

text \<open>Default parameterization, the functions do nothing.
  This can be used as the basis for specialized parameterizations, which may 
  be derived by updating some fields.
\<close>
definition "\<And>more init. dflt_parametrization more init \<equiv> \<lparr>  
  on_init = init,
  on_new_root = \<lambda>_. RETURN o more,
  on_discover = \<lambda>_ _. RETURN o more,
  on_finish = \<lambda>_. RETURN o more,
  on_back_edge = \<lambda>_ _. RETURN o more,
  on_cross_edge = \<lambda>_ _. RETURN o more,
  is_break = \<lambda>_. False \<rparr>"
lemmas dflt_parametrization_simp[simp] =
  gen_parameterization.simps[mk_record_simp, OF dflt_parametrization_def]

text \<open>This locale builds a DFS algorithm from a graph and a parameterization.\<close>
locale param_DFS_defs =
  graph_defs G
  for G :: "('v, 'more) graph_rec_scheme"
  +
  fixes param :: "('v,'es) parameterization"
begin
  subsection \<open>DFS operations\<close>
  subsubsection \<open>Node predicates\<close>
  text \<open>First, we define some predicates to check whether nodes are in certain sets\<close>
  definition is_discovered :: "'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> bool"
    where "is_discovered u s \<equiv> u \<in> dom (discovered s)"

  definition is_finished :: "'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> bool"
    where "is_finished u s \<equiv> u \<in> dom (finished s)"

  definition is_empty_stack :: "('v,'es) state_scheme \<Rightarrow> bool"
    where "is_empty_stack s \<equiv> stack s = []"

  (*definition top_pending :: "('v,'es) state_scheme \<Rightarrow> 'v \<times> 'v set" where
    "top_pending s \<equiv> (hd (stack s), pending s `` {hd (stack s)})"*)

  subsubsection \<open>Effects on Basic State\<close>
  text \<open>We define the effect of the operations on the basic part of the state\<close>
  definition discover 
    :: "'v \<Rightarrow> 'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> ('v,'es) state_scheme"
  where
  "discover u v s \<equiv> let
    d = (discovered s)(v \<mapsto> counter s); c = counter s + 1;
    st = v#stack s;
    p = pending s \<union> {v} \<times> E``{v};
    t = insert (u,v) (tree_edges s)
  in s\<lparr> discovered := d, counter := c, stack := st, pending := p, tree_edges := t\<rparr>"

  lemma discover_simps[simp]:
    "counter (discover u v s) = Suc (counter s)"
    "discovered (discover u v s) = (discovered s)(v \<mapsto> counter s)" 
    "finished (discover u v s) = finished s"
    "stack (discover u v s) = v#stack s"
    "pending (discover u v s) = pending s \<union> {v} \<times> E``{v}"
    "tree_edges (discover u v s) = insert (u,v) (tree_edges s)"
    "cross_edges (discover u v s) = cross_edges s"
    "back_edges (discover u v s) = back_edges s"
    "state.more (discover u v s) = state.more s"
    by (simp_all add: discover_def)

  definition finish 
    :: "'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> ('v,'es) state_scheme" 
  where
  "finish u s \<equiv> let
    f = (finished s)(u \<mapsto> counter s); c = counter s + 1;
    st = tl (stack s)
  in s\<lparr> finished := f, counter := c, stack := st\<rparr>"

  lemma finish_simps[simp]:
    "counter (finish u s) = Suc (counter s)"
    "discovered (finish u s) = discovered s"
    "finished (finish u s) = (finished s)(u \<mapsto> counter s)"
    "stack (finish u s) = tl (stack s)"
    "pending (finish u s) = pending s"
    "tree_edges (finish u s) = tree_edges s"
    "cross_edges (finish u s) = cross_edges s"
    "back_edges (finish u s) = back_edges s"
    "state.more (finish u s) = state.more s"
    by (simp_all add: finish_def)

  definition back_edge
    :: "'v \<Rightarrow> 'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> ('v,'es) state_scheme"
  where
  "back_edge u v s \<equiv> let
    b = insert (u,v) (back_edges s)
   in s\<lparr> back_edges := b \<rparr>"

  lemma back_edge_simps[simp]:
    "counter (back_edge u v s) = counter s"
    "discovered (back_edge u v s) = discovered s"
    "finished (back_edge u v s) = finished s"
    "stack (back_edge u v s) = stack s"
    "pending (back_edge u v s) = pending s"
    "tree_edges (back_edge u v s) = tree_edges s"
    "cross_edges (back_edge u v s) = cross_edges s"
    "back_edges (back_edge u v s) = insert (u,v) (back_edges s)"
    "state.more (back_edge u v s) = state.more s"
    by (simp_all add: back_edge_def)

  definition cross_edge
    :: "'v \<Rightarrow> 'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> ('v,'es) state_scheme"
  where
  "cross_edge u v s \<equiv> let
    c = insert (u,v) (cross_edges s)
   in s\<lparr> cross_edges := c \<rparr>"
  
  lemma cross_edge_simps[simp]:
    "counter (cross_edge u v s) = counter s"
    "discovered (cross_edge u v s) = discovered s"
    "finished (cross_edge u v s) = finished s"
    "stack (cross_edge u v s) = stack s"
    "pending (cross_edge u v s) = pending s"
    "tree_edges (cross_edge u v s) = tree_edges s"
    "cross_edges (cross_edge u v s) = insert (u,v) (cross_edges s)"
    "back_edges (cross_edge u v s) = back_edges s"
    "state.more (cross_edge u v s) = state.more s"
    by (simp_all add: cross_edge_def)


  definition new_root
    :: "'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> ('v,'es) state_scheme"
  where
    "new_root v0 s \<equiv> let
       c = Suc (counter s);
       d = (discovered s)(v0 \<mapsto> counter s);
       p = {v0}\<times>E``{v0};
       st = [v0]
     in s\<lparr>counter := c, discovered := d, pending := p, stack := st\<rparr>"

  lemma new_root_simps[simp]:
    "counter (new_root v0 s) = Suc (counter s)"
    "discovered (new_root v0 s) = (discovered s)(v0 \<mapsto> counter s)"
    "finished (new_root v0 s) = finished s"
    "stack (new_root v0 s) = [v0]"
    "pending (new_root v0 s) = ({v0}\<times>E``{v0})"
    "tree_edges (new_root v0 s) = tree_edges s"
    "cross_edges (new_root v0 s) = cross_edges s"
    "back_edges (new_root v0 s) = back_edges s"
    "state.more (new_root v0 s) = state.more s"
    by (simp_all add: new_root_def)

  definition "empty_state e
    \<equiv> \<lparr> counter = 0,
         discovered = Map.empty,
         finished = Map.empty,
         pending = {},
         stack = [],
         tree_edges = {},
         back_edges = {},
         cross_edges = {},
         \<dots> = e \<rparr>"

  lemma empty_state_simps[simp]:
    "counter (empty_state e) = 0"
    "discovered (empty_state e) = Map.empty"
    "finished (empty_state e) = Map.empty"
    "pending (empty_state e) = {}"
    "stack (empty_state e) = []"
    "tree_edges (empty_state e) = {}"
    "back_edges (empty_state e) = {}"
    "cross_edges (empty_state e) = {}"
    "state.more (empty_state e) = e"
    by (simp_all add: empty_state_def)




  subsubsection \<open>Effects on Whole State\<close>  
  text \<open>The effects of the operations on the whole state are defined by 
    combining the effects of the basic state with the parameterization.\<close>
  
  definition do_cross_edge
    :: "'v \<Rightarrow> 'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> ('v,'es) state_scheme nres"
  where
  "do_cross_edge u v s \<equiv> do {
      let s = cross_edge u v s;
      e \<leftarrow> on_cross_edge param u v s;
      RETURN (s\<lparr>state.more := e\<rparr>)
    }"

  definition do_back_edge
    :: "'v \<Rightarrow> 'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> ('v,'es) state_scheme nres"
  where
  "do_back_edge u v s \<equiv> do {
      let s = back_edge u v s;
      e \<leftarrow> on_back_edge param u v s;
      RETURN (s\<lparr>state.more := e\<rparr>)
    }"

  definition do_known_edge
    :: "'v \<Rightarrow> 'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> ('v,'es) state_scheme nres"
  where
  "do_known_edge u v s \<equiv> 
    if is_finished v s then 
      do_cross_edge u v s 
    else 
      do_back_edge u v s"  

  definition do_discover
    :: "'v \<Rightarrow> 'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> ('v,'es) state_scheme nres"
  where
  "do_discover u v s \<equiv> do {
    let s = discover u v s;
    e \<leftarrow> on_discover param u v s;
    RETURN (s\<lparr>state.more := e\<rparr>)
  }"

  definition do_finish
    :: "'v \<Rightarrow> ('v,'es) state_scheme \<Rightarrow> ('v,'es) state_scheme nres"
  where
  "do_finish u s \<equiv> do {
    let s = finish u s;
    e \<leftarrow> on_finish param u s;
    RETURN (s\<lparr>state.more := e\<rparr>)
  }"

  definition get_new_root where
    "get_new_root s \<equiv> SPEC (\<lambda>v. v\<in>V0 \<and> \<not>is_discovered v s)"  

  definition do_new_root where 
  "do_new_root v0 s \<equiv> do {
    let s = new_root v0 s;
    e \<leftarrow> on_new_root param v0 s;
    RETURN (s\<lparr>state.more := e\<rparr>)
  }"

  lemmas op_defs = discover_def finish_def back_edge_def cross_edge_def new_root_def
  lemmas do_defs = do_discover_def do_finish_def do_known_edge_def
    do_cross_edge_def do_back_edge_def do_new_root_def
  lemmas pred_defs = is_discovered_def is_finished_def is_empty_stack_def

  definition "init \<equiv> do {
    e \<leftarrow> on_init param;
    RETURN (empty_state e)
  }"

  subsection \<open>DFS Algorithm\<close>
  text \<open>We phrase the DFS algorithm iteratively:
    While there are undiscovered root nodes or the stack is not empty,
      inspect the topmost node on the stack: 
        Follow any pending edge, or finish the node if there 
        are no pending edges left.

    \<close>

  definition cond :: "('v,'es) state_scheme \<Rightarrow> bool" where
    "cond s \<longleftrightarrow> (V0 \<subseteq> {v. is_discovered v s} \<longrightarrow> \<not>is_empty_stack s) 
      \<and> \<not>is_break param s"  

  lemma cond_alt:
    "cond = (\<lambda>s. (V0 \<subseteq> dom (discovered s) \<longrightarrow> stack s \<noteq> []) \<and> \<not>is_break param s)"
    apply (rule ext)
    unfolding cond_def is_discovered_def is_empty_stack_def
    by auto


  definition get_pending ::
    "('v, 'es) state_scheme \<Rightarrow> ('v \<times> 'v option \<times> ('v, 'es) state_scheme) nres" 
    \<comment> \<open>Get topmost stack node and a pending edge if any. The pending
          edge is removed.\<close>
  where "get_pending s \<equiv> do {
    let u = hd (stack s);
    let Vs = pending s `` {u};

    if Vs = {} then
      RETURN (u,None,s)
    else do {
      v \<leftarrow> RES Vs;
      let s = s\<lparr> pending := pending s - {(u,v)}\<rparr>;
      RETURN (u,Some v,s)
    }
  }"

  definition step :: "('v,'es) state_scheme \<Rightarrow> ('v,'es) state_scheme nres" 
  where
    "step s \<equiv> 
      if is_empty_stack s then do {
        v0 \<leftarrow> get_new_root s;
        do_new_root v0 s
      } else do {
        (u,Vs,s) \<leftarrow> get_pending s;
        case Vs of 
          None \<Rightarrow> do_finish u s 
        | Some v \<Rightarrow> do {
          if is_discovered v s then 
            do_known_edge u v s
          else 
            do_discover u v s
        }
      }"


  definition "it_dfs \<equiv> init \<bind> WHILE cond step"
  definition "it_dfsT \<equiv> init \<bind> WHILET cond step"

end

subsection \<open>Invariants\<close>
text \<open>We now build the infrastructure for establishing invariants 
  of DFS algorithms. The infrastructure is modular and extensible, i.e., 
  we can define re-usable libraries of invariants.
\<close>


text \<open>For technical reasons, invariants are established in a two-step process:
  \<^enum> First, we prove the invariant wrt. the parameterization in the \<open>param_DFS\<close> locale.
  \<^enum> Next, we transfer the invariant to the \<open>DFS_invar\<close>-locale.
\<close>
(* This locale is required to establish new invariants.
  We would like to directly establish new invariants in the 
  DFS_invar-locale, unfortunately this causes technical problems:
  When interpreting the DFS_invar locale in a proof inside the 
  DFS_invar-locale itself, we get "duplicate constant" warnings,
  unless we prefix the interpreted locale, which may be quite confusing
  in a proof, as the user has to choose the prefixed lemmas, while the
  unprefixed ones are also available, but for the wrong state.
 *)
locale param_DFS =
  fb_graph G + param_DFS_defs G param
  for G :: "('v, 'more) graph_rec_scheme"
  and param :: "('v,'es) parameterization"
begin

  definition is_invar :: "(('v, 'es) state_scheme \<Rightarrow> bool) \<Rightarrow> bool"
    \<comment> \<open>Predicate that states that @{term I} is an invariant.\<close>
    where "is_invar I \<equiv> is_rwof_invar init cond step I"

end

text \<open>Invariants are transferred to this locale, which is parameterized
  with a state. \<close>
locale DFS_invar =
  param_DFS G param
  for G :: "('v, 'more) graph_rec_scheme"
  and param :: "('v,'es) parameterization"
  +
  fixes s :: "('v,'es) state_scheme"
  assumes rwof: "rwof init cond step s"
begin

  lemma make_invar_thm: "is_invar I \<Longrightarrow> I s"
    \<comment> \<open>Lemma to transfer an invariant into this locale\<close>
    using rwof_cons[OF _ rwof, folded is_invar_def] .

end

subsubsection \<open>Establishing Invariants\<close>
context param_DFS
begin
  text \<open> Include this into refine-rules to discard any information about 
    parameterization \<close>
  lemmas indep_invar_rules = 
    leof_True_rule[where m="on_init param"]
    leof_True_rule[where m="on_new_root param v0 s'" for v0 s']
    leof_True_rule[where m="on_discover param u v s'" for u v s']
    leof_True_rule[where m="on_finish param v s'" for v s']
    leof_True_rule[where m="on_cross_edge param u v s'" for u v s']
    leof_True_rule[where m="on_back_edge param u v s'" for u v s']

  
  lemma rwof_eq_DFS_invar[simp]: 
    "rwof init cond step = DFS_invar G param"
    \<comment> \<open>The DFS-invar locale is equivalent to the strongest invariant of the loop.\<close>
    apply (auto intro: DFS_invar.rwof intro!: ext)
    by unfold_locales

  lemma DFS_invar_step: "\<lbrakk>nofail it_dfs; DFS_invar G param s; cond s\<rbrakk> 
    \<Longrightarrow> step s \<le> SPEC (DFS_invar G param)"
    \<comment> \<open>A step preserves the (best) invariant.\<close>
    unfolding it_dfs_def rwof_eq_DFS_invar[symmetric]
    by (rule rwof_step)

  lemma DFS_invar_step': "\<lbrakk>nofail (step s); DFS_invar G param s; cond s\<rbrakk> 
    \<Longrightarrow> step s \<le> SPEC (DFS_invar G param)"
    unfolding it_dfs_def rwof_eq_DFS_invar[symmetric]
    by (rule rwof_step')

  text \<open>We define symbolic names for the preconditions of certain operations\<close>
  definition "pre_is_break s \<equiv> DFS_invar G param s"

  definition "pre_on_new_root v0 s' \<equiv> \<exists>s.
    DFS_invar G param s \<and> cond s \<and> 
    stack s = [] \<and> v0 \<in> V0 \<and> v0 \<notin> dom (discovered s) \<and>
    s' = new_root v0 s"

  definition "pre_on_finish u s' \<equiv> \<exists>s.
    DFS_invar G param s \<and> cond s \<and> 
    stack s \<noteq> [] \<and> u = hd (stack s) \<and> pending s `` {u} = {} \<and> s' = finish u s"

  definition "pre_edge_selected u v s \<equiv> 
    DFS_invar G param s \<and> cond s \<and> 
    stack s \<noteq> [] \<and> u = hd (stack s) \<and> (u, v) \<in> pending s"

  definition "pre_on_cross_edge u v s' \<equiv> \<exists>s. pre_edge_selected u v s \<and>
        v \<in> dom (discovered s) \<and> v\<in>dom (finished s) 
        \<and> s' = cross_edge u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>)"

  definition "pre_on_back_edge u v s' \<equiv> \<exists>s. pre_edge_selected u v s \<and>
        v \<in> dom (discovered s) \<and> v\<notin>dom (finished s) 
        \<and> s' = back_edge u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>)"

  definition "pre_on_discover u v s' \<equiv> \<exists>s. pre_edge_selected u v s \<and>
        v \<notin> dom (discovered s) 
        \<and> s' = discover u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>)"

  lemmas pre_on_defs = pre_on_new_root_def pre_on_finish_def 
    pre_edge_selected_def pre_on_cross_edge_def pre_on_back_edge_def
    pre_on_discover_def pre_is_break_def

  text \<open>Next, we define a set of rules to establish an invariant.\<close>  

  lemma establish_invarI[case_names init new_root finish cross_edge back_edge discover]:
    \<comment> \<open>Establish a DFS invariant (explicit preconditions).\<close>
    assumes init: "on_init param \<le>\<^sub>n SPEC (\<lambda>x. I (empty_state x))"
    assumes new_root: "\<And>s s' v0. 
      \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
       stack s = []; v0 \<in> V0; v0 \<notin> dom (discovered s);
        s' = new_root v0 s\<rbrakk>
         \<Longrightarrow> on_new_root param v0 s' \<le>\<^sub>n 
             SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                         \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes finish: "\<And>s s' u. 
      \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
       stack s \<noteq> []; u = hd (stack s); 
       pending s `` {u} = {};
       s' = finish u s\<rbrakk>
         \<Longrightarrow> on_finish param u s' \<le>\<^sub>n 
              SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                        \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes cross_edge: "\<And>s s' u v.
       \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
        stack s \<noteq> []; (u, v) \<in> pending s; u = hd (stack s); 
        v \<in> dom (discovered s); v\<in>dom (finished s);
        s' = cross_edge u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>)\<rbrakk>
       \<Longrightarrow> on_cross_edge param u v s' \<le>\<^sub>n
           SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                      \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes back_edge: "\<And>s s' u v.
       \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
        stack s \<noteq> []; (u, v) \<in> pending s; u = hd (stack s); 
        v \<in> dom (discovered s); v\<notin>dom (finished s);
        s' = back_edge u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>)\<rbrakk>
       \<Longrightarrow> on_back_edge param u v s' \<le>\<^sub>n
           SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>) 
                      \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes discover: "\<And>s s' u v.
       \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
        stack s \<noteq> [];  (u, v) \<in> pending s; u = hd (stack s); 
        v \<notin> dom (discovered s);
        s' = discover u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>)\<rbrakk>
       \<Longrightarrow> on_discover param u v s' \<le>\<^sub>n
           SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                      \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    shows "is_invar I"
    unfolding is_invar_def
  proof
    show "init \<le>\<^sub>n SPEC I"
      unfolding init_def
      by (refine_rcg refine_vcg) (simp add: init)
  next
    fix s
    assume "rwof init cond step s" and IC: "I s" "cond s"
    hence DI: "DFS_invar G param s" by unfold_locales
    then interpret DFS_invar G param s .

    from \<open>cond s\<close> have IB: "\<not> is_break param s" by (simp add: cond_def)

    have B: "step s \<le>\<^sub>n SPEC (DFS_invar G param)"
      by rule (metis DFS_invar_step' DI \<open>cond s\<close>)

    note rule_assms = DI IC IB

    show "step s \<le>\<^sub>n SPEC I"
      apply (rule leof_use_spec_rule[OF B])
      unfolding step_def do_defs pred_defs get_pending_def get_new_root_def
      apply (refine_rcg refine_vcg)
      apply (simp_all)

      apply (blast intro: new_root[OF rule_assms])
      apply (blast intro: finish[OF rule_assms])
      apply (rule cross_edge[OF rule_assms], auto) []
      apply (rule back_edge[OF rule_assms], auto) []
      apply (rule discover[OF rule_assms], auto) []
      done
  qed

  lemma establish_invarI'[case_names init new_root finish cross_edge back_edge discover]:
    \<comment> \<open>Establish a DFS invariant (symbolic preconditions).\<close>
    assumes init: "on_init param \<le>\<^sub>n SPEC (\<lambda>x. I (empty_state x))"
    assumes new_root: "\<And>s' v0. pre_on_new_root v0 s'
         \<Longrightarrow> on_new_root param v0 s' \<le>\<^sub>n 
             SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                         \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes finish: "\<And>s' u. pre_on_finish u s' 
         \<Longrightarrow> on_finish param u s' \<le>\<^sub>n 
              SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                        \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes cross_edge: "\<And>s' u v. pre_on_cross_edge u v s'
       \<Longrightarrow> on_cross_edge param u v s' \<le>\<^sub>n
           SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                      \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes back_edge: "\<And>s' u v. pre_on_back_edge u v s'
       \<Longrightarrow> on_back_edge param u v s' \<le>\<^sub>n
           SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>) 
                      \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes discover: "\<And>s' u v. pre_on_discover u v s'
       \<Longrightarrow> on_discover param u v s' \<le>\<^sub>n
           SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                      \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    shows "is_invar I"
    apply (rule establish_invarI)
    using assms
    unfolding pre_on_defs
    apply -
    apply blast
    apply (rprems,blast)+
    done
  
  lemma establish_invarI_ND [case_names prereq init new_discover finish cross_edge back_edge]:
    \<comment> \<open>Establish a DFS invariant (new-root and discover cases are combined).\<close>
    assumes prereq: "\<And>u v s. on_discover param u v s = on_new_root param v s"
    assumes init: "on_init param \<le>\<^sub>n SPEC (\<lambda>x. I (empty_state x))"
    assumes new_discover: "\<And>s s' v. 
      \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
       v \<notin> dom (discovered s); 
       discovered s' = (discovered s)(v\<mapsto>counter s); finished s' = finished s;
       counter s' = Suc (counter s); stack s' = v#stack s;
       back_edges s' = back_edges s; cross_edges s' = cross_edges s;
       tree_edges s' \<supseteq> tree_edges s;
       state.more s' = state.more s\<rbrakk>
         \<Longrightarrow> on_new_root param v s' \<le>\<^sub>n 
             SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                         \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes finish: "\<And>s s' u. 
      \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
       stack s \<noteq> []; u = hd (stack s); 
       pending s `` {u} = {};
       s' = finish u s\<rbrakk>
         \<Longrightarrow> on_finish param u s' \<le>\<^sub>n 
              SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                        \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes cross_edge: "\<And>s s' u v.
       \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
        stack s \<noteq> []; (u, v) \<in> pending s; u = hd (stack s); 
        v \<in> dom (discovered s); v\<in>dom (finished s);
        s' = cross_edge u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>)\<rbrakk>
       \<Longrightarrow> on_cross_edge param u v s' \<le>\<^sub>n
           SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                      \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes back_edge: "\<And>s s' u v.
       \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
        stack s \<noteq> []; (u, v) \<in> pending s; u = hd (stack s); 
        v \<in> dom (discovered s); v\<notin>dom (finished s);
        s' = back_edge u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>)\<rbrakk>
       \<Longrightarrow> on_back_edge param u v s' \<le>\<^sub>n
           SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>) 
                        \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    shows "is_invar I"
  proof (induct rule: establish_invarI)
    case (new_root s) thus ?case by (auto intro!: new_discover)
  next
    case (discover s s' u v) hence
      "on_new_root param v s' \<le>\<^sub>n 
        SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                   \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
      by (auto intro!: new_discover)
    with prereq show ?case by simp
  qed fact+

  (* Variant of establish_invarI, where cross_edge and back_edge are combined *)
  lemma establish_invarI_CB [case_names prereq init new_root finish cross_back_edge discover]:
    \<comment> \<open>Establish a DFS invariant (cross and back edge cases are combined).\<close>
    assumes prereq: "\<And>u v s. on_back_edge param u v s = on_cross_edge param u v s"
    assumes init: "on_init param \<le>\<^sub>n SPEC (\<lambda>x. I (empty_state x))"
    assumes new_root: "\<And>s s' v0. 
      \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
       stack s = []; v0 \<in> V0; v0 \<notin> dom (discovered s);
        s' = new_root v0 s\<rbrakk>
         \<Longrightarrow> on_new_root param v0 s' \<le>\<^sub>n 
             SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                         \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes finish: "\<And>s s' u. 
      \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
       stack s \<noteq> []; u = hd (stack s); 
       pending s `` {u} = {};
       s' = finish u s\<rbrakk>
         \<Longrightarrow> on_finish param u s' \<le>\<^sub>n 
              SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                        \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes cross_back_edge: "\<And>s s' u v.
       \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
        stack s \<noteq> []; (u, v) \<in> pending s; u = hd (stack s); 
        v \<in> dom (discovered s);
        discovered s' = discovered s; finished s' = finished s;
        stack s' = stack s; tree_edges s' = tree_edges s; counter s' = counter s;
        pending s' = pending s - {(u,v)};
        cross_edges s' \<union> back_edges s' = cross_edges s \<union> back_edges s \<union> {(u,v)};
        state.more s' = state.more s \<rbrakk>
       \<Longrightarrow> on_cross_edge param u v s' \<le>\<^sub>n
           SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                      \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes discover: "\<And>s s' u v.
       \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
        stack s \<noteq> [];  (u, v) \<in> pending s; u = hd (stack s); 
        v \<notin> dom (discovered s);
        s' = discover u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>)\<rbrakk>
       \<Longrightarrow> on_discover param u v s' \<le>\<^sub>n
           SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                      \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    shows "is_invar I"
  proof (induct rule: establish_invarI)
    case cross_edge thus ?case by (auto intro!: cross_back_edge)
  next
    case (back_edge s s' u v) hence
      "on_cross_edge param u v s' \<le>\<^sub>n 
             SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                         \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
      by (auto intro!: cross_back_edge)
    with prereq show ?case by simp
  qed fact+

  (* Variant of establish_invarI, where cross_edge and back_edge, and discover and new_root are combined *)
  lemma establish_invarI_ND_CB [case_names prereq_ND prereq_CB init new_discover finish cross_back_edge]:
    \<comment> \<open>Establish a DFS invariant (new-root/discover and cross/back-edge cases are combined).\<close>
    assumes prereq: 
        "\<And>u v s. on_discover param u v s = on_new_root param v s"
        "\<And>u v s. on_back_edge param u v s = on_cross_edge param u v s"
    assumes init: "on_init param \<le>\<^sub>n SPEC (\<lambda>x. I (empty_state x))"
    assumes new_discover: "\<And>s s' v. 
     \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
      v \<notin> dom (discovered s); 
      discovered s' = (discovered s)(v\<mapsto>counter s); finished s' = finished s;
      counter s' = Suc (counter s); stack s' = v#stack s;
      back_edges s' = back_edges s; cross_edges s' = cross_edges s;
      tree_edges s' \<supseteq> tree_edges s;
      state.more s' = state.more s\<rbrakk>
        \<Longrightarrow> on_new_root param v s' \<le>\<^sub>n 
            SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                        \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes finish: "\<And>s s' u. 
      \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
       stack s \<noteq> []; u = hd (stack s); 
       pending s `` {u} = {};
       s' = finish u s\<rbrakk>
         \<Longrightarrow> on_finish param u s' \<le>\<^sub>n 
              SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                        \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    assumes cross_back_edge: "\<And>s s' u v.
       \<lbrakk>DFS_invar G param s; I s; cond s; \<not> is_break param s;
        stack s \<noteq> []; (u, v) \<in> pending s; u = hd (stack s); 
        v \<in> dom (discovered s);
        discovered s' = discovered s; finished s' = finished s;
        stack s' = stack s; tree_edges s' = tree_edges s; counter s' = counter s;
        pending s' = pending s - {(u,v)};
        cross_edges s' \<union> back_edges s' = cross_edges s \<union> back_edges s \<union> {(u,v)};
        state.more s' = state.more s \<rbrakk>
       \<Longrightarrow> on_cross_edge param u v s' \<le>\<^sub>n
           SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                      \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
    shows "is_invar I"
  proof (induct rule: establish_invarI_ND)
    case cross_edge thus ?case by (auto intro!: cross_back_edge)
  next
    case (back_edge s s' u v) hence
      "on_cross_edge param u v s' \<le>\<^sub>n 
             SPEC (\<lambda>x. DFS_invar G param (s'\<lparr>state.more := x\<rparr>)
                         \<longrightarrow> I (s'\<lparr>state.more := x\<rparr>))"
      by (auto intro!: cross_back_edge)
    with prereq show ?case by simp
  qed fact+


  lemma is_invarI_full [case_names init new_root finish cross_edge back_edge discover]:
    \<comment> \<open>Establish a DFS invariant not taking into account the parameterization.\<close>
    assumes init: "\<And>e. I (empty_state e)"
    assumes new_root: "\<And>s s' v0 e. 
       \<lbrakk>I s; cond s; DFS_invar G param s; DFS_invar G param s';
        stack s = []; v0 \<notin> dom (discovered s); v0 \<in> V0;
        s' = new_root v0 s\<lparr>state.more := e\<rparr>\<rbrakk> 
      \<Longrightarrow> I s'"
    and finish: "\<And>s s' u e. 
       \<lbrakk>I s; cond s; DFS_invar G param s; DFS_invar G param s';
        stack s \<noteq> []; pending s `` {u} = {};
        u = hd (stack s); s' = finish u s\<lparr>state.more := e\<rparr>\<rbrakk> 
       \<Longrightarrow> I s'"
    and cross_edge: "\<And>s s' u v e.
       \<lbrakk>I s; cond s; DFS_invar G param s; DFS_invar G param s';
        stack s \<noteq> []; v \<in> pending s `` {u}; v \<in> dom (discovered s); 
        v \<in> dom (finished s);
        u = hd (stack s); 
        s' = (cross_edge u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>))\<lparr>state.more := e\<rparr>\<rbrakk>
       \<Longrightarrow> I s'"
    and back_edge: "\<And>s s' u v e.
       \<lbrakk>I s; cond s; DFS_invar G param s; DFS_invar G param s';
        stack s \<noteq> []; v \<in> pending s `` {u}; v \<in> dom (discovered s); v \<notin> dom (finished s); 
        u = hd (stack s); 
        s' = (back_edge u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>))\<lparr>state.more := e\<rparr>\<rbrakk>
       \<Longrightarrow> I s'"
    and discover: "\<And>s s' u v e.
       \<lbrakk>I s; cond s; DFS_invar G param s; DFS_invar G param s';
        stack s \<noteq> []; v \<in> pending s `` {u}; v \<notin> dom (discovered s); 
        u = hd (stack s); 
        s' = (discover u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>))\<lparr>state.more := e\<rparr>\<rbrakk>
       \<Longrightarrow> I s'"
  shows "is_invar I"
  apply (rule establish_invarI) 
  apply (blast intro: indep_invar_rules assms)+
  done

  lemma is_invarI [case_names init new_root finish visited discover]:
    \<comment> \<open>Establish a DFS invariant not taking into account the parameterization, cross/back-edges combined.\<close>
    assumes init': "\<And>e. I (empty_state e)"
    and new_root': "\<And>s s' v0 e. 
       \<lbrakk>I s; cond s; DFS_invar G param s; DFS_invar G param s';
        stack s = []; v0 \<notin> dom (discovered s); v0 \<in> V0;
        s' = new_root v0 s\<lparr>state.more := e\<rparr>\<rbrakk> 
      \<Longrightarrow> I s'"
    and finish': "\<And>s s' u e. 
       \<lbrakk>I s; cond s; DFS_invar G param s; DFS_invar G param s';
        stack s \<noteq> []; pending s `` {u} = {};
        u = hd (stack s); s' = finish u s\<lparr>state.more := e\<rparr>\<rbrakk> 
       \<Longrightarrow> I s'"
    and visited': "\<And>s s' u v e c b.
       \<lbrakk>I s; cond s; DFS_invar G param s; DFS_invar G param s';
        stack s \<noteq> []; v \<in> pending s `` {u}; v \<in> dom (discovered s);
        u = hd (stack s);
        cross_edges s \<subseteq> c; back_edges s \<subseteq> b;
        s' = s\<lparr> 
          pending := pending s - {(u,v)},
          state.more := e, 
          cross_edges := c, 
          back_edges := b\<rparr>\<rbrakk>
       \<Longrightarrow> I s'"
    and discover': "\<And>s s' u v e.
       \<lbrakk>I s; cond s;  DFS_invar G param s; DFS_invar G param s';
        stack s \<noteq> []; v \<in> pending s `` {u}; v \<notin> dom (discovered s); 
        u = hd (stack s); 
        s' = (discover u v (s\<lparr>pending := pending s - {(u,v)}\<rparr>))\<lparr>state.more := e\<rparr>\<rbrakk>
       \<Longrightarrow> I s'"
    shows "is_invar I"
  proof (induct rule: is_invarI_full)
    case (cross_edge s s' u v e) thus ?case
      apply -
      apply (rule visited'[of s s' v u "insert (u,v) (cross_edges s)" "back_edges s" e])
      apply clarsimp_all
      done
  next
    case (back_edge s s' u v e) thus ?case
      apply -
      apply (rule visited'[of s s' v u "cross_edges s" "insert (u,v) (back_edges s)" e])
      apply clarsimp_all
      done
  qed fact+

end

subsection \<open>Basic Invariants\<close>
text \<open>We establish some basic invariants\<close>

context param_DFS begin
  (* Establish some invariants *)
  definition "basic_invar s \<equiv>
    set (stack s) = dom (discovered s) - dom (finished s) \<and>
    distinct (stack s) \<and>
    (stack s \<noteq> [] \<longrightarrow> last (stack s) \<in> V0) \<and>
    dom (finished s) \<subseteq> dom (discovered s) \<and>
    Domain (pending s) \<subseteq> dom (discovered s) - dom (finished s) \<and>
    pending s \<subseteq> E"

  lemma i_basic_invar: "is_invar basic_invar" 
    unfolding basic_invar_def[abs_def]
    apply (induction rule: is_invarI)
    apply (clarsimp_all simp: neq_Nil_conv last_tl)
    apply blast+
    done
end

context DFS_invar begin
  lemmas basic_invar = make_invar_thm[OF i_basic_invar]

  lemma pending_ssE: "pending s \<subseteq> E" 
    using basic_invar 
    by (auto simp: basic_invar_def)

  lemma pendingD:
    "(u,v)\<in>pending s \<Longrightarrow> (u,v)\<in>E \<and> u\<in>dom (discovered s)"
    using basic_invar 
    by (auto simp: basic_invar_def)

  lemma stack_set_def:
    "set (stack s) = dom (discovered s) - dom (finished s)"
    using basic_invar
    by (simp add: basic_invar_def)

  lemma stack_discovered:
    "set (stack s) \<subseteq> dom (discovered s)"
    using stack_set_def
    by auto

  lemma stack_distinct:
    "distinct (stack s)"
    using basic_invar
    by (simp add: basic_invar_def)

  lemma last_stack_in_V0:
    "stack s \<noteq> [] \<Longrightarrow> last (stack s) \<in> V0"
    using basic_invar
    by (simp add: basic_invar_def)

  lemma stack_not_finished:
    "x \<in> set (stack s) \<Longrightarrow> x \<notin> dom (finished s)"
    using stack_set_def
    by auto

  lemma discovered_not_stack_imp_finished:
    "x \<in> dom (discovered s) \<Longrightarrow> x \<notin> set (stack s) \<Longrightarrow> x \<in> dom (finished s)"
    using stack_set_def
    by auto

  lemma finished_discovered:
    "dom (finished s) \<subseteq> dom (discovered s)"
    using basic_invar
    by (auto simp add: basic_invar_def)

  lemma finished_no_pending:
    "v \<in> dom (finished s) \<Longrightarrow> pending s `` {v} = {}"
    using basic_invar
    by (auto simp add: basic_invar_def)

  lemma discovered_eq_finished_un_stack:
    "dom (discovered s) = dom (finished s) \<union> set (stack s)"
    using stack_set_def finished_discovered by auto


  lemma pending_on_stack:
    "(v,w) \<in> pending s \<Longrightarrow> v \<in> set (stack s)"
    using basic_invar
    by (auto simp add: basic_invar_def)

  lemma empty_stack_imp_empty_pending:
    "stack s = [] \<Longrightarrow> pending s = {}"
    using pending_on_stack
    by auto
end


context param_DFS begin

(* Establish some more invariants *)
  lemma i_discovered_reachable: 
    "is_invar (\<lambda>s. dom (discovered s) \<subseteq> reachable)"
  proof (induct rule: is_invarI)
    case (discover s) then interpret i: DFS_invar where s=s by simp
    from discover show ?case 
      apply (clarsimp dest!: i.pendingD)
      by (metis contra_subsetD list.set_sel(1) rtrancl_image_advance i.stack_discovered)
  qed auto

  definition "discovered_closed s \<equiv>
      E``dom (finished s) \<subseteq> dom (discovered s)
    \<and> (E - pending s) `` set (stack s) \<subseteq> dom (discovered s)"

  lemma i_discovered_closed: "is_invar discovered_closed"
  proof (induct rule: is_invarI)
    case (finish s s') 
    hence "(E - pending s) `` set (stack s) \<subseteq> dom (discovered s)" 
      by (simp add: discovered_closed_def)
    moreover from finish have "set (stack s') \<subseteq> set (stack s)" 
      by (auto simp add: neq_Nil_conv cond_def)
    ultimately have "(E - pending s') `` set (stack s') \<subseteq> dom (discovered s')"
      using finish
      by simp blast

    moreover
    from \<open>stack s \<noteq> []\<close> finish have "E``dom (finished s') \<subseteq> dom (discovered s')" 
      apply (cases "stack s") apply simp
      apply (simp add: discovered_closed_def) 
      apply (blast)
      done
    ultimately show ?case by (simp add: discovered_closed_def)
  qed (auto simp add: discovered_closed_def cond_def)

  lemma i_discovered_finite: "is_invar (\<lambda>s. finite (dom (discovered s)))"
    by (induction rule: is_invarI) auto

end

context DFS_invar
begin

  lemmas discovered_reachable = 
    i_discovered_reachable [THEN make_invar_thm]

  lemma stack_reachable: "set (stack s) \<subseteq> reachable" 
    using stack_discovered discovered_reachable by blast

  lemmas discovered_closed = i_discovered_closed[THEN make_invar_thm]

  lemmas discovered_finite[simp, intro!] = i_discovered_finite[THEN make_invar_thm]
  lemma finished_finite[simp, intro!]: "finite (dom (finished s))"
    using finished_discovered discovered_finite by (rule finite_subset)

  lemma finished_closed:
    "E `` dom (finished s) \<subseteq> dom (discovered s)"
    using discovered_closed[unfolded discovered_closed_def]
    by auto

  lemma finished_imp_succ_discovered:
    "v \<in> dom (finished s) \<Longrightarrow> w \<in> succ v \<Longrightarrow> w \<in> dom (discovered s)"
    using discovered_closed[unfolded discovered_closed_def]
    by auto

  lemma pending_reachable: "pending s \<subseteq> reachable \<times> reachable" 
    using pendingD discovered_reachable
    by (fast intro: rtrancl_image_advance_rtrancl)

  lemma pending_finite[simp, intro!]: "finite (pending s)"
  proof -
    have "pending s \<subseteq> (SIGMA u:dom (discovered s). E``{u})"
      by (auto dest: pendingD)
    also have "finite \<dots>"
      apply rule
      apply (rule discovered_finite)
      using discovered_reachable
      by (blast intro: finitely_branching)
    finally (finite_subset) show ?thesis .
  qed

  lemma no_pending_imp_succ_discovered:
    assumes "u \<in> dom (discovered s)"
    and "pending s `` {u} = {}"
    and "v \<in> succ u"
    shows "v \<in> dom (discovered s)"
  proof (cases "u \<in> dom (finished s)")
    case True with finished_imp_succ_discovered assms show ?thesis by simp
  next
    case False with stack_set_def assms have "u \<in> set (stack s)" by auto
    with assms discovered_closed[unfolded discovered_closed_def] show ?thesis by blast
  qed

  lemma nc_finished_eq_reachable:
    assumes NC: "\<not>cond s" "\<not>is_break param s" 
    shows "dom (finished s) = reachable"
  proof -
    from NC basic_invar 
    have [simp]: "stack s = []" "dom (discovered s) = dom (finished s)" and SS: "V0 \<subseteq> dom (discovered s)"
      unfolding basic_invar_def cond_alt by auto

    show "dom (finished s) = reachable"
    proof 
      from discovered_reachable show "dom (finished s) \<subseteq> reachable"
        by simp
    next
      from discovered_closed have "E``(dom (finished s)) \<subseteq> dom (finished s)"
        unfolding discovered_closed_def by auto
      with SS show "reachable \<subseteq> dom (finished s)"
        by (simp, metis rtrancl_reachable_induct)
    qed
  qed

  lemma nc_V0_finished:
    assumes NC: "\<not> cond s" "\<not> is_break param s"
    shows "V0 \<subseteq> dom (finished s)"
    using nc_finished_eq_reachable[OF NC]
    by blast 

  lemma nc_discovered_eq_finished:
    assumes NC: "\<not> cond s" "\<not> is_break param s"
    shows "dom (discovered s) = dom (finished s)"
    using finished_discovered
    using nc_finished_eq_reachable[OF NC] discovered_reachable
    by blast

  lemma nc_discovered_eq_reachable:
    assumes NC: "\<not> cond s" "\<not> is_break param s"
    shows "dom (discovered s) = reachable"
    using NC
    using nc_discovered_eq_finished nc_finished_eq_reachable
    by blast

  lemma nc_fin_closed: 
    assumes NC: "\<not>cond s"
    assumes NB: "\<not>is_break param s"
    shows "E``dom (finished s) \<subseteq> dom (finished s)"
    using finished_imp_succ_discovered
    by (auto simp: nc_discovered_eq_finished[OF NC NB])

end

subsection \<open>Total Correctness\<close>
text \<open>We can show termination of the DFS algorithm, independently of the parameterization\<close>

context param_DFS begin
  definition "param_dfs_variant \<equiv> inv_image 
    (finite_psupset reachable <*lex*> finite_psubset <*lex*> less_than)
    (\<lambda>s. (dom (discovered s), pending s, length (stack s)))"

  lemma param_dfs_variant_wf[simp, intro!]:
    assumes [simp, intro!]: "finite reachable"
    shows "wf param_dfs_variant"  
    unfolding param_dfs_variant_def
    by auto

  lemma param_dfs_variant_step:   
    assumes A: "DFS_invar G param s" "cond s" "nofail it_dfs"
    shows "step s \<le> SPEC (\<lambda>s'. (s',s)\<in>param_dfs_variant)"
  proof -
    interpret DFS_invar G param s by fact

    from A show ?thesis
      unfolding rwof_eq_DFS_invar[symmetric] it_dfs_def
      apply -
      apply (drule (2) WHILE_nofail_imp_rwof_nofail)
      unfolding step_def get_new_root_def do_defs get_pending_def
      unfolding param_dfs_variant_def
      apply refine_vcg
      using discovered_reachable (* TODO: Clean, up. *) 
        (* FIXME: auto-steps take loooong *)
      apply (auto 
        split: option.splits 
        simp: refine_pw_simps pw_le_iff is_discovered_def finite_psupset_def
      ) [1]
      apply (auto simp: refine_pw_simps pw_le_iff is_empty_stack_def) []
      apply simp_all

      apply (auto 
        simp: refine_pw_simps pw_le_iff is_discovered_def
        split: if_split_asm
        ) [2]

      apply (clarsimp simp: refine_pw_simps pw_le_iff is_discovered_def)
      using discovered_reachable pending_reachable
      apply (auto
        simp: is_discovered_def
        simp: refine_pw_simps pw_le_iff finite_psupset_def
        split: if_split_asm)
      done
  qed

  
end


context param_DFS begin
  lemma it_dfsT_eq_it_dfs:
    assumes [simp, intro!]: "finite reachable"
    shows "it_dfsT = it_dfs"
  proof -
    have "it_dfs \<le> it_dfsT" 
      unfolding it_dfs_def it_dfsT_def WHILE_def WHILET_def
      apply (rule bind_mono)
      apply simp
      apply (rule WHILEI_le_WHILEIT)
      done
    also have "it_dfsT \<le> it_dfs"
    proof (cases "nofail it_dfs")
      case False thus ?thesis by (simp add: not_nofail_iff)
    next
      case True

      show ?thesis
        unfolding it_dfsT_def it_dfs_def
        apply (rule bind_mono)
        apply simp
        apply (subst WHILET_eq_WHILE_tproof[
          where I="DFS_invar G param"
          and V="param_dfs_variant"
          ])
        apply auto []

        apply (subst rwof_eq_DFS_invar[symmetric])
        using rwof_init[OF True[unfolded it_dfs_def]]
        apply (fastforce dest: order_trans) []
        
        apply (rule SPEC_rule_conjI)
          apply (rule DFS_invar_step[OF True], assumption+) []
          apply (rule param_dfs_variant_step, (assumption|rule True)+) []
        
        apply simp
        done
    qed
    finally show ?thesis by simp
  qed
end

subsection \<open>Non-Failing Parameterization\<close>
text \<open>
  The proofs so far have been done modulo failure of the parameterization.
  In this locale, we assume that the parameterization does not fail,
  and derive the correctness proof of the DFS algorithm wrt. its invariant.
\<close>
(* Locale that assumes that parameterization does not fail *)
locale DFS =
  param_DFS G param
  for G :: "('v, 'more) graph_rec_scheme"
  and param :: "('v,'es) parameterization"
  +
  assumes nofail_on_init: 
    "nofail (on_init param)"

  assumes nofail_on_new_root:
    "pre_on_new_root v0 s \<Longrightarrow> nofail (on_new_root param v0 s)"

  assumes nofail_on_finish: 
    "pre_on_finish u s \<Longrightarrow> nofail (on_finish param u s)"

  assumes nofail_on_cross_edge: 
    "pre_on_cross_edge u v s \<Longrightarrow> nofail (on_cross_edge param u v s)"

  assumes nofail_on_back_edge: 
    "pre_on_back_edge u v s \<Longrightarrow> nofail (on_back_edge param u v s)"

  assumes nofail_on_discover: 
    "pre_on_discover u v s \<Longrightarrow> nofail (on_discover param u v s)"

begin
  lemmas nofails = nofail_on_init nofail_on_new_root nofail_on_finish 
    nofail_on_cross_edge nofail_on_back_edge nofail_on_discover


  lemma init_leof_invar: "init \<le>\<^sub>n SPEC (DFS_invar G param)"
    unfolding rwof_eq_DFS_invar[symmetric]
    by (rule rwof_leof_init)

  lemma it_dfs_eq_spec: "it_dfs = SPEC (\<lambda>s. DFS_invar G param s \<and> \<not>cond s)"
    unfolding rwof_eq_DFS_invar[symmetric] it_dfs_def
    apply (rule nofail_WHILE_eq_rwof)
    apply (subst WHILE_eq_I_rwof)
    unfolding rwof_eq_DFS_invar
    apply (rule SPEC_nofail[where \<Phi>="\<lambda>_. True"])
    apply (refine_vcg leofD[OF _ init_leof_invar, THEN weaken_SPEC])
    apply (simp add: init_def refine_pw_simps nofail_on_init)
    apply (rule DFS_invar_step')
    apply (simp add: step_def refine_pw_simps nofail_on_init do_defs 
      get_pending_def get_new_root_def pred_defs
      split: option.split)
    apply (intro allI conjI impI nofails)
    apply (auto simp add: pre_on_defs)
    done

  lemma it_dfs_correct: "it_dfs \<le> SPEC (\<lambda>s. DFS_invar G param s \<and> \<not>cond s)"
    by (simp add: it_dfs_eq_spec)

  lemma it_dfs_SPEC:
    assumes "\<And>s. \<lbrakk>DFS_invar G param s; \<not>cond s\<rbrakk> \<Longrightarrow> P s"
    shows "it_dfs \<le> SPEC P"
    using weaken_SPEC[OF it_dfs_correct]
    using assms
    by blast

  lemma it_dfsT_correct: 
    assumes "finite reachable"
    shows "it_dfsT \<le> SPEC (\<lambda>s. DFS_invar G param s \<and> \<not>cond s)"
    apply (subst it_dfsT_eq_it_dfs[OF assms])
    by (rule it_dfs_correct)

  lemma it_dfsT_SPEC:
    assumes "finite reachable"
    assumes "\<And>s. \<lbrakk>DFS_invar G param s; \<not>cond s\<rbrakk> \<Longrightarrow> P s"
    shows "it_dfsT \<le> SPEC P"
    apply (subst it_dfsT_eq_it_dfs[OF assms(1)])
    using assms(2)
    by (rule it_dfs_SPEC)

end

end
