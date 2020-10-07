section "Invariants for Promela data structures"
theory PromelaInvariants
imports PromelaDatastructures
begin

text \<open>
  The different data structures used in the Promela implementation require different invariants,
  which are specified in this file. As there is no (useful) way of specifying \emph{correctness} of the implementation,
those invariants are tailored towards proving the finitness of the generated state-space. 
\<close>

(*<*)
(*subsection {* Auxiliary lemmas *}*)
lemma foldli_set:
  "set (foldli list (\<lambda>_. True) (#) xs) = set xs \<union> set list"
  by (induct list arbitrary: xs) simp_all

lemma foldli_conj:
  "foldli list id (\<lambda>kv \<sigma>. P kv) b \<longleftrightarrow> b \<and> (\<forall>x \<in> set list. P x)"
  by (induct list arbitrary: b) simp_all

(* Destroy the evil border of abstraction... *)
lemma lm_ball_Assoc_List_set:
  "lm.ball m P \<longleftrightarrow> (\<forall>x \<in> Assoc_List.set m. P x)"
  unfolding Assoc_List.set_def
  by (simp add: icf_rec_unf lm_basic.g_ball_def 
    poly_map_iteratei_defs.iteratei_def it_to_it_def Assoc_List.iteratei_def
    foldli_conj)

lemma lm_to_list_Assoc_List_set:
  "set (lm.to_list l) = Assoc_List.set l"
  unfolding Assoc_List.set_def
  by (simp add: icf_rec_unf lm_basic.g_to_list_def 
    poly_map_iteratei_defs.iteratei_def it_to_it_def Assoc_List.iteratei_def 
    foldli_set)

lemma dom_lm_\<alpha>_Assoc_List_set:
  "dom (lm.\<alpha> v) = fst ` (Assoc_List.set v)"
  by (simp add: icf_rec_unf Assoc_List.lookup_def Assoc_List.set_def
    dom_map_of_conv_image_fst)

lemma ran_lm_\<alpha>_Assoc_List_set:
  "ran (lm.\<alpha> v) = snd ` (Assoc_List.set v)"
  by (simp add: icf_rec_unf Assoc_List.lookup_def Assoc_List.set_def 
    ran_distinct)

lemma lm_ball_eq_ran:
  "lm.ball v (\<lambda>(k,v). P v) \<longleftrightarrow> ran (lm.\<alpha> v) \<subseteq> Collect P"
  by (auto simp add: ran_lm_\<alpha>_Assoc_List_set lm_ball_Assoc_List_set)

lemma lm_ball_lm_to_map_map_weaken:
  "\<forall>x \<in> f ` set xs. P x \<Longrightarrow> lm.ball (lm.to_map (map f xs)) P"
  by (induct xs) (simp_all add: lm.correct)

lemma Assoc_List_set_eq_lookup:
  "(k,v) \<in> Assoc_List.set vs \<longleftrightarrow> Assoc_List.lookup vs k = Some v"
  by (simp add: Assoc_List.lookup_def Assoc_List.set_def) 

(*>*)

subsection \<open>Bounds\<close>

text \<open>
  Finiteness requires that possible variable ranges are finite, as is the maximium number of processes.
  Currently, they are supplied here as constants. In a perfect world, they should be able to be set dynamically. 
\<close>

(* NB! Make sure those values coincide with the bounds definied in @{const ppVarType} *)
definition min_var_value :: "integer" where
  "min_var_value = -(2^31)"
definition max_var_value :: "integer" where
  "max_var_value = (2^31) - 1"

lemma min_max_var_value_simps [simp, intro!]:
  "min_var_value < max_var_value"
  "min_var_value < 0"
  "min_var_value \<le> 0"
  "max_var_value > 0"
  "max_var_value \<ge> 0"
by (simp_all add: min_var_value_def max_var_value_def)

definition "max_procs \<equiv> 255"
definition "max_channels \<equiv> 65535"
definition "max_array_size = 65535"


subsection \<open>Variables and similar\<close>

fun varType_inv :: "varType \<Rightarrow> bool" where
  "varType_inv (VTBounded l h) 
  \<longleftrightarrow> l \<ge> min_var_value \<and> h \<le> max_var_value \<and> l < h"
| "varType_inv VTChan \<longleftrightarrow> True"

fun variable_inv :: "variable \<Rightarrow> bool" where
  "variable_inv (Var t val) 
  \<longleftrightarrow> varType_inv t \<and> val \<in> {min_var_value..max_var_value}"
| "variable_inv (VArray t sz ar) 
  \<longleftrightarrow> varType_inv t 
    \<and> sz \<le> max_array_size 
    \<and> IArray.length ar = sz 
    \<and> set (IArray.list_of ar) \<subseteq> {min_var_value..max_var_value}"

fun channel_inv :: "channel \<Rightarrow> bool" where
  "channel_inv (Channel cap ts q) 
  \<longleftrightarrow> cap \<le> max_array_size 
    \<and> cap \<ge> 0 
    \<and> set ts \<subseteq> Collect varType_inv 
    \<and> length ts \<le> max_array_size 
    \<and> length q \<le> max_array_size 
    \<and> (\<forall>x \<in> set q. length x = length ts 
    \<and> set x \<subseteq> {min_var_value..max_var_value})"
| "channel_inv (HSChannel ts) 
  \<longleftrightarrow> set ts \<subseteq> Collect varType_inv \<and> length ts \<le> max_array_size"
| "channel_inv InvChannel \<longleftrightarrow> True"

lemma varTypes_finite:
  "finite (Collect varType_inv)"
proof (rule finite_subset)
  show "Collect (varType_inv) \<subseteq> 
      {VTChan} 
    \<union> (\<lambda>(l,h). VTBounded l h) 
      ` ({min_var_value..max_var_value} \<times> {min_var_value..max_var_value})"
    apply (rule subsetI)
    apply (case_tac x)
      apply auto
    done

  show "finite ..." by auto
qed

lemma variables_finite:
  "finite (Collect variable_inv)"
proof (rule finite_subset)
  let ?mm = "{min_var_value..max_var_value}"
  let ?V1 = "(\<lambda>(t,val). Var t val) ` ({vt. varType_inv vt} \<times> ?mm)"
  let ?V2 = "(\<lambda>(t,sz,ar). VArray t sz ar) 
    ` ({vt. varType_inv vt} 
      \<times> {0..max_array_size} 
      \<times> {ar. IArray.length ar \<le> max_array_size 
           \<and> set (IArray.list_of ar) \<subseteq> ?mm})"

  {
    fix A :: "'a set"
    let ?LS = "{xs. set xs \<subseteq> A \<and> length xs \<le> max_array_size }"
    let ?AS = "{ar. IArray.length ar \<le> max_array_size 
      \<and> set (IArray.list_of ar) \<subseteq> A}"

    assume "finite A"
    hence "finite ?LS" by (simp add: finite_lists_length_le)
    moreover have "?AS \<subseteq> IArray ` ?LS"
      apply (auto simp: image_def)
      apply (rule_tac x = "IArray.list_of x" in exI)
      apply auto
      apply (metis iarray.exhaust list_of.simps)
      done
    ultimately have "finite ?AS" by (auto simp add: finite_subset)
  } note finite_arr = this

  show "Collect variable_inv \<subseteq> (?V1 \<union> ?V2)"
    apply (rule subsetI)
    apply (case_tac x)
      apply (auto simp add: image_def)
    done

  show "finite ..." by (blast intro: varTypes_finite finite_arr)
qed

lemma channels_finite:
  "finite (Collect channel_inv)"
proof (rule finite_subset)
  let ?C1 = 
    "(\<lambda>(cap,ts,q). Channel cap ts q) 
     ` ({0..max_array_size} 
      \<times> {ts. set ts \<subseteq> Collect varType_inv \<and> length ts \<le> max_array_size} 
      \<times> {q. set q \<subseteq> {x. set x \<subseteq> {min_var_value..max_var_value} 
                        \<and> length x \<le> max_array_size} 
            \<and> length q \<le> max_array_size})"
  let ?C2 = 
    "HSChannel ` {ts. set ts \<subseteq> Collect varType_inv \<and> length ts \<le> max_array_size}"
  let ?C3 = "{InvChannel}"

  show "(Collect channel_inv) \<subseteq> ?C1 \<union> ?C2 \<union> ?C3"
    apply (rule subsetI)
    apply (case_tac x)
      apply (auto simp add: image_def)
    done

  show "finite ..." by (blast intro: finite_lists_length_le varTypes_finite)+
qed

text \<open>To give an upper bound of variable names, we need a way to calculate it.\<close>

primrec procArgName :: "procArg \<Rightarrow> String.literal" where
  "procArgName (ProcArg _ name) = name"

primrec varDeclName :: "varDecl \<Rightarrow> String.literal" where
  "varDeclName (VarDeclNum _ _ name _ _) = name"
| "varDeclName (VarDeclChan name _ _) = name"

primrec procVarDeclName :: "procVarDecl \<Rightarrow> String.literal" where
  "procVarDeclName (ProcVarDeclNum _ _ name _ _) = name"
| "procVarDeclName (ProcVarDeclChan name _) = name"

definition edgeDecls :: "edge \<Rightarrow> procVarDecl set" where
  "edgeDecls e = (
     case effect e of
      EEDecl p \<Rightarrow> {p}
    |  _ \<Rightarrow> {})" 

lemma edgeDecls_finite:
  "finite (edgeDecls e)"
by (simp add: edgeDecls_def split: edgeEffect.split)

definition edgeSet :: "states \<Rightarrow> edge set" where
  "edgeSet s = set (concat (map snd (IArray.list_of s)))"

lemma edgeSet_finite:
  "finite (edgeSet s)"
by (simp add: edgeSet_def)

definition statesDecls :: "states \<Rightarrow> procVarDecl set" where
  "statesDecls s = \<Union>(edgeDecls ` (edgeSet s))"

definition statesNames :: "states \<Rightarrow> String.literal set" where
  "statesNames s = procVarDeclName ` statesDecls s"

lemma statesNames_finite:
  "finite (statesNames s)"
by (simp add: edgeSet_finite edgeDecls_finite statesNames_def statesDecls_def)


fun process_names :: "states \<Rightarrow> process \<Rightarrow> String.literal set" where
  "process_names ss (_, _, args, decls) = 
      statesNames ss 
    \<union> procArgName ` set args 
    \<union> varDeclName ` set decls
    \<union> {STR ''_'', STR ''__assert__'', STR ''_pid''}" (* dunno if this is ok as a fixed set ... *)

lemma process_names_finite:
  "finite (process_names ss p)"
by (cases p) (simp add: statesNames_finite)

definition vardict_inv :: "states \<Rightarrow> process \<Rightarrow> var_dict \<Rightarrow> bool" where
  "vardict_inv ss p vs 
   \<longleftrightarrow> lm.ball vs (\<lambda>(k,v). k \<in> process_names ss p \<and> variable_inv v)"

lemma vardicts_finite:
  "finite (Collect (vardict_inv ss p))"
proof -
  have "Assoc_List.set ` Collect (vardict_inv ss p) \<subseteq> 
           Pow (process_names ss p \<times> {v. variable_inv v})"
    by (auto simp add: lm_ball_Assoc_List_set vardict_inv_def)

  moreover have "finite ..."
    using process_names_finite variables_finite
    by simp
  ultimately show ?thesis by (metis finite_Assoc_List_set_image finite_subset)
qed

lemma lm_to_map_vardict_inv:
  assumes "\<forall>(k,v) \<in> set xs. k \<in> process_names ss proc \<and> variable_inv v"
  shows "vardict_inv ss proc (lm.to_map xs)"
using assms
unfolding vardict_inv_def
by (auto simp add: lm.correct dest: map_of_SomeD)

subsection \<open>Invariants of a process\<close>

(* The definition of a channel to be between -1 and max_channels definitly lacks the necessary abstraction ... *)
definition pState_inv :: "program \<Rightarrow> pState \<Rightarrow> bool" where
  "pState_inv prog p 
  \<longleftrightarrow> pid p \<le> max_procs
    \<and> pState.idx p < IArray.length (states prog) 
    \<and> IArray.length (states prog) = IArray.length (processes prog)
    \<and> pc p < IArray.length ((states prog) !! pState.idx p)
    \<and> set (pState.channels p) \<subseteq> {-1..<integer_of_nat max_channels} 
    \<and> length (pState.channels p) \<le> max_channels
    \<and> vardict_inv ((states prog) !! pState.idx p) 
                  ((processes prog) !! pState.idx p) 
                  (pState.vars p)"

lemma pStates_finite:
  "finite (Collect (pState_inv prog))"
proof -
  let ?P1 = "{..max_procs::nat}"
  let ?P2 = "{..IArray.length (states prog)}"
  let ?P3 = "{..Max (IArray.length ` (set (IArray.list_of (states prog))))}"
  let ?P4 = "{cs. set cs \<subseteq> {-1..<integer_of_nat max_channels} 
                  \<and> length cs \<le> max_channels}"
  let ?P5 = "\<Union>x\<in>{..IArray.length (states prog)}. 
                Collect (vardict_inv (states prog !! x) (processes prog !! x))"
  let ?P = "?P1 \<times> ?P2 \<times> ?P3 \<times> ?P4 \<times> ?P5"

  have "{p. pState_inv prog p} \<subseteq> 
    (\<lambda>(pid,idx,pc,channels,vars). pState.make pid vars pc channels idx) ` ?P"
    unfolding pState_inv_def image_def [of _ ?P]
    apply (clarsimp simp add: pState.defs)
    apply (tactic \<open>Record.split_simp_tac @{context} [] (K ~1) 1\<close>)
    apply auto
    apply (rule order_trans [OF less_imp_le])
    apply (auto intro!: Max_ge)
    done
  moreover
  have "finite ?P4" by (fastforce intro: finite_lists_length_le)
  hence "finite ?P" by (auto intro: finite_cartesian_product simp: vardicts_finite)

  ultimately show ?thesis by (elim finite_subset) (rule finite_imageI)
qed

text \<open>
  Throughout the calculation of the semantic engine, a modified process is not necessarily part of @{term "procs g"}.
  Hence we need to establish an additional constraint for the relation between a global and a process state.\<close>

definition cl_inv :: "('a gState_scheme * pState) \<Rightarrow> bool" where
  "cl_inv gp = (case gp of (g,p) \<Rightarrow> 
      length (pState.channels p) \<le> length (gState.channels g))"

lemma cl_inv_lengthD:
  "cl_inv (g,p) \<Longrightarrow> length (pState.channels p) \<le> length (gState.channels g)"
unfolding cl_inv_def
by auto

lemma cl_invI:
  "length (pState.channels p) \<le> length (gState.channels g) \<Longrightarrow> cl_inv (g,p)"
unfolding cl_inv_def by auto

lemma cl_inv_trans:
  "length (channels g) \<le> length (channels g') \<Longrightarrow> cl_inv (g,p) \<Longrightarrow> cl_inv (g',p)"
by (simp add: cl_inv_def)

lemma cl_inv_vars_update[intro!]:
  "cl_inv (g,p) \<Longrightarrow> cl_inv (g, pState.vars_update vs p)"
  "cl_inv (g,p) \<Longrightarrow> cl_inv (gState.vars_update vs g, p)"
by (simp_all add: cl_inv_def)

lemma cl_inv_handshake_update[intro!]:
  "cl_inv (g,p) \<Longrightarrow> cl_inv (g\<lparr>handshake := h\<rparr>,p)"
by (simp add: cl_inv_def)

lemma cl_inv_hsdata_update[intro!]:
  "cl_inv (g,p) \<Longrightarrow> cl_inv (g\<lparr>hsdata := h\<rparr>,p)"
by (simp add: cl_inv_def)

lemma cl_inv_procs_update[intro!]:
  "cl_inv (g,p) \<Longrightarrow> cl_inv (g\<lparr>procs := ps\<rparr>,p)"
by (simp add: cl_inv_def)

lemma cl_inv_channels_update:
  assumes "cl_inv (g,p)"
  shows "cl_inv (gState.channels_update (\<lambda>cs. cs[i:=c]) g, p)"
using assms unfolding cl_inv_def 
by simp

subsection \<open>Invariants of the global state\<close>

text \<open>Note that @{term gState_inv} must be defined in a way to be applicable to both @{typ gState} and @{typ gState\<^sub>I}.\<close>

definition gState_inv :: "program \<Rightarrow> 'a gState_scheme \<Rightarrow> bool" where
  "gState_inv prog g 
  \<longleftrightarrow> length (procs g) \<le> max_procs 
    \<and> (\<forall>p \<in> set (procs g). pState_inv prog p \<and> cl_inv (g,p))
    \<and> length (channels g) \<le> max_channels
    \<and> set (channels g) \<subseteq> Collect channel_inv
    \<and> lm.ball (vars g) (\<lambda>(k,v). variable_inv v)" 

text \<open>The set of global states adhering to the terms of @{const gState_inv} is not finite.
But the set of all global states that can be constructed by the semantic engine from one starting state is. 
Thus we establish a progress relation, \ie all successors of a state @{term g} relate to @{term g} under this specification.\<close>

definition gState_progress_rel :: "program \<Rightarrow> ('a gState_scheme) rel" where
  "gState_progress_rel p = {(g,g'). gState_inv p g \<and> gState_inv p g'
                                  \<and> length (channels g) \<le> length (channels g')
                                  \<and> dom (lm.\<alpha> (vars g)) = dom (lm.\<alpha> (vars g'))}"

lemma gState_progress_rel_gState_invI1[intro]:
  "(g,g') \<in> gState_progress_rel prog \<Longrightarrow> gState_inv prog g"
by (simp add: gState_progress_rel_def)

lemma gState_progress_rel_gState_invI2[intro]:
  "(g,g') \<in> gState_progress_rel prog \<Longrightarrow> gState_inv prog g'"
by (simp add: gState_progress_rel_def)

lemma gState_progress_relI:
  assumes "gState_inv prog g"
  and "gState_inv prog g'"
  and "length (channels g) \<le> length (channels g')"
  and "dom (lm.\<alpha> (vars g)) = dom (lm.\<alpha> (vars g'))"
  shows "(g,g') \<in> gState_progress_rel prog"
unfolding gState_progress_rel_def
using assms
by auto

lemma gState_progress_refl[simp,intro!]:
  "gState_inv prog g \<Longrightarrow> (g,g) \<in> (gState_progress_rel prog)"
unfolding gState_progress_rel_def
by auto

lemma refl_on_gState_progress_rel:
  "refl_on (Collect (gState_inv prog)) (gState_progress_rel prog)"
by (auto intro!: refl_onI)

lemma trans_gState_progress_rel[simp]:
  "trans (gState_progress_rel prog)"
by (intro transI) (simp add: gState_progress_rel_def)

lemmas gState_progress_rel_trans [trans] = trans_gState_progress_rel[THEN transD]

lemma gState_progress_rel_trancl_id[simp]:
  "(gState_progress_rel prog)\<^sup>+ = gState_progress_rel prog"
by simp

lemma gState_progress_rel_rtrancl_absorb:
  assumes "gState_inv prog g"
  shows "(gState_progress_rel prog)\<^sup>* `` {g} = gState_progress_rel prog `` {g}"
using assms refl_on_gState_progress_rel
by (intro Image_absorb_rtrancl) auto

text \<open>
  The main theorem: The set of all global states reachable from an initial state, is finite.
\<close>
lemma gStates_finite:
  fixes g :: "gState"
  shows "finite ((gState_progress_rel prog)\<^sup>* `` {g})"
proof (cases "gState_inv prog g")
  case False hence "(gState_progress_rel prog)\<^sup>* `` {g} = {g}" 
    by (intro Image_empty_rtrancl_Image_id) 
       (auto simp add: gState_progress_rel_def)
  thus ?thesis by simp
next
  case True
  let ?G1 = "{m. dom (lm.\<alpha> m) = dom (lm.\<alpha> (vars g)) 
                 \<and> ran (lm.\<alpha> m) \<subseteq> Collect variable_inv }"
  let ?G2 = "{cs. set cs \<subseteq> Collect channel_inv 
                  \<and> length cs \<le> max_channels}"
  let ?G3 = "{True, False}"
  let ?G4 = "{ps. set ps \<subseteq> Collect (pState_inv prog) 
                  \<and> length ps \<le> max_procs}"
  
  let ?G = "?G1 \<times> ?G2 \<times> ?G3 \<times> ?G4"
  let ?G' = "(\<lambda>(vars,chans,t,ps). gState.make vars chans t ps) ` ?G"

  have G1: "finite ?G1"
  proof (rule finite_subset)
    show "?G1 \<subseteq> {v'. fst ` Assoc_List.set v' = fst ` Assoc_List.set (vars g) 
                     \<and> snd ` Assoc_List.set v' \<subseteq> Collect variable_inv}"
      by (simp add: dom_lm_\<alpha>_Assoc_List_set ran_lm_\<alpha>_Assoc_List_set)
    show "finite ..." (is "finite ?X")
    proof (rule finite_Assoc_List_set_image, rule finite_subset)
      show "Assoc_List.set ` ?X \<subseteq> 
             Pow (fst ` Assoc_List.set (vars g) \<times> Collect variable_inv)"
        by auto
      show "finite ..." by (auto simp add: variables_finite dom_lm_\<alpha>_Assoc_List_set[symmetric])
    qed
  qed

  have "finite ((gState_progress_rel prog) `` {g})"
  proof (rule finite_subset)
    show "(gState_progress_rel prog) `` {g} \<subseteq> 
           (\<lambda>(vars,chans,t,ps). gState.make vars chans t ps) ` ?G"
      apply (clarsimp simp add: image_def gState_inv_def gState.defs gState_progress_rel_def)
      apply (rule_tac x = "vars x" in exI)
      apply (simp add: lm_ball_eq_ran)
      apply (rule_tac x = "channels x" in exI)
      apply (case_tac "timeout x")
        apply clarsimp
        apply (rule_tac x="procs x" in exI)
        apply auto
      done
    show "finite ..." using G1 
      by (blast intro: finite_lists_length_le channels_finite pStates_finite)
  qed
  with gState_progress_rel_rtrancl_absorb[OF True] show ?thesis by simp
qed

lemma gState_progress_rel_channels_update:
  assumes "gState_inv prog g"
  and "channel_inv c"
  and "i < length (channels g)"
  shows "(g,gState.channels_update (\<lambda>cs. cs[i:=c]) g) \<in> gState_progress_rel prog"
using assms
by (auto intro!: gState_progress_relI 
         simp add: gState_inv_def cl_inv_def 
         dest!: subsetD[OF set_update_subset_insert])

lemma gState_progress_rel_channels_update_step:
  assumes "gState_inv prog g"
  and step: "(g,g') \<in> gState_progress_rel prog"
  and "channel_inv c"
  and "i < length (channels g')"
  shows "(g,gState.channels_update (\<lambda>cs. cs[i:=c]) g') \<in> gState_progress_rel prog"
proof -
  note step
  also hence "gState_inv prog g'" by blast
  note gState_progress_rel_channels_update[OF this assms(3,4)]
  finally show ?thesis .
qed

subsection \<open>Invariants of the program\<close>

text \<open>
  Naturally, we need our program to also adhere to certain invariants. Else we can't show, that
  the generated states are correct according to the invariants above.
\<close>

definition program_inv where
  "program_inv prog 
  \<longleftrightarrow> IArray.length (states prog) > 0
    \<and> IArray.length (states prog) = IArray.length (processes prog)
    \<and> (\<forall>s \<in> set (IArray.list_of (states prog)). IArray.length s > 0)
    \<and> lm.ball (proc_data prog) 
              (\<lambda>(_,sidx). 
                    sidx < IArray.length (processes prog) 
                  \<and> fst (processes prog !! sidx) = sidx)
    \<and> (\<forall>(sidx,start,procArgs,args) \<in> set (IArray.list_of (processes prog)). 
        (\<exists>s. start = Index s \<and> s < IArray.length (states prog !! sidx)))"

lemma program_inv_length_states:
  assumes "program_inv prog"
  and "n < IArray.length (states prog)"
  shows "IArray.length (states prog !! n) > 0"
using assms by (simp add: program_inv_def)

lemma program_invI:
  assumes "0 < IArray.length (states prog)"
  and "IArray.length (states prog) = IArray.length (processes prog)"
  and "\<And>s. s \<in> set (IArray.list_of (states prog)) 
           \<Longrightarrow> 0 < IArray.length s"
  and "\<And>sidx. sidx \<in> ran (lm.\<alpha> (proc_data prog)) 
               \<Longrightarrow> sidx < IArray.length (processes prog) 
                  \<and> fst (processes prog !! sidx) = sidx"
  and "\<And>sidx start procArgs args. 
         (sidx,start,procArgs,args) \<in> set (IArray.list_of (processes prog)) 
         \<Longrightarrow> \<exists>s. start = Index s \<and> s < IArray.length (states prog !! sidx)"
  shows "program_inv prog"
unfolding program_inv_def
using assms
by (auto simp add: lm_ball_eq_ran)

end
