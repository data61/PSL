theory FSM
imports
  "Transition_Systems_and_Automata.Sequence_Zip"
  "Transition_Systems_and_Automata.Transition_System"
  "Transition_Systems_and_Automata.Transition_System_Extra"
  "Transition_Systems_and_Automata.Transition_System_Construction"
begin 

section \<open> Finite state machines \<close>

text \<open>
We formalise finite state machines as a 4-tuples, omitting the explicit formulation of the state 
set,as it can easily be calculated from the successor function.
This definition does not require the successor function to be restricted to the input or output 
alphabet, which is later expressed by the property @{verbatim well_formed}, together with the 
finiteness of the state set.
\<close>

record ('in, 'out, 'state) FSM =
  succ    :: "('in \<times> 'out) \<Rightarrow> 'state \<Rightarrow> 'state set"
  inputs  :: "'in set"
  outputs :: "'out set"
  initial :: "'state"



subsection \<open> FSMs as transition systems \<close>

text \<open>
We interpret FSMs as transition systems with a singleton initial state set, based on 
@{cite "Transition_Systems_and_Automata-AFP"}. 
\<close>
                                   
global_interpretation FSM : transition_system_initial
  "\<lambda> a p. snd a"                    \<comment> \<open>execute\<close>
  "\<lambda> a p. snd a \<in> succ A (fst a) p" \<comment> \<open>enabled\<close>
  "\<lambda> p. p = initial A"              \<comment> \<open>initial\<close>
  for A
  defines path = FSM.path 
      and run = FSM.run 
      and reachable = FSM.reachable 
      and nodes = FSM.nodes
  by this

abbreviation "size_FSM M \<equiv> card (nodes M)" 
notation 
  size_FSM ("(|_|)")

subsection \<open> Language \<close>

text \<open>
The following definitions establish basic notions for FSMs similarly to those of nondeterministic
finite automata as defined in @{cite "Transition_Systems_and_Automata-AFP"}.

In particular, the language of an FSM state are the IO-parts of the paths in the FSM enabled from
that state.
\<close>

abbreviation "target \<equiv> FSM.target"
abbreviation "states \<equiv> FSM.states"
abbreviation "trace \<equiv> FSM.trace"

abbreviation successors :: "('in, 'out, 'state, 'more) FSM_scheme \<Rightarrow> 'state \<Rightarrow> 'state set" where
    "successors \<equiv> FSM.successors TYPE('in) TYPE('out) TYPE('more)"

lemma states_alt_def: "states r p = map snd r" 
  by (induct r arbitrary: p) (auto)
lemma trace_alt_def: "trace r p = smap snd r" 
  by (coinduction arbitrary: r p) (auto)


definition language_state :: "('in, 'out, 'state) FSM \<Rightarrow> 'state 
                              \<Rightarrow> ('in \<times> 'out) list set" ("LS") 
  where
  "language_state M q \<equiv> {map fst r |r . path M r q}"

text \<open>
The language of an FSM is the language of its initial state.
\<close>
abbreviation "L M \<equiv> LS M (initial M)"
  

lemma language_state_alt_def : "LS M q = {io | io tr . path M (io || tr) q \<and> length io = length tr}"
proof -
  have "LS M q \<subseteq> { io | io tr . path M  (io || tr) q \<and> length io = length tr }"
  proof 
    fix xr assume xr_assm : "xr \<in> LS M q"
    then obtain r where r_def : "map fst r = xr" "path M r q" 
      unfolding language_state_def by auto
    then obtain xs ys where xr_split : "xr = xs || ys" 
                                       "length xs = length ys" 
                                       "length xs = length xr"
      by (metis length_map zip_map_fst_snd) 
    then have "(xs || ys) \<in> { io | io tr . path M  (io || tr) q \<and> length io = length tr }" 
    proof -
      have f1: "xs || ys = map fst r"
        by (simp add: r_def(1) xr_split(1))
      then have f2: "path M ((xs || ys) || take (min (length (xs || ys)) (length (map snd r))) 
                                                  (map snd r)) q"
        by (simp add: r_def(2))
      have "length (xs || ys) = length 
                                  (take (min (length (xs || ys)) (length (map snd r))) (map snd r))"
        using f1 by force
      then show ?thesis
        using f2 by blast
    qed 
    then show "xr \<in> { io | io tr . path M  (io || tr) q \<and> length io = length tr }" 
      using xr_split by metis
  qed
  moreover have "{ io | io tr . path M  (io || tr) q \<and> length io = length tr } \<subseteq> LS M q" 
  proof 
    fix xs assume xs_assm : "xs \<in> { io | io tr . path M  (io || tr) q \<and> length io = length tr }"
    then obtain ys where ys_def : "path M (xs || ys) q" "length xs = length ys" 
      by auto
    then have "xs = map fst (xs || ys)" 
      by auto
    then show "xs \<in> LS M q" 
      using ys_def unfolding language_state_def by blast 
  qed
  ultimately show ?thesis 
    by auto
qed
  

lemma language_state[intro]:
  assumes "path M (w || r) q" "length w = length r"
  shows "w \<in> LS M q"
  using assms unfolding language_state_def by force

lemma language_state_elim[elim]:
  assumes "w \<in> LS M q"
  obtains r
  where "path M (w || r) q" "length w = length r"
  using assms unfolding language_state_def by (force iff: split_zip_ex)

lemma language_state_split:
  assumes "w1 @ w2 \<in> LS M q"
  obtains tr1 tr2
  where "path M (w1 || tr1) q" "length w1 = length tr1"
        "path M (w2 || tr2) (target (w1 || tr1) q)" "length w2 = length tr2"
proof -
  obtain tr where tr_def : "path M ((w1 @ w2) || tr) q" "length (w1 @ w2) = length tr"
    using assms by blast 
  let ?tr1 = "take (length w1) tr"
  let ?tr2 = "drop (length w1) tr"
  have tr_split : "?tr1 @ ?tr2 = tr" 
    by auto
  then show ?thesis
  proof -
    have f1: "length w1 + length w2 = length tr"
      using tr_def(2) by auto
    then have f2: "length w2 = length tr - length w1" 
      by presburger
    then have "length w1 = length (take (length w1) tr)"
      using f1 by (metis (no_types) tr_split diff_add_inverse2 length_append length_drop)
    then show ?thesis
      using f2 by (metis (no_types) FSM.path_append_elim length_drop that tr_def(1) zip_append1)
  qed
qed

lemma language_state_prefix :
  assumes "w1 @ w2 \<in> LS M q"
shows "w1 \<in> LS M q"
  using assms by (meson language_state language_state_split) 


lemma succ_nodes :
  fixes A :: "('a,'b,'c) FSM"
  and   w :: "('a \<times> 'b)"
  assumes "q2 \<in> succ A w q1"
  and     "q1 \<in> nodes A"
shows "q2 \<in> nodes A"
proof -
  obtain x y where "w = (x,y)" 
    by (meson surj_pair)
  then have "q2 \<in> successors A q1" 
    using assms  by auto
  then have "q2 \<in> reachable A q1" 
    by blast 
  then have "q2 \<in> reachable A (initial A)" 
    using assms by blast 
  then show "q2 \<in> nodes A" 
    by blast
qed

lemma states_target_index :
  assumes "i < length p"
  shows "(states p q1) ! i = target (take (Suc i) p) q1"
  using assms by auto 



subsection \<open> Product machine for language intersection \<close>

text \<open>
The following describes the construction of a product machine from two FSMs @{verbatim M1} 
and @{verbatim M2} such that the language of the product machine is the intersection of the 
language of @{verbatim M1} and the language of @{verbatim M2}.
\<close>

definition product :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow>
  ('in, 'out, 'state1 \<times>'state2) FSM" where
  "product A B \<equiv>
  \<lparr>
    succ = \<lambda> a (p\<^sub>1, p\<^sub>2). succ A a p\<^sub>1 \<times> succ B a p\<^sub>2,
    inputs = inputs A \<union> inputs B,
    outputs = outputs A \<union> outputs B,
    initial = (initial A, initial B)
  \<rparr>"

lemma product_simps[simp]:
  "succ (product A B) a (p\<^sub>1, p\<^sub>2) = succ A a p\<^sub>1 \<times> succ B a p\<^sub>2"
  "inputs (product A B) = inputs A \<union> inputs B"
  "outputs (product A B) = outputs A \<union> outputs B"
  "initial (product A B) = (initial A, initial B)"
  unfolding product_def by simp+

lemma product_target[simp]:
  assumes "length w = length r\<^sub>1" "length r\<^sub>1 = length r\<^sub>2"
  shows "target (w || r\<^sub>1 || r\<^sub>2) (p\<^sub>1, p\<^sub>2) = (target (w || r\<^sub>1) p\<^sub>1, target (w || r\<^sub>2) p\<^sub>2)"
  using assms by (induct arbitrary: p\<^sub>1 p\<^sub>2 rule: list_induct3) (auto)
lemma product_path[iff]:
  assumes "length w = length r\<^sub>1" "length r\<^sub>1 = length r\<^sub>2"
  shows "path (product A B) (w || r\<^sub>1 || r\<^sub>2) (p\<^sub>1, p\<^sub>2) \<longleftrightarrow> path A (w || r\<^sub>1) p\<^sub>1 \<and> path B (w || r\<^sub>2) p\<^sub>2"
  using assms by (induct arbitrary: p\<^sub>1 p\<^sub>2 rule: list_induct3) (auto)

lemma product_language_state[simp]: "LS (product A B) (q1,q2) = LS A q1 \<inter> LS B q2"
  by (fastforce iff: split_zip)

lemma product_nodes :
  "nodes (product A B) \<subseteq> nodes A \<times> nodes B"
proof 
  fix q assume "q \<in> nodes (product A B)"
  then show "q \<in> nodes A \<times> nodes B"
  proof (induction rule: FSM.nodes.induct)
    case (initial p)
    then show ?case by auto
  next
    case (execute p a)
    then have "fst p \<in> nodes A" "snd p \<in> nodes B" 
      by auto
    
    have "snd a \<in> (succ A (fst a) (fst p)) \<times> (succ B (fst a) (snd p))"
      using execute by auto
    then have "fst (snd a) \<in> succ A (fst a) (fst p)"
              "snd (snd a) \<in> succ B (fst a) (snd p)"
      by auto

    have "fst (snd a) \<in> nodes A"
      using \<open>fst p \<in> nodes A\<close> \<open>fst (snd a) \<in> succ A (fst a) (fst p)\<close>
      by (metis FSM.nodes.simps fst_conv snd_conv) 
    moreover have "snd (snd a) \<in> nodes B"
      using \<open>snd p \<in> nodes B\<close> \<open>snd (snd a) \<in> succ B (fst a) (snd p)\<close>
      by (metis FSM.nodes.simps fst_conv snd_conv) 
    ultimately show ?case
      by (simp add: mem_Times_iff) 
      
  qed
qed



subsection \<open> Required properties \<close>

text \<open>
FSMs used by the adaptive state counting algorithm are required to satisfy certain properties which
are introduced in here.
Most notably, the observability property (see function @{verbatim observable}) implies the 
uniqueness of certain paths and hence allows for several stronger variations of previous results.
\<close>


fun finite_FSM :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "finite_FSM M = (finite (nodes M) 
                  \<and> finite (inputs M) 
                  \<and> finite (outputs M))"

fun observable :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "observable M = (\<forall> t . \<forall> s1 . ((succ M) t s1 = {}) 
                                \<or> (\<exists> s2 . (succ M) t s1 = {s2}))"

fun completely_specified :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "completely_specified M = (\<forall> s1 \<in> nodes M . \<forall> x \<in> inputs M . 
                              \<exists> y \<in> outputs M . 
                                \<exists> s2 . s2 \<in> (succ M) (x,y) s1)"

fun well_formed :: "('in, 'out, 'state) FSM \<Rightarrow> bool" where
  "well_formed M = (finite_FSM M
                    \<and> (\<forall> s1 x y . (x \<notin> inputs M \<or> y \<notin> outputs M) 
                                    \<longrightarrow> succ M (x,y) s1 = {})
                    \<and> inputs M \<noteq> {}
                    \<and> outputs M \<noteq> {})"

abbreviation "OFSM M \<equiv> well_formed M 
                        \<and> observable M 
                        \<and> completely_specified M"

lemma OFSM_props[elim!] :
  assumes "OFSM M"
shows "well_formed M" 
      "observable M" 
      "completely_specified M" using assms by auto

lemma set_of_succs_finite :
  assumes "well_formed M"
  and     "q \<in> nodes M"
shows "finite (succ M io q)"
proof (rule ccontr)
  assume "infinite (succ M io q)"
  moreover have "succ M io q \<subseteq> nodes M" 
    using assms by (simp add: subsetI succ_nodes) 
  ultimately have "infinite (nodes M)"
    using infinite_super by blast 
  then show "False" 
    using assms by auto
qed

lemma well_formed_path_io_containment : 
  assumes "well_formed M"
  and     "path M p q"
shows "set (map fst p) \<subseteq> (inputs M \<times> outputs M)"
using assms proof (induction p arbitrary: q)
case Nil
  then show ?case by auto
next
  case (Cons a p)
  have "fst a \<in> (inputs M \<times> outputs M)"
  proof (rule ccontr)
    assume "fst a \<notin> inputs M \<times> outputs M"
    then have "fst (fst a) \<notin> inputs M \<or> snd (fst a) \<notin> outputs M" 
      by (metis SigmaI prod.collapse) 
    then have "succ M (fst a) q = {}" 
      using Cons by (metis prod.collapse well_formed.elims(2)) 
    moreover have "(snd a) \<in> succ M (fst a) q" 
      using Cons by auto
    ultimately show "False" 
      by auto
  qed
  moreover have "set (map fst p) \<subseteq> (inputs M \<times> outputs M)" 
    using Cons by blast 
  ultimately show ?case 
    by auto
qed


lemma path_input_containment :
  assumes "well_formed M"
  and     "path M p q"  
shows "set (map fst (map fst p)) \<subseteq> inputs M"
using assms proof (induction p arbitrary: q rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc a p)
  have "set (map fst (p @ [a])) \<subseteq> (inputs M \<times> outputs M)" 
    using well_formed_path_io_containment[OF snoc.prems] by assumption
  then have "(fst a) \<in> (inputs M \<times> outputs M)" 
    by auto
  then have "fst (fst a) \<in> inputs M" 
    by auto
  moreover have "set (map fst (map fst p)) \<subseteq> inputs M" 
    using snoc.IH[OF snoc.prems(1)]
    using snoc.prems(2) by blast 
  ultimately show ?case
    by simp 
qed

lemma path_state_containment :
  assumes "path M p q"
  and     "q \<in> nodes M"
shows "set (map snd p) \<subseteq> nodes M"
  using assms by (metis FSM.nodes_states states_alt_def) 


lemma language_state_inputs :
  assumes "well_formed M"
  and     "io \<in> language_state M q"
shows "set (map fst io) \<subseteq> inputs M"
proof -
  obtain tr where "path M (io || tr) q" "length tr = length io" 
    using assms(2) by auto
  show ?thesis 
    by (metis (no_types) 
        \<open>\<And>thesis. (\<And>tr. \<lbrakk>path M (io || tr) q; length tr = length io\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
        assms(1) map_fst_zip path_input_containment)
qed 


lemma set_of_paths_finite : 
  assumes "well_formed M"
  and     "q1 \<in> nodes M"
shows "finite { p . path M p q1 \<and> target p q1 = q2 \<and> length p \<le> k }"
proof -

  let ?trs = "{ tr . set tr \<subseteq> nodes M \<and> length tr \<le> k }"
  let ?ios = "{ io . set io \<subseteq> inputs M \<times> outputs M \<and> length io \<le> k }"
  let ?iotrs = "image (\<lambda> (io,tr) . io || tr) (?ios \<times> ?trs)"

  let ?paths = "{ p . path M p q1 \<and> target p q1 = q2 \<and> length p \<le> k }"
  
  have "finite (inputs M \<times> outputs M)" 
    using assms by auto
  then have "finite ?ios" 
    using assms by (simp add: finite_lists_length_le) 
  moreover have "finite ?trs" 
    using assms by (simp add: finite_lists_length_le)
  ultimately have "finite ?iotrs" 
    by auto

  moreover have "?paths \<subseteq> ?iotrs" 
  proof 
    fix p assume p_assm : "p \<in> { p . path M p q1 \<and> target p q1 = q2 \<and> length p \<le> k }"
    then obtain io tr where p_split : "p = io || tr \<and> length io = length tr" 
      using that by (metis (no_types) length_map zip_map_fst_snd)
    then have "io \<in> ?ios" 
      using well_formed_path_io_containment
    proof -
      have f1: "path M p q1 \<and> target p q1 = q2 \<and> length p \<le> k"
        using p_assm by force
      then have "set io \<subseteq> inputs M \<times> outputs M"
        by (metis (no_types) assms(1) map_fst_zip p_split well_formed_path_io_containment)
      then show ?thesis
        using f1 by (simp add: p_split)
    qed 

    moreover have "tr \<in> ?trs" using p_split
    proof -
      have f1: "path M (io || tr) q1 \<and> target (io || tr) q1 = q2 
                  \<and> length (io || tr) \<le> k" using \<open>p \<in> {p. path M p q1 
                  \<and> target p q1 = q2 \<and> length p \<le> k}\<close> p_split by force
      then have f2: "length tr \<le> k" by (simp add: p_split)
      have "set tr \<subseteq> nodes M"
        using f1 by (metis (no_types) assms(2) length_map p_split path_state_containment 
                      zip_eq zip_map_fst_snd)
      then show ?thesis 
        using f2 by blast
    qed 
    ultimately show "p \<in> ?iotrs" 
      using p_split by auto
  qed

  ultimately show ?thesis 
    using Finite_Set.finite_subset by blast
qed 


lemma non_distinct_duplicate_indices :
  assumes "\<not> distinct xs"
shows "\<exists> i1 i2 . i1 \<noteq> i2 \<and> xs ! i1 = xs ! i2 \<and> i1 \<le> length xs \<and> i2 \<le> length xs"
  using assms by (meson distinct_conv_nth less_imp_le) 

lemma reaching_path_without_repetition :
  assumes "well_formed M"
  and     "q2 \<in> reachable M q1"
  and     "q1 \<in> nodes M"
shows "\<exists> p . path M p q1 \<and> target p q1 = q2 \<and> distinct (q1 # states p q1)"
proof -
  have shorten_nondistinct : "\<forall> p. (path M p q1 \<and> target p q1 = q2 \<and> \<not> distinct (q1 # states p q1)) 
               \<longrightarrow> (\<exists> p' . path M p' q1 \<and> target p' q1 = q2 \<and> length p' < length p)"
  proof 
    fix p 
    show "(path M p q1 \<and> target p q1 = q2 \<and> \<not> distinct (q1 # states p q1)) 
               \<longrightarrow> (\<exists> p' . path M p' q1 \<and> target p' q1 = q2 \<and> length p' < length p)"
    proof 
      assume assm : "path M p q1 \<and> target p q1 = q2 \<and> \<not> distinct (q1 # states p q1)"
      then show "(\<exists>p'. path M p' q1 \<and> target p' q1 = q2 \<and> length p' < length p)"
      proof (cases "q1 \<in> set (states p q1)")
        case True
        have "\<exists> i1 . target (take i1 p) q1 = q1 \<and> i1 \<le> length p \<and> i1 > 0"
        proof (rule ccontr)
          assume "\<not> (\<exists> i1. target (take i1 p) q1 = q1 \<and> i1 \<le> length p \<and> i1 > 0)"
          then have "\<not> (\<exists> i1 . (states p q1) ! i1 = q1 \<and> i1 \<le> length (states p q1))" 
            by (metis True in_set_conv_nth less_eq_Suc_le scan_length scan_nth zero_less_Suc)
          then have "q1 \<notin> set (states p q1)" 
            by (meson in_set_conv_nth less_imp_le)  
          then show "False" 
            using True by auto
        qed
        then obtain i1 where i1_def : "target (take i1 p) q1 = q1 \<and> i1 \<le> length p \<and> i1 > 0" 
          by auto

        then have "path M (take i1 p) q1" 
          using assm by (metis FSM.path_append_elim append_take_drop_id)  
        moreover have "path M (drop i1 p) q1" 
          using i1_def by (metis FSM.path_append_elim append_take_drop_id assm) 
        ultimately have "path M (drop i1 p) q1 \<and> (target (drop i1 p) q1 = q2)" 
          using i1_def by (metis (no_types) append_take_drop_id assm fold_append o_apply)
        
        moreover have "length (drop i1 p) < length p" 
          using i1_def by auto
        ultimately show ?thesis 
          using assms by blast
      
     next
        case False
        then have assm' : "path M p q1 \<and> target p q1 = q2 \<and> \<not> distinct (states p q1)" 
          using assm by auto

        have "\<exists> i1 i2 . i1 \<noteq> i2 \<and> target (take i1 p) q1 = target (take i2 p) q1 
                        \<and> i1 \<le> length p \<and> i2 \<le> length p"
        proof (rule ccontr)
          assume "\<not> (\<exists> i1 i2 . i1 \<noteq> i2 \<and> target (take i1 p) q1 = target (take i2 p) q1 
                                \<and> i1 \<le> length p \<and> i2 \<le> length p)"
          then have "\<not> (\<exists> i1 i2 . i1 \<noteq> i2 \<and> (states p q1) ! i1 = (states p q1) ! i2 
                                  \<and> i1 \<le> length (states p q1) \<and> i2 \<le> length (states p q1))"
            by (metis (no_types, lifting) Suc_leI assm' distinct_conv_nth nat.inject 
                scan_length scan_nth) 
    
          then have "distinct (states p q1)" 
            using non_distinct_duplicate_indices by blast 
          then show "False" 
            using assm' by auto
        qed
        then obtain i1 i2 where i_def : "i1 < i2 \<and> target (take i1 p) q1 = target (take i2 p) q1 
                                          \<and> i1 \<le> length p \<and> i2 \<le> length p" 
          by (metis nat_neq_iff)
    
        then have "path M (take i1 p) q1" 
          using assm by (metis FSM.path_append_elim append_take_drop_id)  
        moreover have "path M (drop i2 p) (target (take i2 p) q1)" 
          by (metis FSM.path_append_elim append_take_drop_id assm) 
        ultimately have "path M ((take i1 p) @ (drop i2 p)) q1 
                          \<and> (target ((take i1 p) @ (drop i2 p)) q1 = q2)" 
          using i_def assm
          by (metis FSM.path_append append_take_drop_id fold_append o_apply) 
    
        moreover have "length ((take i1 p) @ (drop i2 p)) < length p" 
          using i_def by auto
    
        ultimately have "path M ((take i1 p) @ (drop i2 p)) q1 
                          \<and> target ((take i1 p) @ (drop i2 p)) q1 = q2 
                          \<and> length ((take i1 p) @ (drop i2 p)) < length p" 
          by simp
      
        then show ?thesis 
          using assms by blast
      qed      
    qed
  qed

  obtain p where p_def : "path M p q1 \<and> target p q1 = q2" 
    using assms by auto

  let ?paths = "{p' . (path M p' q1 \<and> target p' q1 = q2 \<and> length p' \<le> length p)}"
  let ?minPath = "arg_min length (\<lambda> io . io \<in> ?paths)" 
  
  have "?paths \<noteq> empty" 
    using p_def by auto
  moreover have "finite ?paths" 
    using assms by (simp add: set_of_paths_finite) 
  ultimately have minPath_def : "?minPath \<in> ?paths \<and> (\<forall> p' \<in> ?paths . length ?minPath \<le> length p')" 
    by (meson arg_min_nat_lemma equals0I) 
  
  moreover have "distinct (q1 # states ?minPath q1)"
  proof (rule ccontr)
    assume "\<not> distinct (q1 # states ?minPath q1)"
    then have "\<exists> p' . path M p' q1 \<and> target p' q1 = q2 \<and> length p' < length ?minPath" 
      using shorten_nondistinct minPath_def by blast 
    then show "False" 
      using minPath_def using arg_min_nat_le dual_order.strict_trans1 by auto 
  qed

  ultimately show ?thesis by auto
qed





lemma observable_path_unique[simp] :
  assumes "io \<in> LS M q"
  and     "observable M"
  and     "path M (io || tr1) q" "length io = length tr1"
  and     "path M (io || tr2) q" "length io = length tr2"
shows "tr1 = tr2"
proof (rule ccontr)
  assume tr_assm : "tr1 \<noteq> tr2"
  then have state_diff : "(states (io || tr1) q ) \<noteq> (states (io || tr2) q)"
    by (metis assms(4) assms(6) map_snd_zip states_alt_def)
  show "False"
  using assms tr_assm proof (induction io arbitrary: q tr1 tr2)
    case Nil
    then show ?case using Nil 
      by simp
  next
    case (Cons io_hd io_tl)
    then obtain tr1_hd tr1_tl tr2_hd tr2_tl where tr_split : "tr1 = tr1_hd # tr1_tl 
                                                              \<and> tr2 = tr2_hd # tr2_tl"
      by (metis length_0_conv neq_Nil_conv)

    have p1: "path M ([io_hd] || [tr1_hd]) q"   
      using Cons.prems tr_split by auto
    have p2: "path M ([io_hd] || [tr2_hd]) q"   
      using Cons.prems tr_split by auto
    have tr_hd_eq : "tr1_hd = tr2_hd"           
      using Cons.prems unfolding observable.simps
    proof -
      assume "\<forall>t s1. succ M t s1 = {} \<or> (\<exists>s2. succ M t s1 = {s2})"
      then show ?thesis
        by (metis (no_types) p1 p2 FSM.path_cons_elim empty_iff prod.sel(1) prod.sel(2) singletonD 
            zip_Cons_Cons)
    qed

    then show ?thesis
      using Cons.IH Cons.prems(3) Cons.prems(4) Cons.prems(5) Cons.prems(6) Cons.prems(7) assms(2) 
            tr_split by auto 
  qed
qed


lemma observable_path_unique_ex[elim] : 
  assumes "observable M"
  and     "io \<in> LS M q"
obtains tr 
where "{ t . path M (io || t) q \<and> length io = length t } = { tr }" 
proof -
  obtain tr where tr_def : "path M (io || tr) q" "length io = length tr" 
    using assms by auto
  then have "{ t . path M (io || t) q \<and> length io = length t } \<noteq> {}" 
    by blast
  moreover have "\<forall> t \<in> { t . path M (io || t) q \<and> length io = length t } . t = tr" 
    using assms tr_def by auto  
  ultimately show ?thesis 
    using that by moura
qed

lemma well_formed_product[simp] :
  assumes "well_formed M1"
  and     "well_formed M2"
shows "well_formed (product M2 M1)" (is "well_formed ?PM")
unfolding well_formed.simps proof
  have "finite (nodes M1)" "finite (nodes M2)" 
    using assms by auto
  then have "finite (nodes M2 \<times> nodes M1)" 
    by simp

  moreover have "nodes ?PM \<subseteq> nodes M2 \<times> nodes M1" 
    using product_nodes assms by blast
  ultimately show "finite_FSM ?PM" 
    using infinite_subset assms by auto  
next
  have "inputs ?PM = inputs M2 \<union> inputs M1" 
       "outputs ?PM = outputs M2 \<union> outputs M1" 
    by auto
  then show "(\<forall>s1 x y. x \<notin> inputs ?PM \<or> y \<notin> outputs ?PM \<longrightarrow> succ ?PM (x, y) s1 = {}) 
                                                              \<and> inputs ?PM \<noteq> {} \<and> outputs ?PM \<noteq> {}" 
    using assms by auto
qed


subsection \<open> States reached by a given IO-sequence \<close>

text \<open>
Function @{verbatim io_targets} collects all states of an FSM reached from a given state by a 
given IO-sequence.
Notably, for any observable FSM, this set contains at most one state.
\<close>

fun io_targets :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> 'state set" where
  "io_targets M q io = { target (io || tr) q | tr . path M (io || tr) q \<and> length io = length tr }"

lemma io_target_implies_L :
  assumes "q \<in> io_targets M (initial M) io"
  shows "io \<in> L M" 
proof -
  obtain tr where "path M (io || tr) (initial M)" 
                  "length tr = length io" 
                  "target (io || tr) (initial M) = q" 
    using assms by auto
  then show ?thesis by auto
qed

lemma io_target_from_path :
  assumes "path M (w || tr) q"
  and     "length w = length tr"
shows "target (w || tr) q \<in> io_targets M q w"
  using assms by auto

lemma io_targets_observable_singleton_ex :
  assumes "observable M"
  and     "io \<in> LS M q1"
shows "\<exists> q2 . io_targets M q1 io = { q2 }"
proof -
  obtain tr where tr_def : "{ t . path M (io || t) q1 \<and> length io = length t } = { tr }" 
    using assms observable_path_unique_ex by (metis (mono_tags, lifting)) 
  then have "io_targets M q1 io = { target (io || tr) q1 }" 
    by fastforce 
  then show ?thesis 
    by blast 
qed

lemma io_targets_observable_singleton_ob :
  assumes "observable M"
  and     "io \<in> LS M q1"
obtains q2 
  where "io_targets M q1 io = { q2 }"
proof -
  obtain tr where tr_def : "{ t . path M (io || t) q1 \<and> length io = length t } = { tr }" 
    using assms observable_path_unique_ex by (metis (mono_tags, lifting)) 
  then have "io_targets M q1 io = { target (io || tr) q1 }" 
    by fastforce 
  then show ?thesis using that by blast 
qed

lemma io_targets_elim[elim] :
  assumes "p \<in> io_targets M q io"
obtains tr 
where "target (io || tr) q = p \<and> path M (io || tr) q \<and> length io = length tr" 
  using assms  unfolding io_targets.simps by force 


lemma io_targets_reachable :
  assumes "q2 \<in> io_targets M q1 io"
  shows "q2 \<in> reachable M q1" 
  using assms  unfolding io_targets.simps by blast

lemma io_targets_nodes :
  assumes "q2 \<in> io_targets M q1 io"
  and     "q1 \<in> nodes M"
shows "q2 \<in> nodes M"
  using assms by auto


lemma observable_io_targets_split :
  assumes "observable M"
  and "io_targets M q1 (vs @ xs) = {q3}"
  and "io_targets M q1 vs = {q2}"
shows "io_targets M q2 xs = {q3}"
proof -
  have "vs @ xs \<in> LS M q1" 
    using assms(2) by force 
  then obtain trV trX where tr_def : 
        "path M (vs || trV) q1" "length vs = length trV"
        "path M (xs || trX) (target (vs || trV) q1)" "length xs = length trX" 
    using language_state_split[of vs xs M q1] by auto
  then have tgt_V : "target (vs || trV) q1 = q2" 
    using assms(3) by auto
  then have path_X : "path M (xs || trX) q2 \<and> length xs = length trX" 
    using tr_def by auto

  have tgt_all :  "target (vs @ xs || trV @ trX) q1 = q3"
  proof -
    have f1: "\<exists>cs. q3 = target (vs @ xs || cs) q1 
                    \<and> path M (vs @ xs || cs) q1 \<and> length (vs @ xs) = length cs"
      using assms(2) by auto
    have "length (vs @ xs) = length trV + length trX"
      by (simp add: tr_def(2) tr_def(4))
    then have "length (vs @ xs) = length (trV @ trX)"
      by simp
    then show ?thesis
      using f1 by (metis FSM.path_append \<open>vs @ xs \<in> LS M q1\<close> assms(1) observable_path_unique 
                    tr_def(1) tr_def(2) tr_def(3) zip_append)
  qed 
  then have "target ((vs || trV) @ (xs || trX)) q1 = q3" 
    using tr_def by simp 
  then have "target (xs || trX) q2 = q3" 
    using tgt_V by auto
  then have "q3 \<in> io_targets M q2 xs" 
    using path_X by auto
  then show ?thesis 
    by (metis (no_types) \<open>observable M\<close> path_X insert_absorb io_targets_observable_singleton_ex 
        language_state singleton_insert_inj_eq')
qed 



lemma observable_io_target_unique_target :
  assumes "observable M"
  and     "io_targets M q1 io = {q2}"
  and     "path M (io || tr) q1"
  and     "length io = length tr"
shows "target (io || tr) q1 = q2"
  using assms by auto
  
lemma target_in_states : 
  assumes "length io = length tr"
  and     "length io > 0"
  shows "last (states (io || tr) q) = target (io || tr) q"
proof -
  have "0 < length tr"
    using assms(1) assms(2) by presburger
  then show ?thesis
    by (simp add: FSM.target_alt_def assms(1) states_alt_def)
qed 

lemma target_alt_def :
  assumes "length io = length tr"
  shows "length io = 0 \<Longrightarrow> target (io || tr) q = q"
        "length io > 0 \<Longrightarrow> target (io || tr) q = last tr"
proof -
  show "length io = 0 \<Longrightarrow> target (io || tr) q = q" by simp
  show "length io > 0 \<Longrightarrow> target (io || tr) q = last tr" 
    by (metis assms last_ConsR length_greater_0_conv map_snd_zip scan_last states_alt_def) 
qed

lemma obs_target_is_io_targets :
  assumes "observable M"
  and     "path M (io || tr) q"
  and     "length io = length tr"
shows "io_targets M q io = {target (io || tr) q}"
  by (metis assms(1) assms(2) assms(3) io_targets_observable_singleton_ex language_state 
      observable_io_target_unique_target)



lemma io_target_target :
  assumes "io_targets M q1 io = {q2}"
  and     "path M (io || tr) q1"
  and     "length io = length tr"
shows "target (io || tr) q1 = q2"
proof -
  have "target (io || tr) q1 \<in> io_targets M q1 io" using assms(2) assms(3) by auto 
  then show ?thesis using assms(1) by blast
qed 


lemma index_last_take :
  assumes "i < length xs"
  shows "xs ! i = last (take (Suc i) xs)"
  by (simp add: assms take_Suc_conv_app_nth) 

lemma path_last_io_target :
  assumes "path M (xs || tr) q" 
  and     "length xs = length tr"
  and     "length xs > 0"
shows "last tr \<in> io_targets M q xs" 
proof -
  have "last tr = target (xs || tr) q"
    by (metis assms(2) assms(3) map_snd_zip states_alt_def target_in_states)
  then show ?thesis using assms(1) assms(2) by auto
qed


lemma path_prefix_io_targets :
  assumes "path M (xs || tr) q" 
  and     "length xs = length tr"
  and     "length xs > 0"
shows "last (take (Suc i) tr) \<in> io_targets M q (take (Suc i) xs)" 
proof -
  have "path M (take (Suc i) xs || take (Suc i) tr) q" 
    by (metis (no_types) FSM.path_append_elim append_take_drop_id assms(1) take_zip) 
  then show ?thesis 
    using assms(2) assms(3) path_last_io_target by fastforce  
qed


lemma states_index_io_target :
  assumes "i < length xs"
  and     "path M (xs || tr) q" 
  and     "length xs = length tr"
  and     "length xs > 0"
shows "(states (xs || tr) q) ! i \<in> io_targets M q (take (Suc i) xs)"
proof -
  have "(states (xs || tr) q) ! i = last (take (Suc i) (states (xs || tr) q))" 
    by (metis assms(1) assms(3) map_snd_zip states_alt_def index_last_take) 
  then have "(states (xs || tr) q) ! i = last (states (take (Suc i) xs || take (Suc i) tr) q)"
    by (simp add: take_zip) 
  then have "(states (xs || tr) q) ! i = last (take (Suc i) tr)" 
    by (simp add: assms(3) states_alt_def) 
  moreover have "last (take (Suc i) tr) \<in> io_targets M q (take (Suc i) xs)" 
    by (meson assms(2) assms(3) assms(4) path_prefix_io_targets) 
  ultimately show ?thesis 
    by simp
qed


lemma observable_io_targets_append :
  assumes "observable M"
  and "io_targets M q1 vs = {q2}"
  and "io_targets M q2 xs = {q3}"
shows "io_targets M q1 (vs@xs) = {q3}"
proof -
  obtain trV where "path M (vs || trV) q1 \<and> length trV = length vs \<and> target (vs || trV) q1 = q2" 
    by (metis assms(2) io_targets_elim singletonI) 
  moreover obtain trX where "path M (xs || trX) q2 \<and> length trX = length xs 
                              \<and> target (xs || trX) q2 = q3" 
    by (metis assms(3) io_targets_elim singletonI)
  ultimately have "path M (vs @ xs || trV @ trX) q1 \<and> length (trV @ trX) = length (vs @ xs) 
                    \<and> target (vs @ xs || trV @ trX) q1 = q3" 
    by auto
  then show ?thesis 
    by (metis assms(1) obs_target_is_io_targets) 
qed


lemma io_path_states_prefix :
  assumes "observable M"
  and "path M (io1 || tr1) q"
  and "length tr1 = length io1"
  and "path M (io2 || tr2) q"
  and "length tr2 = length io2"
  and "prefix io1 io2"
shows "tr1 = take (length tr1) tr2"
proof -
  let ?tr1' = "take (length tr1) tr2"
  let ?io1' = "take (length tr1) io2"
  have "path M (?io1' || ?tr1') q"
    by (metis FSM.path_append_elim append_take_drop_id assms(4) take_zip)
  have "length ?tr1' = length ?io1'"
    using assms (5) by auto

  have "?io1' = io1"
  proof -
    have "\<forall>ps psa. \<not> prefix (ps::('a \<times> 'b) list) psa \<or> length ps \<le> length psa"
      using prefix_length_le by blast
    then have "length (take (length tr1) io2) = length io1"
      using assms(3) assms(6) min.absorb2 by auto
    then show ?thesis
      by (metis assms(6) min.cobounded2 min_def_raw prefix_length_prefix 
          prefix_order.dual_order.antisym take_is_prefix)
  qed

  show "tr1 = ?tr1'"
    by (metis \<open>length (take (length tr1) tr2) = length (take (length tr1) io2)\<close> 
        \<open>path M (take (length tr1) io2 || take (length tr1) tr2) q\<close> \<open>take (length tr1) io2 = io1\<close> 
        assms(1) assms(2) assms(3) language_state observable_path_unique)
qed

  

lemma observable_io_targets_suffix :
  assumes "observable M"
  and "io_targets M q1 vs = {q2}"
  and "io_targets M q1 (vs@xs) = {q3}"
shows "io_targets M q2 xs = {q3}"
proof -
  have "prefix vs (vs@xs)" 
    by auto
  
  obtain trV where "path M (vs || trV) q1 \<and> length trV = length vs \<and> target (vs || trV) q1 = q2" 
    by (metis assms(2) io_targets_elim singletonI)
  moreover obtain trVX where "path M (vs@xs || trVX) q1 
                                \<and> length trVX = length (vs@xs) \<and> target (vs@xs || trVX) q1 = q3" 
    by (metis assms(3) io_targets_elim singletonI)

  
  ultimately have "trV = take (length trV) trVX" 
    using io_path_states_prefix[OF assms(1) _ _ _ _ \<open>prefix vs (vs@xs)\<close>, of trV q1 trVX] by auto
  show ?thesis 
    by (meson assms(1) assms(2) assms(3) observable_io_targets_split)
qed


lemma observable_io_target_is_singleton[simp] :
  assumes "observable M"
  and     "p \<in> io_targets M q io"
shows "io_targets M q io = {p}" 
proof -
  have "io \<in> LS M q" 
    using assms(2) by auto
  then obtain p' where "io_targets M q io = {p'}" 
    using assms(1) by (meson io_targets_observable_singleton_ex) 
  then show ?thesis 
    using assms(2) by simp
qed


lemma observable_path_prefix :
  assumes "observable M"
  and     "path M (io || tr) q"
  and     "length io = length tr"
  and     "path M (ioP || trP) q"
  and     "length ioP = length trP"
  and     "prefix ioP io" 
shows "trP = take (length ioP) tr"
proof -
  have ioP_def : "ioP = take (length ioP) io" 
    using assms(6) by (metis append_eq_conv_conj prefixE) 
  then have "take (length ioP) (io || tr) = take (length ioP) io || take (length ioP) tr" 
    using take_zip by blast 
  moreover have "path M (take (length ioP) (io || tr)) q" 
    using assms by (metis FSM.path_append_elim append_take_drop_id)
  ultimately have "path M (take (length ioP) io || take (length ioP) tr) q 
                    \<and> length (take (length ioP) io) = length (take (length ioP) tr)" 
    using assms(3) by auto
  then have "path M (ioP || take (length ioP) tr) q \<and> length ioP = length (take (length ioP) tr)" 
    using assms(3) using ioP_def by auto
  then show ?thesis 
    by (meson assms(1) assms(4) assms(5) language_state observable_path_unique)
qed


lemma io_targets_succ : 
  assumes "q2 \<in> io_targets M q1 [xy]"
  shows "q2 \<in> succ M xy q1"
proof -
  obtain tr where tr_def : "target ([xy] || tr) q1 = q2" 
                           "path M ([xy] || tr) q1" 
                           "length [xy] = length tr"
    using assms by auto

  have "length tr = Suc 0"
    using \<open>length [xy] = length tr\<close> by auto
  then obtain q2' where "tr = [q2']"
    by (metis Suc_length_conv length_0_conv)
  then have "target ([xy] || tr) q1 = q2'"
    by auto
  then have "q2' = q2"
    using \<open>target ([xy] || tr) q1 = q2\<close> by simp
  then have "path M ([xy] || [q2]) q1" 
    using tr_def(2) \<open>tr = [q2']\<close> by auto
  then have "path M [(xy,q2)] q1"
    by auto

  show ?thesis 
  proof (cases rule: FSM.path.cases[of M "[(xy,q2)]" q1])
    case nil
    show ?case 
      using \<open>path M [(xy,q2)] q1\<close> by simp
  next
    case cons 
    show "snd (xy, q2) \<in> succ M (fst (xy, q2)) q1 \<Longrightarrow> path M [] (snd (xy, q2)) 
            \<Longrightarrow> q2 \<in> succ M xy q1" 
      by auto
  qed
qed


subsection \<open> D-reachability \<close>

text \<open>
A state of some FSM is d-reached (deterministically reached) by some input sequence if any sequence 
in the language of the FSM with this input sequence reaches that state. 
That state is then called d-reachable. 
\<close>

abbreviation  "d_reached_by M p xs q tr ys \<equiv> 
                    ((length xs = length ys \<and> length xs = length tr 
                    \<and> (path M ((xs || ys) || tr) p) \<and> target ((xs || ys) || tr) p = q) 
                    \<and> (\<forall> ys2 tr2 .  (length xs = length ys2 \<and> length xs = length tr2 
                    \<and> path M ((xs || ys2) || tr2) p) \<longrightarrow> target ((xs || ys2) || tr2) p = q))"  

fun d_reaches :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in list \<Rightarrow> 'state \<Rightarrow> bool" where
  "d_reaches M p xs q = (\<exists> tr ys . d_reached_by M p xs q tr ys)"

fun d_reachable :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'state set" where
  "d_reachable M p = { q . (\<exists> xs . d_reaches M p xs q) }"


lemma d_reaches_unique[elim] : 
  assumes "d_reaches M p xs q1"
  and    "d_reaches M p xs q2"
shows "q1 = q2"
using assms unfolding d_reaches.simps by blast

lemma d_reaches_unique_cases[simp] : "{ q . d_reaches M (initial M) xs q } = {} 
                                      \<or> (\<exists> q2 . { q . d_reaches M (initial M) xs q } = { q2 })"
  unfolding d_reaches.simps by blast

lemma d_reaches_unique_obtain[simp] :
  assumes "d_reaches M (initial M) xs q"
shows "{ p . d_reaches M (initial M) xs p } = { q }"
  using assms unfolding d_reaches.simps by blast

lemma d_reaches_io_target :
  assumes "d_reaches M p xs q"
  and     "length ys = length xs"
shows "io_targets M p (xs || ys) \<subseteq> {q}"
proof 
  fix q' assume "q' \<in> io_targets M p (xs || ys)"
  then obtain trQ where "path M ((xs || ys) || trQ) p \<and> length (xs || ys) = length trQ" 
    by auto
  moreover obtain trD ysD where "d_reached_by M p xs q trD ysD" using assms(1) 
    by auto
  ultimately have "target ((xs || ys) || trQ) p = q" 
    by (simp add: assms(2))
  then show "q' \<in> {q}" 
    using \<open>d_reached_by M p xs q trD ysD\<close> \<open>q' \<in> io_targets M p (xs || ys)\<close> assms(2) by auto
qed
  
lemma d_reachable_reachable : "d_reachable M p \<subseteq> reachable M p" 
  unfolding d_reaches.simps d_reachable.simps by blast




subsection \<open> Deterministic state cover \<close>

text \<open>
The deterministic state cover of some FSM is a minimal set of input sequences such that every
d-reachable state of the FSM is d-reached by a sequence in the set and the set contains the
empty sequence (which d-reaches the initial state). 
\<close>


fun is_det_state_cover_ass :: "('in, 'out, 'state) FSM \<Rightarrow> ('state \<Rightarrow> 'in list) \<Rightarrow> bool" where
  "is_det_state_cover_ass M f = (f (initial M) = [] \<and> (\<forall> s \<in> d_reachable M (initial M) . 
                                                                d_reaches M (initial M) (f s) s))"

lemma det_state_cover_ass_dist : 
  assumes "is_det_state_cover_ass M f"
  and     "s1 \<in> d_reachable M (initial M)"
  and     "s2 \<in> d_reachable M (initial M)"
  and     "s1 \<noteq> s2"
shows "\<not>(d_reaches M (initial M) (f s2) s1)"
  by (meson assms(1) assms(3) assms(4) d_reaches_unique is_det_state_cover_ass.simps)


lemma det_state_cover_ass_diff :
  assumes "is_det_state_cover_ass M f"
  and     "s1 \<in> d_reachable M (initial M)"
  and     "s2 \<in> d_reachable M (initial M)"
  and     "s1 \<noteq> s2"
shows "f s1 \<noteq> f s2"
  by (metis assms det_state_cover_ass_dist is_det_state_cover_ass.simps)


fun is_det_state_cover :: "('in, 'out, 'state) FSM \<Rightarrow> 'in list set \<Rightarrow> bool" where
  "is_det_state_cover M V = (\<exists> f . is_det_state_cover_ass M f 
                                    \<and> V = image f (d_reachable M (initial M)))"

lemma det_state_cover_d_reachable[elim] :
  assumes "is_det_state_cover M V"
  and     "v \<in> V"
obtains q
where "d_reaches M (initial M) v q"
  by (metis (no_types, hide_lams) assms(1) assms(2) image_iff is_det_state_cover.simps 
      is_det_state_cover_ass.elims(2))



lemma det_state_cover_card[simp] :
  assumes "is_det_state_cover M V"
  and     "finite (nodes M)"
shows   "card (d_reachable M (initial M)) = card V"
proof -
  obtain f where f_def : "is_det_state_cover_ass M f \<and> V = image f (d_reachable M (initial M))"
    using assms unfolding is_det_state_cover.simps by blast
  then have card_f : "card V = card (image f (d_reachable M (initial M)))"
    by simp

  have "d_reachable M (initial M) \<subseteq> nodes M"
    unfolding d_reachable.simps d_reaches.simps using d_reachable_reachable by blast
  then have dr_finite : "finite (d_reachable M (initial M))"
    using assms infinite_super by blast 

  then have card_le : "card (image f (d_reachable M (initial M))) \<le> card (d_reachable M (initial M))"
    using card_image_le by blast

  have "card (image f (d_reachable M (initial M))) = card (d_reachable M (initial M))"
    by (meson card_image det_state_cover_ass_diff f_def inj_onI)

  then show ?thesis using card_f by auto
qed

lemma det_state_cover_finite :
  assumes "is_det_state_cover M V"
  and     "finite (nodes M)"
shows "finite V"
proof -
  have "d_reachable M (initial M) \<subseteq> nodes M"
    by auto 
  show "finite V" using det_state_cover_card[OF assms]
    by (metis \<open>d_reachable M (initial M) \<subseteq> nodes M\<close> assms(1) assms(2) finite_imageI infinite_super 
        is_det_state_cover.simps)    
qed


lemma det_state_cover_initial :
  assumes "is_det_state_cover M V"
  shows   "[] \<in> V"
proof -
  have "d_reached_by M (initial M) [] (initial M) [] []"
    by (simp add: FSM.nil)
  then have "d_reaches M (initial M) [] (initial M)" 
    by auto
  
  have "initial M \<in> d_reachable M (initial M)"
    by (metis (no_types) \<open>d_reaches M (initial M) [] (initial M)\<close> d_reachable.simps mem_Collect_eq)
  then show ?thesis
    by (metis (no_types, lifting) assms image_iff is_det_state_cover.elims(2) 
        is_det_state_cover_ass.simps) 
qed

lemma det_state_cover_empty : 
  assumes "is_det_state_cover M V"
  shows "[] \<in> V"
proof -
  obtain f where f_def : "is_det_state_cover_ass M f \<and> V = f ` d_reachable M (initial M)" 
    using assms by auto
  then have "f (initial M) = []" 
    by auto
  moreover have "initial M \<in> d_reachable M (initial M)" 
  proof -
    have "d_reaches M (initial M) [] (initial M)" 
      by auto
    then show ?thesis 
      by (metis d_reachable.simps mem_Collect_eq) 
  qed
  moreover have "f (initial M) \<in> V" 
    using f_def calculation by blast
  ultimately show ?thesis 
    by auto
qed




subsection \<open> IO reduction \<close>

text \<open>
An FSM is a reduction of another, if its language is a subset of the language of the latter FSM.
\<close>


fun io_reduction :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out, 'state) FSM 
                      \<Rightarrow> bool" (infix "\<preceq>" 200) 
  where 
  "M1 \<preceq> M2 = (LS M1 (initial M1) \<subseteq> LS M2 (initial M2))"


lemma language_state_inclusion_of_state_reached_by_same_sequence : 
  assumes "LS M1 q1 \<subseteq> LS M2 q2"
  and     "observable M1"
  and     "observable M2"
  and     "io_targets M1 q1 io = { q1t }"
  and     "io_targets M2 q2 io = { q2t }"
shows "LS M1 q1t \<subseteq> LS M2 q2t"
proof 
  fix x assume "x \<in> LS M1 q1t" 
  obtain q1x where "io_targets M1 q1t x = {q1x}"
    by (meson \<open>x \<in> LS M1 q1t\<close> assms(2) io_targets_observable_singleton_ex) 
  have "io \<in> LS M1 q1" 
    using assms(4) by auto
  have "io@x \<in> LS M1 q1" 
    using observable_io_targets_append[OF assms(2) \<open>io_targets M1 q1 io = { q1t }\<close> 
          \<open>io_targets M1 q1t x = {q1x}\<close>]
    by (metis io_targets_elim language_state singletonI) 
  then have "io@x \<in> LS M2 q2" 
    using assms(1) by blast
  then obtain q2x where "io_targets M2 q2 (io@x) = {q2x}"
    by (meson assms(3) io_targets_observable_singleton_ex)
  show "x \<in> LS M2 q2t"
    using observable_io_targets_split[OF assms(3) \<open>io_targets M2 q2 (io @ x) = {q2x}\<close> assms(5)] 
    by auto
qed




subsection \<open> Language subsets for input sequences \<close>

text \<open>
The following definitions describe restrictions of languages to only those IO-sequences that 
exhibit a certain input sequence or whose input sequence is contained in a given set of
input sequences.
This allows to define the notion that some FSM is a reduction of another over a given set of
input sequences, but not necessarily over the entire language of the latter FSM.
\<close>

fun language_state_for_input :: 
  "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in list \<Rightarrow> ('in \<times> 'out) list set" where
  "language_state_for_input M q xs = {(xs || ys) | ys . (length xs = length ys \<and> (xs || ys) \<in> LS M q)}"

fun language_state_for_inputs  :: 
  "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> 'in list set \<Rightarrow> ('in \<times> 'out) list set" 
    ("(LS\<^sub>i\<^sub>n _ _ _)" [1000,1000,1000]) where
  "language_state_for_inputs  M q ISeqs = {(xs || ys) | xs ys . (xs \<in> ISeqs 
                                                                  \<and> length xs = length ys 
                                                                  \<and> (xs || ys) \<in> LS M q)}"

abbreviation "L\<^sub>i\<^sub>n M TS \<equiv> LS\<^sub>i\<^sub>n M (initial M) TS"

abbreviation  "io_reduction_on M1 TS M2 \<equiv> (L\<^sub>i\<^sub>n M1 TS \<subseteq> L\<^sub>i\<^sub>n M2 TS)" 
notation 
  io_reduction_on ("(_ \<preceq>\<lbrakk>_\<rbrakk> _)" [1000,0,0] 61)
notation  (latex output)
  io_reduction_on ("(_ \<preceq>\<^bsub>_\<^esub> _)" [1000,0,0] 61)


lemma language_state_for_input_alt_def :
  "language_state_for_input M q xs = LS\<^sub>i\<^sub>n M q {xs}"
  unfolding language_state_for_input.simps language_state_for_inputs.simps by blast

lemma language_state_for_inputs_alt_def :
  "LS\<^sub>i\<^sub>n M q ISeqs = \<Union> (image (language_state_for_input M q) ISeqs)" 
  by auto

lemma language_state_for_inputs_in_language_state :
  "LS\<^sub>i\<^sub>n M q T \<subseteq> language_state M q"
  unfolding language_state_for_inputs.simps language_state_def
  by blast 

lemma language_state_for_inputs_map_fst :
  assumes "io \<in> language_state M q"
  and     "map fst io \<in> T"
shows "io \<in> LS\<^sub>i\<^sub>n M q T"
proof -
  let ?xs = "map fst io"
  let ?ys = "map snd io"
  have "?xs \<in> T \<and> length ?xs = length ?ys \<and> ?xs || ?ys \<in> language_state M q" 
    using assms(2,1) by auto
  then have "?xs || ?ys \<in> LS\<^sub>i\<^sub>n M q T" 
    unfolding language_state_for_inputs.simps by blast 
  then show ?thesis 
    by simp
qed 

lemma language_state_for_inputs_nonempty :
  assumes "set xs \<subseteq> inputs M"
  and     "completely_specified M"
  and     "q \<in> nodes M"
shows "LS\<^sub>i\<^sub>n M q {xs} \<noteq> {}"
using assms proof (induction xs arbitrary: q)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have "x \<in> inputs M" 
    by simp
  then obtain y q' where x_step : "q' \<in> succ M (x,y) q" 
    using Cons(3,4) unfolding completely_specified.simps by blast
  then have "path M ([(x,y)] || [q']) q \<and> length [q] = length [(x,y)]" 
            "target ([(x,y)] || [q']) q = q'" 
    by auto
  then have "q' \<in> nodes M" 
    using Cons(4) by (metis FSM.nodes_target)            
  then have "LS\<^sub>i\<^sub>n M q' {xs} \<noteq> {}" 
    using Cons.prems Cons.IH by auto
  then obtain ys where "length xs = length ys \<and> (xs || ys) \<in> LS M q'" 
    by auto
  then obtain tr where "path M ((xs || ys) || tr) q' \<and> length tr = length (xs || ys)" 
    by auto
  then have "path M ([(x,y)] @ (xs || ys) || [q'] @ tr) q 
              \<and> length ([q'] @ tr) = length ([(x,y)] @ (xs || ys))" 
    by (simp add: FSM.path.intros(2) x_step)
  then have "path M ((x#xs || y#ys) || [q'] @ tr) q \<and> length ([q'] @ tr) = length (x#xs || y#ys)" 
    by auto
  then have "(x#xs || y#ys) \<in> LS M q" 
    by (metis language_state)
  moreover have "length (x#xs) = length (y#ys)" 
    by (simp add: \<open>length xs = length ys \<and> xs || ys \<in> LS M q'\<close>) 
  ultimately have "(x#xs || y#ys) \<in> LS\<^sub>i\<^sub>n M q {x # xs}" 
    unfolding language_state_for_inputs.simps by blast
  then show ?case by blast
qed

lemma language_state_for_inputs_map_fst_contained :
  assumes "vs \<in> LS\<^sub>i\<^sub>n M q V"
shows "map fst vs \<in> V" 
proof -
  have "(map fst vs) || (map snd vs) = vs" 
    by auto
  then have "(map fst vs) || (map snd vs) \<in> LS\<^sub>i\<^sub>n M q V" 
    using assms by auto
  then show ?thesis by auto
qed

lemma language_state_for_inputs_empty : 
  assumes "[] \<in> V"
  shows "[] \<in> LS\<^sub>i\<^sub>n M q V"
proof -
  have "[] \<in> language_state_for_input M q []" by auto
  then show ?thesis using language_state_for_inputs_alt_def by (metis UN_I assms) 
qed

lemma language_state_for_input_empty[simp] : 
  "language_state_for_input M q [] = {[]}"
by auto


lemma language_state_for_input_take :
  assumes "io \<in> language_state_for_input M q xs"
shows "take n io \<in> language_state_for_input M q (take n xs)" 
proof -
  obtain ys where "io = xs || ys" "length xs = length ys" "xs || ys \<in> language_state M q" 
    using assms by auto
  then obtain p where "length p = length xs" "path M ((xs || ys) || p) q "
    by auto 
  then have "path M (take n ((xs || ys) || p)) q"
    by (metis FSM.path_append_elim append_take_drop_id) 
  then have "take n (xs || ys) \<in> language_state M q"
    by (simp add: \<open>length p = length xs\<close> \<open>length xs = length ys\<close> language_state take_zip)
  then have "(take n xs) || (take n ys) \<in> language_state M q"
    by (simp add: take_zip) 
  
  have "take n io = (take n xs) || (take n ys)"
    using \<open>io = xs || ys\<close> take_zip by blast 
  moreover have "length (take n xs) = length (take n ys)"
    by (simp add: \<open>length xs = length ys\<close>) 
  ultimately show ?thesis 
    using \<open>(take n xs) || (take n ys) \<in> language_state M q\<close> 
    unfolding language_state_for_input.simps by blast
qed

lemma language_state_for_inputs_prefix :
  assumes "vs@xs \<in> L\<^sub>i\<^sub>n M1 {vs'@xs'}"
  and "length vs = length vs'"
shows "vs \<in> L\<^sub>i\<^sub>n M1 {vs'}"
proof -
  have "vs@xs \<in> L M1"
    using assms(1) by auto
  then have "vs \<in> L M1"
    by (meson language_state_prefix) 
  then have "vs \<in> L\<^sub>i\<^sub>n M1 {map fst vs}"
    by (meson insertI1 language_state_for_inputs_map_fst)
  moreover have "vs' = map fst vs"
    by (metis append_eq_append_conv assms(1) assms(2) language_state_for_inputs_map_fst_contained 
        length_map map_append singletonD)
  ultimately show ?thesis 
    by blast
qed

lemma language_state_for_inputs_union : 
  shows "LS\<^sub>i\<^sub>n M q T1 \<union> LS\<^sub>i\<^sub>n M q T2 = LS\<^sub>i\<^sub>n M q (T1 \<union> T2)"
  unfolding language_state_for_inputs.simps by blast

lemma io_reduction_on_subset :
  assumes "io_reduction_on M1 T M2"
  and     "T' \<subseteq> T"
shows "io_reduction_on M1 T' M2"
proof (rule ccontr)
  assume "\<not> io_reduction_on M1 T' M2"
  then obtain xs' where "xs' \<in> T'" "\<not> L\<^sub>i\<^sub>n M1 {xs'} \<subseteq> L\<^sub>i\<^sub>n M2 {xs'}"
  proof -
    have f1: "\<forall>ps P Pa. (ps::('a \<times> 'b) list) \<notin> P \<or> \<not> P \<subseteq> Pa \<or> ps \<in> Pa"
      by blast
    obtain pps :: "('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pps x0 x1 \<in> x1 \<and> pps x0 x1 \<notin> x0)"
      by moura
    then have f2: "\<forall>P Pa. pps Pa P \<in> P \<and> pps Pa P \<notin> Pa \<or> P \<subseteq> Pa"
      by (meson subsetI)
    have f3: "\<forall>ps f c A. (ps::('a \<times> 'b) list) \<notin> LS\<^sub>i\<^sub>n f (c::'c) A \<or> map fst ps \<in> A"
      by (meson language_state_for_inputs_map_fst_contained)
    then have "L\<^sub>i\<^sub>n M1 T' \<subseteq> L\<^sub>i\<^sub>n M1 T"
      using f2 by (meson assms(2) language_state_for_inputs_in_language_state 
                    language_state_for_inputs_map_fst set_rev_mp)
    then show ?thesis
      using f3 f2 f1 by (meson \<open>\<not> io_reduction_on M1 T' M2\<close> assms(1) 
                          language_state_for_inputs_in_language_state 
                          language_state_for_inputs_map_fst)
  qed 
  then have "xs' \<in> T" 
    using assms(2) by blast

  have "\<not> io_reduction_on M1 T M2"
  proof -
    have f1: "\<forall>as. as \<notin> T' \<or> as \<in> T"
      using assms(2) by auto
    obtain pps :: "('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pps x0 x1 \<in> x1 \<and> pps x0 x1 \<notin> x0)"
      by moura
    then have "\<forall>P Pa. (\<not> P \<subseteq> Pa \<or> (\<forall>ps. ps \<notin> P \<or> ps \<in> Pa)) 
                      \<and> (P \<subseteq> Pa \<or> pps Pa P \<in> P \<and> pps Pa P \<notin> Pa)"
      by blast
    then show ?thesis
      using f1 by (meson \<open>\<not> io_reduction_on M1 T' M2\<close> language_state_for_inputs_in_language_state 
                    language_state_for_inputs_map_fst language_state_for_inputs_map_fst_contained)
  qed 

  then show "False" 
    using assms(1) by auto
qed

subsection \<open> Sequences to failures \<close>

text \<open>
A sequence to a failure for FSMs @{verbatim M1} and @{verbatim M2} is a sequence such that any 
proper prefix of it is contained in the languages of both @{verbatim M1} and @{verbatim M2}, while 
the sequence itself is contained only in the language of A.

That is, if a sequence to a failure for @{verbatim M1} and @{verbatim M2} exists, then 
@{verbatim M1} is not a reduction of @{verbatim M2}.
\<close>


fun sequence_to_failure :: 
  "('in,'out,'state) FSM \<Rightarrow> ('in,'out,'state) FSM \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> bool" where
  "sequence_to_failure M1 M2 xs = (
    (butlast xs) \<in> (language_state M2 (initial M2) \<inter> language_state M1 (initial M1))
    \<and> xs \<in> (language_state M1 (initial M1) - language_state M2 (initial M2)))"


lemma sequence_to_failure_ob :
  assumes "\<not> M1 \<preceq> M2"
  and     "well_formed M1"
  and     "well_formed M2"  
obtains io
where "sequence_to_failure M1 M2 io"
proof -
  let ?diff = "{ io . io \<in> language_state M1 (initial M1) \<and> io \<notin> language_state M2 (initial M2)}"
  have "?diff \<noteq> empty" 
    using assms by auto
  moreover  obtain io where io_def[simp] : "io = arg_min length (\<lambda> io . io \<in> ?diff)" 
    using assms by auto
  ultimately have io_diff : "io \<in> ?diff" 
    using assms by (meson all_not_in_conv arg_min_natI) 

  then have "io \<noteq> []" 
    using assms io_def language_state by auto 
  then obtain io_init io_last where io_split[simp] : "io = io_init @ [io_last]" 
    by (metis append_butlast_last_id) 

  have io_init_inclusion : "io_init \<in> language_state M1 (initial M1) 
                            \<and> io_init \<in> language_state M2 (initial M2)"
  proof (rule ccontr)
    assume assm : "\<not> (io_init \<in> language_state M1 (initial M1) 
                        \<and> io_init \<in> language_state M2 (initial M2))"

    have "io_init @ [io_last] \<in> language_state M1 (initial M1)" 
      using io_diff io_split by auto
    then have "io_init \<in> language_state M1 (initial M1)" 
      by (meson language_state language_state_split) 
    moreover have "io_init \<notin> language_state M2 (initial M2)" 
      using assm calculation by auto
    ultimately have "io_init \<in> ?diff" 
      by auto 
    moreover have "length io_init < length io" 
      using io_split by auto 
    ultimately have "io \<noteq> arg_min length (\<lambda> io . io \<in> ?diff)"
    proof -
      have "\<exists>ps. ps \<in> {ps \<in> language_state M1 (initial M1). 
                              ps \<notin> language_state M2 (initial M2)} \<and> \<not> length io \<le> length ps"
        using \<open>io_init \<in> {io\<in> language_state M1 (initial M1). io \<notin> language_state M2 (initial M2)}\<close>
              \<open>length io_init < length io\<close> linorder_not_less 
        by blast
      then show ?thesis
        by (meson arg_min_nat_le)
    qed
    then show "False" using io_def by simp
  qed

  then have "sequence_to_failure M1 M2 io" 
    using io_split io_diff by auto
  then show ?thesis 
    using that by auto  
qed

lemma sequence_to_failure_succ :
  assumes "sequence_to_failure M1 M2 io"
  shows "\<forall> q \<in> io_targets M2 (initial M2) (butlast io) . succ M2 (last io) q = {}"
proof
  have "io \<noteq> []"
    using assms by auto
  fix q assume "q \<in> io_targets M2 (initial M2) (butlast io)"
  then obtain tr where "q = target (butlast io || tr) (initial M2)"
                 and   "path M2 (butlast io || tr) (initial M2)"
                 and   "length (butlast io) = length tr" 
    unfolding io_targets.simps by auto
  
  show "succ M2 (last io) q = {}"
  proof (rule ccontr)
    assume "succ M2 (last io) q \<noteq> {}"
    then obtain q' where "q' \<in> succ M2 (last io) q"
      by blast
    then have "path M2 [(last io, q')] (target (butlast io || tr) (initial M2))" 
      using \<open>q = target (butlast io || tr) (initial M2)\<close> by auto

    have "path M2 ((butlast io || tr) @ [(last io, q')]) (initial M2)"
      using \<open>path M2 (butlast io || tr) (initial M2)\<close> 
            \<open>path M2 [(last io, q')] (target (butlast io || tr) (initial M2))\<close> by auto

    have "butlast io @ [last io] = io"
      by (meson \<open>io \<noteq> []\<close> append_butlast_last_id)

    have "path M2 (io || (tr@[q'])) (initial M2)"
    proof -
      have "path M2 ((butlast io || tr) @ ([last io] || [q'])) (initial M2)"
        by (simp add: FSM.path_append \<open>path M2 (butlast io || tr) (initial M2)\<close> 
              \<open>path M2 [(last io, q')] (target (butlast io || tr) (initial M2))\<close>)
      then show ?thesis
        by (metis (no_types) \<open>butlast io @ [last io] = io\<close> 
              \<open>length (butlast io) = length tr\<close> zip_append)
    qed
    
    have "io \<in> L M2"
    proof -
      have "length tr + (0 + Suc 0) = length io"
        by (metis \<open>butlast io @ [last io] = io\<close> \<open>length (butlast io) = length tr\<close> 
            length_append list.size(3) list.size(4))
      then show ?thesis
        using \<open>path M2 (io || tr @ [q']) (initial M2)\<close> by fastforce
    qed
    then show "False" 
      using assms by auto
  qed
qed

lemma sequence_to_failure_non_nil : 
  assumes "sequence_to_failure M1 M2 xs"
  shows "xs \<noteq> []" 
proof 
  assume "xs = []"
  then have "xs \<in> L M1 \<inter> L M2" 
    by auto
  then show "False" using assms by auto
qed

lemma sequence_to_failure_from_arbitrary_failure :
  assumes "vs@xs \<in> L M1 - L M2"
    and "vs \<in> L M2 \<inter> L M1"
shows "\<exists> xs' . prefix xs' xs \<and> sequence_to_failure M1 M2 (vs@xs')"
using assms proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)

  have "vs @ xs \<in> L M1"
    using snoc.prems(1) by (metis Diff_iff append.assoc language_state_prefix) 

  show ?case
  proof (cases "vs@xs \<in> L M2")
    case True
    have "butlast (vs@xs@[x]) \<in> L M2 \<inter> L M1" 
      using True \<open>vs @ xs \<in> L M1\<close> by (simp add: butlast_append) 
    then show ?thesis
      using sequence_to_failure.simps snoc.prems by blast
  next
    case False
    then have "vs@xs \<in> L M1 - L M2"
      using \<open>vs @ xs \<in> L M1\<close> by blast
    then obtain xs' where "prefix xs' xs" "sequence_to_failure M1 M2 (vs@xs')"
      using snoc.prems(2) snoc.IH by blast
    then show ?thesis
      using prefix_snoc by auto 
  qed 
qed  


text \<open>
The following lemma shows that if @{verbatim M1} is not a reduction of @{verbatim M2}, then a 
minimal sequence to a failure exists that is of length at most the number of states in 
@{verbatim M1} times the number of states in @{verbatim M2}. 
\<close>

lemma sequence_to_failure_length :
  assumes "well_formed M1"
  and     "well_formed M2"
  and     "observable M1"
  and     "observable M2"
  and     "\<not> M1 \<preceq> M2"
  shows "\<exists> xs . sequence_to_failure M1 M2 xs \<and> length xs \<le> |M2| * |M1|"
proof -

  obtain seq where "sequence_to_failure M1 M2 seq" 
    using assms sequence_to_failure_ob by blast
  then have "seq \<noteq> []" 
    by auto

  let ?bls = "butlast seq"
  have "?bls \<in> L M1" "?bls \<in> L M2" 
    using \<open>sequence_to_failure M1 M2 seq\<close> by auto


  then obtain tr1b tr2b where 
    "path M1 (?bls || tr1b) (initial M1)"
    "length tr1b = length ?bls"
    "path M2 (?bls || tr2b) (initial M2)"
    "length ?bls = length tr2b"
    by fastforce
  then have "length tr2b = length tr1b" 
    by auto

  let ?PM = "product M2 M1"
  have "well_formed ?PM" 
    using well_formed_product[OF assms(1,2)] by assumption
  
  have "path ?PM (?bls || tr2b || tr1b) (initial M2, initial M1)" 
    using product_path[OF \<open>length ?bls = length tr2b\<close> \<open>length tr2b = length tr1b\<close>, 
                       of M2 M1 "initial M2" "initial M1"]
    using \<open>path M1 (butlast seq || tr1b) (initial M1)\<close> 
          \<open>path M2 (butlast seq || tr2b) (initial M2)\<close> 
    by blast

  let ?q1b = "target (?bls || tr1b) (initial M1)"
  let ?q2b = "target (?bls || tr2b) (initial M2)"

   
  have "io_targets M2 (initial M2) ?bls = {?q2b}"
    by (metis \<open>length (butlast seq) = length tr2b\<close> \<open>path M2 (butlast seq || tr2b) (initial M2)\<close> 
        assms(4) obs_target_is_io_targets)
  have "io_targets M1 (initial M1) ?bls = {?q1b}"
    by (metis \<open>length tr1b = length (butlast seq)\<close> \<open>path M1 (butlast seq || tr1b) (initial M1)\<close> 
        assms(3) obs_target_is_io_targets)



  have "(?q2b, ?q1b) \<in> reachable (product M2 M1) (initial M2, initial M1)"
  proof -
    have "target (butlast seq || tr2b || tr1b) (initial M2, initial M1) 
            \<in> reachable (product M2 M1) (initial M2, initial M1)"
      using \<open>path (product M2 M1) (butlast seq || tr2b || tr1b) (initial M2, initial M1)\<close> by blast
    then show ?thesis
      using \<open>length (butlast seq) = length tr2b\<close> \<open>length tr2b = length tr1b\<close> by auto
  qed

  

  have "(initial M2, initial M1) \<in> nodes (product M2 M1)"
    by (simp add: FSM.nodes.initial) 

  obtain p where repFreePath : "path (product M2 M1) p (initial M2, initial M1) \<and>
        target p (initial M2, initial M1) =
        (?q2b,?q1b)"
        "distinct ((initial M2, initial M1) # states p (initial M2, initial M1))" 
    using reaching_path_without_repetition[OF \<open>well_formed ?PM\<close> 
          \<open>(?q2b, ?q1b) \<in> reachable (product M2 M1) (initial M2, initial M1)\<close> 
          \<open>(initial M2, initial M1) \<in> nodes (product M2 M1)\<close>] 
    by blast
  
  then have "set (states p (initial M2, initial M1)) \<subseteq> nodes ?PM"
    by (simp add: FSM.nodes_states \<open>(initial M2, initial M1) \<in> nodes (product M2 M1)\<close>) 
  moreover have "(initial M2, initial M1) \<notin> set (states p (initial M2, initial M1))" 
    using \<open>distinct ((initial M2, initial M1) # states p (initial M2, initial M1))\<close> by auto
  ultimately have "set (states p (initial M2, initial M1)) \<subseteq> nodes ?PM - {(initial M2,initial M1)}"
    by blast
  moreover have "finite (nodes ?PM)" 
    using \<open>well_formed ?PM\<close> by auto
  ultimately have "card (set (states p (initial M2, initial M1))) < card (nodes ?PM)"
    by (metis \<open>(initial M2, initial M1) \<in> nodes (product M2 M1)\<close> 
        \<open>(initial M2, initial M1) \<notin> set (states p (initial M2, initial M1))\<close> 
        \<open>set (states p (initial M2, initial M1)) \<subseteq> nodes (product M2 M1)\<close> 
        psubsetI psubset_card_mono)

  moreover have "card (set (states p (initial M2, initial M1))) 
                  = length (states p (initial M2, initial M1))"
    using distinct_card repFreePath(2) by fastforce
  ultimately have "length (states p (initial M2, initial M1)) < |?PM|"
    by linarith
  then have "length p < |?PM|" 
    by auto
 


  let ?p1 = "map (snd \<circ> snd) p"
  let ?p2 = "map (fst \<circ> snd) p"
  let ?pIO = "map fst p"

  have "p = ?pIO || ?p2 || ?p1" 
    by (metis map_map zip_map_fst_snd)


  have "path M2 (?pIO || ?p2) (initial M2)"  
       "path M1 (?pIO || ?p1) (initial M1)" 
    using product_path[of ?pIO ?p2 ?p1 M2 M1] 
    using \<open>p = ?pIO || ?p2 || ?p1\<close> repFreePath(1) by auto

  have "(?q2b, ?q1b) = (target (?pIO || ?p2 || ?p1) (initial M2, initial M1))" 
    using \<open>p = ?pIO || ?p2 || ?p1\<close> repFreePath(1) by auto

  then have "?q2b = target (?pIO || ?p2) (initial M2)" 
            "?q1b = target (?pIO || ?p1) (initial M1)" 
    by auto

  have "io_targets M2 (initial M2) ?pIO = {?q2b}"
    by (metis \<open>path M2 (map fst p || map (fst \<circ> snd) p) (initial M2)\<close> 
        \<open>target (?bls || tr2b) (initial M2) = target (map fst p || map (fst \<circ> snd) p) (initial M2)\<close> 
        assms(4) length_map obs_target_is_io_targets)

  have "io_targets M1 (initial M1) ?pIO = {?q1b}"
    by (metis \<open>path M1 (map fst p || map (snd \<circ> snd) p) (initial M1)\<close> 
        \<open>target (?bls || tr1b) (initial M1) = target (map fst p || map (snd \<circ> snd) p) (initial M1)\<close> 
        assms(3) length_map obs_target_is_io_targets)

    
  
  have "seq \<in> L M1" "seq \<notin> L M2"
    using \<open>sequence_to_failure M1 M2 seq\<close> by auto

  have "io_targets M1 (initial M1) ?bls = {?q1b}"
    by (metis \<open>length tr1b = length (butlast seq)\<close> \<open>path M1 (butlast seq || tr1b) (initial M1)\<close> 
        assms(3) obs_target_is_io_targets)
  
  obtain q1s where "io_targets M1 (initial M1) seq = {q1s}"
    by (meson \<open>seq \<in> L M1\<close> assms(3) io_targets_observable_singleton_ob)
  

  moreover have "seq = (butlast seq)@[last seq]"
    using \<open>seq \<noteq> []\<close> by auto
  ultimately have "io_targets M1 (initial M1) ((butlast seq)@[last seq]) = {q1s}" 
    by auto
  

  have "io_targets M1 ?q1b [last seq] = {q1s}"
    using observable_io_targets_suffix[OF assms(3) \<open>io_targets M1 (initial M1) ?bls = {?q1b}\<close> 
          \<open>io_targets M1 (initial M1) ((butlast seq)@[last seq]) = {q1s}\<close>] by assumption
  then obtain tr1s where "q1s = target ([last seq] || tr1s) ?q1b" 
                         "path M1 ([last seq] || tr1s) ?q1b" 
                         "length [last seq] = length tr1s"
    by auto

  have "path M1 ([last seq] || [q1s]) ?q1b"
    by (metis (no_types) \<open>length [last seq] = length tr1s\<close> 
        \<open>path M1 ([last seq] || tr1s) (target (butlast seq || tr1b) (initial M1))\<close> 
        \<open>q1s = target ([last seq] || tr1s) (target (butlast seq || tr1b) (initial M1))\<close> 
        append_Nil append_butlast_last_id butlast.simps(2) length_butlast length_greater_0_conv 
        not_Cons_self2 target_alt_def(2))
  then have "q1s \<in> succ M1 (last seq) ?q1b" 
    by auto

  have "succ M2 (last seq) ?q2b = {}"
  proof (rule ccontr)
    assume "succ M2 (last seq) (target (butlast seq || tr2b) (initial M2)) \<noteq> {}"
    then obtain q2f where "q2f \<in> succ M2 (last seq) ?q2b"
      by blast
    then have "target ([last seq] || [q2f]) ?q2b = q2f" 
              "path M2 ([last seq] || [q2f]) ?q2b" 
              "length [q2f] = length [last seq]" 
      by auto
    then have "q2f \<in> io_targets M2 ?q2b [last seq]" 
      by (metis io_target_from_path)
    then have "io_targets M2 ?q2b [last seq] = {q2f}" 
      using assms(4) by (meson observable_io_target_is_singleton)

    
    have "io_targets M2 (initial M2) (butlast seq @ [last seq]) = {q2f}"
      using observable_io_targets_append[OF assms(4) \<open>io_targets M2 (initial M2) ?bls = {?q2b}\<close> 
            \<open>io_targets M2 ?q2b [last seq] = {q2f}\<close>] by assumption
    then have "seq \<in> L M2" 
      using \<open>seq = butlast seq @ [last seq]\<close> by auto
    then show "False"
      using \<open>seq \<notin> L M2\<close> by blast 
  qed

  have "?pIO \<in> L M1" "?pIO \<in> L M2" 
    using \<open>path M1 (?pIO || ?p1) (initial M1)\<close> \<open>path M2 (?pIO || ?p2) (initial M2)\<close> by auto
  then have "butlast (?pIO@[last seq]) \<in> L M1 \<inter> L M2"
    by auto

  have "?pIO@[last seq] \<in> L M1" 
    using observable_io_targets_append[OF assms(3) \<open>io_targets M1 (initial M1) ?pIO = {?q1b}\<close> 
          \<open>io_targets M1 ?q1b [last seq] = {q1s}\<close>] 
    by (metis all_not_in_conv insert_not_empty io_targets_elim language_state)
           
  moreover have "?pIO@[last seq] \<notin> L M2"
  proof
    assume "?pIO@[last seq] \<in> L M2"
    then obtain q2f where "io_targets M2 (initial M2) (?pIO@[last seq]) = {q2f}"
      by (meson assms(4) io_targets_observable_singleton_ob)
      
    have "io_targets M2 ?q2b [last seq] = {q2f}"
      using observable_io_targets_split[OF assms(4) 
            \<open>io_targets M2 (initial M2) (?pIO@[last seq]) = {q2f}\<close> 
            \<open>io_targets M2 (initial M2) (map fst p) = {?q2b}\<close>] by assumption

    then have "q2f \<in> succ M2 (last seq) ?q2b" 
      by (simp add: io_targets_succ)
    then show "False"
      using \<open>succ M2 (last seq) ?q2b = {}\<close> by auto
  qed

  ultimately have "?pIO@[last seq] \<in> L M1 - L M2"
    by auto


  have "sequence_to_failure M1 M2 (?pIO@[last seq])"
    using \<open>butlast (?pIO@[last seq]) \<in> L M1 \<inter> L M2\<close> \<open>?pIO@[last seq] \<in> L M1 - L M2\<close> by auto

  have "length (?pIO@[last seq]) = Suc (length ?pIO)"
    by auto
  then have "length (?pIO@[last seq]) \<le> |?PM|"
    using \<open>length p < |?PM|\<close> by auto

  
  have "card (nodes M2 \<times> nodes M1) \<le> |M2| * |M1|"
    by (simp add: card_cartesian_product)
  
  have "finite (nodes M2 \<times> nodes M1)"
  proof
    show "finite (nodes M2)" 
      using assms by auto
    show "finite (nodes M1)" 
      using assms by auto
  qed
    
  have "|?PM| \<le> |M2| * |M1|" 
    by (meson \<open>card (nodes M2 \<times> nodes M1) \<le> |M2| * |M1|\<close> \<open>finite (nodes M2 \<times> nodes M1)\<close> 
        card_mono dual_order.trans product_nodes)

  then have "length (?pIO@[last seq]) \<le> |M2| * |M1|"
    using \<open>length (?pIO@[last seq]) \<le> |?PM|\<close> by auto

  then have "sequence_to_failure M1 M2 (?pIO@[last seq]) \<and> length (?pIO@[last seq]) \<le> |M2| * |M1|" 
    using \<open>sequence_to_failure M1 M2 (?pIO@[last seq])\<close> by auto
  then show ?thesis
    by blast
qed



subsection \<open> Minimal sequence to failure extending \<close>

text \<open>
A minimal sequence to a failure extending some some set of IO-sequences is a sequence to a failure
of minimal length such that a prefix of that sequence is contained in the set.
\<close>


fun minimal_sequence_to_failure_extending :: 
  "'in list set \<Rightarrow> ('in,'out,'state) FSM \<Rightarrow> ('in,'out,'state) FSM \<Rightarrow> ('in \<times> 'out) list 
    \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> bool" where
  "minimal_sequence_to_failure_extending V M1 M2 v' io = (
   v' \<in> L\<^sub>i\<^sub>n M1 V \<and> sequence_to_failure M1 M2 (v' @ io) 
              \<and> \<not> (\<exists> io' . \<exists> w' \<in> L\<^sub>i\<^sub>n M1 V . sequence_to_failure M1 M2 (w' @ io') 
                                                            \<and> length io' < length io))"

lemma minimal_sequence_to_failure_extending_det_state_cover_ob :
  assumes "well_formed M1"
  and     "well_formed M2"
  and     "observable M2"
  and     "is_det_state_cover M2 V"
  and     "\<not> M1 \<preceq> M2"
obtains vs xs
where "minimal_sequence_to_failure_extending V M1 M2 vs xs" 
proof -
  \<comment> \<open>set of all IO-sequences that extend some reaction of M1 to V to a failure\<close>
  let ?exts = "{xs. \<exists>vs' \<in> L\<^sub>i\<^sub>n M1 V. sequence_to_failure M1 M2 (vs'@xs)}"
  
  \<comment> \<open>arbitrary sequence to failure\<close>
  \<comment> \<open>must be contained in ?exts as V contains the empty sequence\<close>
  obtain stf where "sequence_to_failure M1 M2 stf"
    using assms sequence_to_failure_ob by blast
  then have "sequence_to_failure M1 M2 ([] @ stf)" 
    by simp
  moreover have "[] \<in> L\<^sub>i\<^sub>n M1 V"
    by (meson assms(4) det_state_cover_initial language_state_for_inputs_empty)
  ultimately have "stf \<in> ?exts"
    by blast

  \<comment> \<open>the minimal length sequence of ?exts\<close>
  \<comment> \<open>is a minimal sequence to a failure extending V by construction\<close>
  let ?xsMin = "arg_min length (\<lambda>xs. xs \<in> ?exts)"
  have xsMin_def : "?xsMin \<in> ?exts 
                    \<and> (\<forall>xs \<in> ?exts. length  ?xsMin \<le> length xs)"
    by (metis (no_types, lifting) \<open>stf \<in> ?exts\<close> arg_min_nat_lemma) 
  then obtain vs where "vs \<in> L\<^sub>i\<^sub>n M1 V 
                        \<and> sequence_to_failure M1 M2 (vs @ ?xsMin)"
    by blast
  moreover have "\<not>(\<exists>xs . \<exists>ws \<in> L\<^sub>i\<^sub>n M1 V. sequence_to_failure M1 M2 (ws@xs) 
                                         \<and> length xs < length ?xsMin)"
    using leD xsMin_def by blast
  ultimately have "minimal_sequence_to_failure_extending V M1 M2 vs ?xsMin" 
    by auto
  then show ?thesis 
    using that by auto
qed
  
lemma mstfe_prefix_input_in_V :
  assumes "minimal_sequence_to_failure_extending V M1 M2 vs xs"
  shows "(map fst vs) \<in> V"
proof -
  have "vs \<in> L\<^sub>i\<^sub>n M1 V" 
    using assms by auto
  then show ?thesis 
    using language_state_for_inputs_map_fst_contained by auto
qed




subsection \<open> Complete test suite derived from the product machine \<close>

text \<open>
The classical result of testing FSMs for language inclusion :
Any failure can be observed by a sequence of length at
most n*m where n is the number of states of the reference 
model (here FSM @{verbatim M2}) and m is an upper bound on the number
of states of the SUT (here FSM @{verbatim M1}).
\<close>

lemma product_suite_soundness :
  assumes "well_formed M1"
  and     "well_formed M2"
  and     "observable M1"
  and     "observable M2"
  and     "inputs M2 = inputs M1"
  and     "|M1| \<le> m "
shows     "\<not> M1 \<preceq> M2 \<longrightarrow> \<not> M1 \<preceq>\<lbrakk>{xs . set xs \<subseteq> inputs M2 \<and> length xs \<le> |M2| * m}\<rbrakk> M2" 
  (is "\<not> M1 \<preceq> M2 \<longrightarrow> \<not> M1 \<preceq>\<lbrakk>?TS\<rbrakk> M2")
proof 
  assume "\<not> M1 \<preceq> M2"
  obtain stf where "sequence_to_failure M1 M2 stf \<and> length stf \<le> |M2| * |M1|"
    using sequence_to_failure_length[OF assms(1-4) \<open>\<not> M1 \<preceq> M2\<close>] by blast
  then have "sequence_to_failure M1 M2 stf" "length stf \<le> |M2| * |M1|"
    by auto

  then have "stf \<in> L M1"
    by auto
  let ?xs = "map fst stf"
  have "set ?xs \<subseteq> inputs M1"
    by (meson \<open>stf \<in> L M1\<close> assms(1) language_state_inputs)
  then have "set ?xs \<subseteq> inputs M2"
    using assms(5) by auto
 
  have "length ?xs \<le> |M2| * |M1|"
    using \<open>length stf \<le> |M2| * |M1|\<close> by auto 
  have "length ?xs \<le> |M2| * m"
  proof -
    show ?thesis
      by (metis (no_types) \<open>length (map fst stf) \<le> |M2| * |M1|\<close> \<open>|M1| \<le> m\<close> 
          dual_order.trans mult.commute mult_le_mono1)
  qed 

  have "stf \<in> L\<^sub>i\<^sub>n M1 {?xs}"
    by (meson \<open>stf \<in> L M1\<close> insertI1 language_state_for_inputs_map_fst)
  have "?xs \<in> ?TS" 
    using \<open>set ?xs \<subseteq> inputs M2\<close> \<open>length ?xs \<le> |M2| * m\<close> by blast
  have "stf \<in> L\<^sub>i\<^sub>n M1 ?TS"
    by (metis (no_types, lifting) \<open>map fst stf \<in> {xs. set xs \<subseteq> inputs M2 \<and> length xs \<le> |M2| * m}\<close> 
        \<open>stf \<in> L M1\<close> language_state_for_inputs_map_fst) 

  have "stf \<notin> L M2"
    using \<open>sequence_to_failure M1 M2 stf\<close> by auto
  then have "stf \<notin> L\<^sub>i\<^sub>n M2 ?TS"
    by auto 
    

  show "\<not> M1 \<preceq>\<lbrakk>?TS\<rbrakk> M2"
    using \<open>stf \<in> L\<^sub>i\<^sub>n M1 ?TS\<close> \<open>stf \<notin> L\<^sub>i\<^sub>n M2 ?TS\<close> by blast
qed


lemma product_suite_completeness :
  assumes "well_formed M1"
  and     "well_formed M2"
  and     "observable M1"
  and     "observable M2"
  and     "inputs M2 = inputs M1"
  and     "|M1| \<le> m "
shows     "M1 \<preceq> M2 \<longleftrightarrow> M1 \<preceq>\<lbrakk>{xs . set xs \<subseteq> inputs M2 \<and> length xs \<le> |M2| * m}\<rbrakk> M2" 
  (is "M1 \<preceq> M2 \<longleftrightarrow> M1 \<preceq>\<lbrakk>?TS\<rbrakk> M2")
proof 
  show "M1 \<preceq> M2 \<Longrightarrow> M1 \<preceq>\<lbrakk>?TS\<rbrakk> M2" \<comment> \<open>soundness holds trivially\<close>
    unfolding language_state_for_inputs.simps io_reduction.simps by blast
  show "M1 \<preceq>\<lbrakk>?TS\<rbrakk> M2 \<Longrightarrow> M1 \<preceq> M2"
    using product_suite_soundness[OF assms] by auto
qed


end