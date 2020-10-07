section \<open>Memoization\<close>

subsection \<open>Memory Implementations for the State Monad\<close>

theory Memory
  imports "DP_CRelVS" "HOL-Library.Mapping"
begin

lemma lift_pI[intro?]:
  "lift_p P f" if "\<And> heap x heap'. P heap \<Longrightarrow> run_state f heap = (x, heap') \<Longrightarrow> P heap'"
  unfolding lift_p_def by (auto intro: that)

lemma mem_correct_default:
  "mem_correct
    (\<lambda> k. do {m \<leftarrow> State_Monad.get; State_Monad.return (m k)})
    (\<lambda> k v. do {m \<leftarrow> State_Monad.get; State_Monad.set (m(k\<mapsto>v))})
    (\<lambda> _. True)"
  by standard
    (auto simp: map_le_def state_mem_defs.map_of_def State_Monad.bind_def State_Monad.get_def State_Monad.return_def State_Monad.set_def lift_p_def)


lemma mem_correct_rbt_mapping:
  "mem_correct
    (\<lambda> k. do {m \<leftarrow> State_Monad.get; State_Monad.return (Mapping.lookup m k)})
    (\<lambda> k v. do {m \<leftarrow> State_Monad.get; State_Monad.set (Mapping.update k v m)})
    (\<lambda> _. True)"
  by standard
     (auto simp:
        map_le_def state_mem_defs.map_of_def State_Monad.bind_def State_Monad.get_def State_Monad.return_def State_Monad.set_def lookup_update' lift_p_def
     )



locale mem_correct_empty = mem_correct +
  fixes empty
  assumes empty_correct: "map_of empty \<subseteq>\<^sub>m Map.empty" and P_empty: "P empty"

lemma (in mem_correct_empty) dom_empty[simp]:
  "dom (map_of empty) = {}"
  using empty_correct by (auto dest: map_le_implies_dom_le)

lemma mem_correct_empty_default:
  "mem_correct_empty
    (\<lambda> k. do {m \<leftarrow> State_Monad.get; State_Monad.return (m k)})
    (\<lambda> k v. do {m \<leftarrow> State_Monad.get; State_Monad.set (m(k\<mapsto>v))})
    (\<lambda> _. True)
    Map.empty"
  by (intro mem_correct_empty.intro[OF mem_correct_default] mem_correct_empty_axioms.intro)
     (auto simp: state_mem_defs.map_of_def map_le_def State_Monad.bind_def State_Monad.get_def State_Monad.return_def)

lemma mem_correct_rbt_empty_mapping:
  "mem_correct_empty
    (\<lambda> k. do {m \<leftarrow> State_Monad.get; State_Monad.return (Mapping.lookup m k)})
    (\<lambda> k v. do {m \<leftarrow> State_Monad.get; State_Monad.set (Mapping.update k v m)})
    (\<lambda> _. True)
    Mapping.empty"
  by (intro mem_correct_empty.intro[OF mem_correct_rbt_mapping] mem_correct_empty_axioms.intro)
     (auto simp: state_mem_defs.map_of_def map_le_def State_Monad.bind_def State_Monad.get_def State_Monad.return_def lookup_empty)

locale dp_consistency_empty =
  dp_consistency + mem_correct_empty
begin

lemma cmem_empty:
  "cmem empty"
  using empty_correct unfolding cmem_def by auto

corollary memoization_correct:
  "dp x = v" "cmem m" if "consistentDP dp\<^sub>T" "State_Monad.run_state (dp\<^sub>T x) empty = (v, m)"
  using that unfolding consistentDP_def
  by (auto dest!: rel_funD[where x = x] elim!: crel_vs_elim intro: P_empty cmem_empty)

lemma memoized:
  "dp x = fst (State_Monad.run_state (dp\<^sub>T x) empty)" if "consistentDP dp\<^sub>T"
  using surjective_pairing memoization_correct(1)[OF that] by blast

lemma cmem_result:
  "cmem (snd (State_Monad.run_state (dp\<^sub>T x) empty))" if "consistentDP dp\<^sub>T"
  using surjective_pairing memoization_correct(2)[OF that] by blast

end (* DP Consistency Empty *)

locale dp_consistency_default =
  fixes dp :: "'param \<Rightarrow> 'result"
begin

sublocale dp_consistency_empty
  "\<lambda> k. do {(m::'param \<rightharpoonup> 'result) \<leftarrow> State_Monad.get; State_Monad.return (m k)}"
  "\<lambda> k v. do {m \<leftarrow> State_Monad.get; State_Monad.set (m(k\<mapsto>v))}"
  "\<lambda> (_::'param \<rightharpoonup> 'result). True"
  dp
  Map.empty
  by (intro
      dp_consistency_empty.intro dp_consistency.intro mem_correct_default mem_correct_empty_default
     )

end (* DP Consistency Default *)

locale dp_consistency_mapping =
  fixes dp :: "'param \<Rightarrow> 'result"
begin

sublocale dp_consistency_empty
  "(\<lambda> k. do {(m::('param,'result) mapping) \<leftarrow> State_Monad.get; State_Monad.return (Mapping.lookup m k)})"
    "(\<lambda> k v. do {m \<leftarrow> State_Monad.get; State_Monad.set (Mapping.update k v m)})"
    "(\<lambda> _::('param,'result) mapping. True)" dp Mapping.empty
  by (intro
      dp_consistency_empty.intro dp_consistency.intro mem_correct_rbt_mapping
      mem_correct_rbt_empty_mapping
     )

end (* DP Consistency RBT *)

subsubsection \<open>Tracing Memory\<close>
context state_mem_defs
begin

definition
  "lookup_trace k =
  State (\<lambda> (log, m). case State_Monad.run_state (lookup k) m of
    (None, m) \<Rightarrow> (None, ((''Missed'', k) # log, m)) |
    (Some v, m) \<Rightarrow> (Some v, ((''Found'', k) # log, m))
  )"

definition
  "update_trace k v =
  State (\<lambda> (log, m). case State_Monad.run_state (update k v) m of
    (_, m) \<Rightarrow> ((), ((''Stored'', k) # log, m))
  )"

end

context mem_correct
begin

lemma map_of_simp:
  "state_mem_defs.map_of lookup_trace = map_of o snd"
  unfolding state_mem_defs.map_of_def lookup_trace_def
  by (rule ext) (auto split: prod.split option.split)

lemma mem_correct_tracing: "mem_correct lookup_trace update_trace (P o snd)"
  by standard
    (auto
      intro!: lift_pI
      elim: lift_p_P[OF lookup_inv]
      simp: lookup_trace_def update_trace_def state_mem_defs.map_of_def map_of_simp
      split: prod.splits option.splits;
      metis snd_conv lookup_correct update_correct lift_p_P update_inv lookup_inv lift_p_P
   )+

end

context mem_correct_empty
begin

lemma mem_correct_tracing_empty:
  "mem_correct_empty lookup_trace update_trace (P o snd) ([], empty)"
  by (intro mem_correct_empty.intro mem_correct_tracing mem_correct_empty_axioms.intro)
     (simp add: map_of_simp empty_correct P_empty)+

end

locale dp_consistency_mapping_tracing =
  fixes dp :: "'param \<Rightarrow> 'result"
begin

interpretation mapping: dp_consistency_mapping .

sublocale dp_consistency_empty
  mapping.lookup_trace mapping.update_trace "(\<lambda> _. True) o snd" dp "([], Mapping.empty)"
  by (rule
      dp_consistency_empty.intro dp_consistency.intro
      mapping.mem_correct_tracing_empty mem_correct_empty.axioms(1)
     )+

end (* DP Consistency RBT *)

end (* Theory *)
