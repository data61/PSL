section \<open>Example\<close>

theory HMM_Example
  imports
    HMM_Implementation
    "HOL-Library.AList_Mapping"
begin

text \<open>
  We would like to implement mappings as red-black trees
  but they require the key type to be linearly ordered.
  Unfortunately, \<open>HOL-Analysis\<close> fixes the product order to the element-wise order
  and thus we cannot restore a linear order,
  and the red-black tree implementation (from \<open>HOL-Library\<close>) cannot be used.
\<close>

text \<open>The ice cream example from Jurafsky and Martin \cite{Jurafsky}.\<close>

definition
  "states = [''start'', ''hot'', ''cold'', ''end'']"

definition observations :: "int list" where
  "observations = [0, 1, 2, 3]"

definition
  "kernel =
    [
      (''start'', [(''hot'',0.8 :: real), (''cold'',0.2)]),
      (''hot'',   [(''hot'',0.6 :: real), (''cold'',0.3), (''end'', 0.1)]),
      (''cold'',  [(''hot'',0.4 :: real), (''cold'',0.5), (''end'', 0.1)]),
      (''end'',   [(''end'', 1)])
    ]"

definition
  "emissions =
    [
      (''hot'',   [(1, 0.2), (2, 0.4), (3, 0.4)]),
      (''cold'',  [(1, 0.5), (2, 0.4), (3, 0.1)]),
      (''end'',   [(0, 1)])
    ]
  "

global_interpretation Concrete_HMM kernel emissions observations states
  defines
      viterbi_rec   = HMM_interp.viterbi_ix\<^sub>m'
  and viterbi       = HMM_interp.viterbi
  and viterbi_final = HMM_interp.viterbi_final
  and forward_rec   = HMM_interp.forward_ix\<^sub>m'
  and forward       = HMM_interp.forward
  and likelihood    = HMM_interp.likelihood_compute
  by (standard; eval)

lemmas [code] = HMM_interp.viterbi_ix\<^sub>m'.simps[unfolded O_code K_code]

lemmas [code] = HMM_interp.forward_ix\<^sub>m'.simps[unfolded O_code K_code]

value "likelihood ''start'' [1, 1, 1]"

text \<open>
  If we enforce the last observation to correspond to @{term \<open>''end''\<close>},
  then @{term forward} and @{term likelihood} yield the same result.
\<close>
value "likelihood ''start'' [1, 1, 1, 0]"

value "forward ''start'' ''end'' [1, 1, 1, 0]"

value "forward ''start'' ''end'' [3, 3, 3, 0]"

value "forward ''start'' ''end'' [3, 1, 3, 0]"

value "forward ''start'' ''end'' [3, 1, 3, 1, 0]"

value "viterbi ''start'' ''end'' [1, 1, 1, 0]"

value "viterbi ''start'' ''end'' [3, 3, 3, 0]"

value "viterbi ''start'' ''end'' [3, 1, 3, 0]"

value "viterbi ''start'' ''end'' [3, 1, 3, 1, 0]"

text \<open>
  If we enforce the last observation to correspond to @{term \<open>''end''\<close>},
  then @{term viterbi} and @{term viterbi_final} yield the same result.
\<close>
value "viterbi_final ''start'' [3, 1, 3, 1, 0]"

value "viterbi_final ''start'' [1, 1, 1, 1, 1, 1, 1, 0]"

value "viterbi_final ''start'' [1, 1, 1, 1, 1, 1, 1, 1]"

end