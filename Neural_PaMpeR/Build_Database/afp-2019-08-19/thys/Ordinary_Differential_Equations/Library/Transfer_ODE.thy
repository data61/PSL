theory Transfer_ODE
  imports Transfer_Analysis
    Ordinary_Differential_Equations.ODE_Analysis
    "List-Index.List_Index"
begin

context includes lifting_syntax begin

lemma index_transfer[transfer_rule]:
  "(list_all2 A ===> A ===> (=)) index index"
  if [transfer_rule]: "bi_unique A"
  unfolding index_def find_index_def
  by transfer_prover

lemma interval_transfer[transfer_rule]: "(rel_set A ===> (=)) interval interval"
  if [transfer_rule]: "bi_unique A" "bi_total A" "(A ===> A ===> (=)) inner inner" "(rel_set A) Basis Basis"
  unfolding interval_def
  by transfer_prover

lemma ll_on_open_transfer[transfer_rule]:
  "(rel_set A ===> (A ===> B ===> C) ===> (rel_set B) ===> (=)) ll_on_open ll_on_open"
  if [transfer_rule]:
    "bi_unique A" "bi_total A" "(A ===> A ===> (=)) dist dist" "(A ===> A ===> (=)) inner inner" "(rel_set A) Basis Basis"
    "bi_unique B" "bi_total B" "(B ===> B ===> (=)) dist dist"
    "bi_unique C" "bi_total C" "(C ===> C ===> (=)) dist dist"
  unfolding ll_on_open_def ll_on_open_axioms_def
  by transfer_prover

lemma auto_ll_on_open_transfer[transfer_rule]:
  "((A ===> A) ===> (rel_set A) ===> (=)) auto_ll_on_open auto_ll_on_open"
  if [transfer_rule]: "bi_unique A" "bi_total A" "(A ===> A ===> (=)) dist dist"
  unfolding auto_ll_on_open_def ll_on_open_axioms_def
  by transfer_prover

lemma has_vderiv_on_transfer[transfer_rule]:
  "(((=) ===> A) ===> ((=) ===> A) ===> rel_set (=) ===> (=)) (has_vderiv_on) (has_vderiv_on)"
  if [transfer_rule]:
    "A 0 0" "bi_unique A" "bi_total A" "(rel_set A ===> (=)) open open"
    "((=) ===> A ===> A) (*\<^sub>R) (*\<^sub>R)"
    "(A ===> A ===> A) (+) (+)"
    "(A ===> A ===> A) (-) (-)"
    "(A ===> (=)) norm norm"
  unfolding has_vderiv_on_def has_vector_derivative_def has_derivative_within
  by transfer_prover

lemma solves_ode_transfer[transfer_rule]:
  "(((=) ===> A) ===> ((=) ===> A ===> A)  ===> rel_set (=) ===> rel_set A ===> (=)) (solves_ode) (solves_ode)"
  if [transfer_rule]:
    "A 0 0" "bi_unique A" "bi_total A" "(rel_set A ===> (=)) open open"
    "((=) ===> A ===> A) (*\<^sub>R) (*\<^sub>R)"
    "(A ===> A ===> A) (+) (+)"
    "(A ===> A ===> A) (-) (-)"
    "(A ===> (=)) norm norm"
  unfolding solves_ode_def
  by transfer_prover


lemma c1_on_open_transfer[transfer_rule]:
  "((A ===> A) ===> (A ===> rel_blinfun A A) ===> rel_set A ===> (=)) c1_on_open c1_on_open"
  if [transfer_rule]:
    "bi_unique A" "bi_total A"
    "(A ===> A ===> A) (+) (+)"
    "(A ===> A ===> A) (-) (-)"
    "((=) ===> A ===> A) (*\<^sub>R) (*\<^sub>R)"
    "(A ===> (=)) norm norm"
    "A 0 0"
  unfolding c1_on_open_def has_derivative_at
  by transfer_prover

end

end