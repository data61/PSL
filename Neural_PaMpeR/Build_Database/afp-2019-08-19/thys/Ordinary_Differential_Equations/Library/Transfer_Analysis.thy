theory Transfer_Analysis
imports "HOL-Analysis.Analysis"
begin

text \<open>TODO: make this theory available much earlier! \<close>

context includes lifting_syntax begin
lemma Sigma_transfer[transfer_rule]:
  "(rel_set A ===> (A ===> rel_set B) ===> rel_set (rel_prod A B)) Sigma Sigma"
  unfolding Sigma_def
  by transfer_prover
end

subsection \<open>Parametricity rules for analysis constants\<close>

context includes lifting_syntax begin

lemma less_transfer[transfer_rule]:
  "(A ===> A ===> (=)) less less"
  if [transfer_rule]: "bi_unique A" "(A ===> A ===> (=)) less_eq less_eq"
  for A::"'c::order \<Rightarrow> 'd::order \<Rightarrow> bool"
  unfolding order.strict_iff_order[abs_def]
  by transfer_prover

lemma norm_transfer[transfer_rule]:
  "(A ===> (=)) norm norm"
  if [transfer_rule]: "(A ===> A ===> (=)) inner inner"
  unfolding norm_eq_sqrt_inner
  by transfer_prover

lemma dist_transfer[transfer_rule]:
  "(A ===> A ===> (=)) dist dist"
  if [transfer_rule]: "(A ===> (=)) norm norm" "(A ===> A ===> A) (-) (-)"
  unfolding dist_norm
  by transfer_prover

lemma open_transfer[transfer_rule]:
  "(rel_set A ===> (=)) open open"
  if [transfer_rule]: "bi_unique A" "bi_total A" "(A ===> A ===> (=)) dist dist"
  unfolding open_dist
  by transfer_prover

lemma closed_transfer[transfer_rule]:
  "(rel_set A ===> (=)) closed closed"
  if [transfer_rule]: "bi_unique A" "bi_total A" "(rel_set A ===> (=)) open open"
  unfolding closed_def
  by transfer_prover

lemma sgn_transfer[transfer_rule]:
  "(A ===> A) sgn sgn"
  if [transfer_rule]: "(A ===> (=)) norm norm" "((=) ===> A ===> A) scaleR scaleR"
  unfolding sgn_div_norm
  by transfer_prover

lemma uniformity_transfer[transfer_rule]:
  "(rel_filter (rel_prod A A)) uniformity uniformity"
  if [transfer_rule]: "bi_total A"  "bi_unique A" "(A ===> A ===> (=)) dist dist"
  unfolding uniformity_dist
  by transfer_prover

lemma lipschitz_on_transfer[transfer_rule]:
  "((=) ===> (rel_set A) ===> (A ===> B) ===> (=)) lipschitz_on lipschitz_on"
  if [transfer_rule]: "(B ===> B ===> (=)) dist dist" "(A ===> A ===> (=)) dist dist"
  unfolding lipschitz_on_def by transfer_prover

lemma cball_transfer[transfer_rule]:
  "(A ===> (=) ===> rel_set A) cball cball"
  if [transfer_rule]: "bi_total A" "(A ===> A ===> (=)) dist dist"
  unfolding cball_def by transfer_prover

lemma ball_transfer[transfer_rule]:
  "(A ===> (=) ===> rel_set A) ball ball"
  if [transfer_rule]: "bi_total A" "(A ===> A ===> (=)) dist dist"
  unfolding ball_def by transfer_prover

lemma local_lipschitz_transfer[transfer_rule]:
  "(rel_set A ===> rel_set B ===> (A ===> B ===> C) ===> (=)) local_lipschitz local_lipschitz"
  if [transfer_rule]: "bi_total A" "bi_unique A" "bi_total B" "bi_unique B"
    "(A ===> A ===> (=)) dist dist"
    "(B ===> B ===> (=)) dist dist"
    "(C ===> C ===> (=)) dist dist"
  unfolding local_lipschitz_def
  by transfer_prover

lemma filterlim_transfer[transfer_rule]:
  "((A ===> B) ===> rel_filter B ===> rel_filter A ===> (=)) filterlim filterlim"
  if [transfer_rule]: "bi_unique B"
  unfolding filterlim_iff
  by transfer_prover

lemma nhds_transfer[transfer_rule]:
  "(A ===> rel_filter A) nhds nhds"
  if [transfer_rule]: "bi_unique A" "bi_total A" "(rel_set A ===> (=)) open open"
  unfolding nhds_def
  by transfer_prover

lemma at_within_transfer[transfer_rule]:
  "(A ===> rel_set A ===> rel_filter A) at_within at_within"
  if [transfer_rule]: "bi_unique A" "bi_total A" "(rel_set A ===> (=)) open open"
  unfolding at_within_def
  by transfer_prover

lemma continuous_on_transfer[transfer_rule]:
  "(rel_set A ===> (A ===> B) ===> (=)) continuous_on continuous_on"
  if [transfer_rule]: "bi_unique A" "bi_total A" "(rel_set A ===> (=)) open open"
    "bi_unique B" "bi_total B" "(rel_set B ===> (=)) open open"
  unfolding continuous_on_def
  by transfer_prover

lemma is_interval_transfer[transfer_rule]: "(rel_set A ===> (=)) is_interval is_interval"
  if [transfer_rule]: "bi_unique A" "bi_total A" "(A ===> A ===> (=)) inner inner" "(rel_set A) Basis Basis"
  unfolding is_interval_def
  by transfer_prover

lemma additive_transfer[transfer_rule]:
  "((B ===> A) ===> (=)) Modules.additive Modules.additive"
  if [transfer_rule]:
    "bi_unique A"
    "bi_total B"
    "(A ===> A ===> A) (+) (+)"
    "(B ===> B ===> B) (+) (+)"
  unfolding Modules.additive_def
  by transfer_prover

lemma linear_transfer[transfer_rule]: "((B ===> A) ===> (=)) linear linear"
  if [transfer_rule]:
    "bi_unique A"
    "bi_total B"
    "(A ===> A ===> A) (+) (+)"
    "((=) ===> A ===> A) (*\<^sub>R) (*\<^sub>R)"
    "(B ===> B ===> B) (+) (+)"
    "((=) ===> B ===> B) (*\<^sub>R) (*\<^sub>R)"
  unfolding linear_iff
  by transfer_prover

lemma bounded_linear_transfer[transfer_rule]: "((B ===> A) ===> (=)) bounded_linear bounded_linear"
  if [transfer_rule]:
    "bi_unique A"
    "bi_total B"
    "(A ===> A ===> A) (+) (+)"
    "((=) ===> A ===> A) (*\<^sub>R) (*\<^sub>R)"
    "(B ===> B ===> B) (+) (+)"
    "((=) ===> B ===> B) (*\<^sub>R) (*\<^sub>R)"
    "(A ===> (=)) norm norm"
    "(B ===> (=)) norm norm"
  unfolding bounded_linear_def bounded_linear_axioms_def
  by transfer_prover

lemma Pi_transfer[transfer_rule]: "(rel_set B ===> (B ===> rel_set A) ===> rel_set (B ===> A)) FuncSet.Pi FuncSet.Pi"
  if [transfer_rule]: "bi_unique A" "bi_total A" "bi_unique B" "bi_total B"
  unfolding FuncSet.Pi_def
  by transfer_prover

lift_definition rel_blinfun:: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow>
  ('a::real_normed_vector \<Rightarrow>\<^sub>L 'c::real_normed_vector) \<Rightarrow> ('b::real_normed_vector \<Rightarrow>\<^sub>L 'd::real_normed_vector) \<Rightarrow> bool" is rel_fun .

lemma bi_unique_rel_blinfun[transfer_rule]:
  "bi_total A \<Longrightarrow> bi_unique B \<Longrightarrow> bi_unique (rel_blinfun A B)"
  using bi_unique_fun[of A B]
  unfolding bi_unique_def
  by transfer auto

lemma bi_total_rel_blinfun[transfer_rule]:
  "bi_total (rel_blinfun A B)"
  if
    "bi_unique A" "bi_total B" (* really? *)
    "bi_unique B" "bi_total A"
    "(B ===> B ===> B) (+) (+)"
    "((=) ===> B ===> B) (*\<^sub>R) (*\<^sub>R)"
    "(A ===> A ===> A) (+) (+)"
    "((=) ===> A ===> A) (*\<^sub>R) (*\<^sub>R)"
    "(B ===> (=)) norm norm"
    "(A ===> (=)) norm norm"
  using bounded_linear_transfer[OF that(3-)]
  using bi_total_fun[OF that(1,2)]
  unfolding bi_total_def
  apply (transfer fixing: A B)
  apply auto
    subgoal for x
      apply (drule spec[where x=x])
      apply auto
      apply (drule rel_funD, assumption)
      apply fastforce
      done
    subgoal for x
      apply (drule spec[where x=x])
      apply auto
      apply (drule rel_funD, assumption)
      apply fastforce
      done
    done

lemma blinfun_apply_transfer[transfer_rule]:
  "(rel_blinfun A B ===> A ===> B) blinfun_apply blinfun_apply"
  by (auto simp: rel_blinfun_def)

lemma norm_blinfun_transfer[transfer_rule]: "(rel_blinfun A A ===> (=)) norm norm"
  if [transfer_rule]: "(A ===> (=)) norm norm" "(rel_set A) UNIV UNIV"
  unfolding norm_blinfun.rep_eq
  unfolding onorm_def
  by transfer_prover

lemma minus_blinfun_transfer[transfer_rule]:
  "(rel_blinfun A B ===> rel_blinfun A B ===> rel_blinfun A B) (-) (-)"
  if "(B ===> B ===> B) (-) (-)"
  using that
  apply (auto simp: rel_blinfun_def blinfun.bilinear_simps
      intro!: rel_funI dest: rel_funD)
  by (metis rel_funD)

lemma compose_blinfun_transfer[transfer_rule]:"(rel_blinfun A B ===> rel_blinfun C A ===> rel_blinfun C B) (o\<^sub>L) (o\<^sub>L)"
  apply (auto simp: rel_blinfun_def blinfun.bilinear_simps
      intro!: rel_funI dest: rel_funD)
  by (metis rel_funD)

end

end