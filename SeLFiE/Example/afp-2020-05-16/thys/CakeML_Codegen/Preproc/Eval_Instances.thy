section \<open>Default instances\<close>

theory Eval_Instances
imports Embed
begin

ML_file "eval_instances.ML"

setup \<open>Eval_Instances.setup\<close>

derive evaluate nat bool list unit prod sum option char num name "term"

end
