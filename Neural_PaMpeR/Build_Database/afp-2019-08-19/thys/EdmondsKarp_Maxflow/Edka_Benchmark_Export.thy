section \<open>Exporting Code\<close>
theory Edka_Benchmark_Export 
imports Edka_Checked_Impl
begin

text \<open>Moved to own theory, as code-export makes theory unusable for inclusion from
other AFP entries. \<close>

export_code nat_of_integer integer_of_nat int_of_integer integer_of_int
  edmonds_karp edka_imp edka_imp_tabulate edka_imp_run prepareNet
  compute_flow_val_imp edmonds_karp_val
  in SML_imp 
  module_name Fofu 
  file \<open>evaluation/fofu-SML/Fofu_Export.sml\<close>  


end
