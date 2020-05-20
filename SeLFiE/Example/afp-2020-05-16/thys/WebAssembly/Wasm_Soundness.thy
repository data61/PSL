section \<open>Soundness Theorems\<close>

theory Wasm_Soundness imports Main Wasm_Properties begin

theorem preservation:
  assumes "\<turnstile>_i s;vs;es : ts"
          "\<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>"
  shows "\<turnstile>_i s';vs';es' : ts"
proof -
  obtain \<S> where "store_typing s \<S>" "\<S>\<bullet>None \<tturnstile>_i vs;es : ts"
    using assms(1) config_typing.simps
    by blast
  hence "store_typing s' \<S>" "\<S>\<bullet>None \<tturnstile>_i vs';es' : ts"
    using assms(2) store_preserved types_preserved_e
    by simp_all
  thus ?thesis
    using config_typing.intros
    by blast
qed

theorem progress:
  assumes "\<turnstile>_i s;vs;es : ts"
  shows "const_list es \<or> es = [Trap] \<or> (\<exists>a s' vs' es'. \<lparr>s;vs;es\<rparr> \<leadsto>_i \<lparr>s';vs';es'\<rparr>)"
proof -
  obtain \<S> where "store_typing s \<S>" "\<S>\<bullet>None \<tturnstile>_i vs;es : ts"
    using assms config_typing.simps
    by blast
  thus ?thesis
    using progress_e3
    by blast
qed

end