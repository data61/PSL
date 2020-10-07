section \<open> Sequent Calculus \<close>

theory utp_sequent
  imports utp_pred_laws
begin

definition sequent :: "'\<alpha> upred \<Rightarrow> '\<alpha> upred \<Rightarrow> bool" (infixr "\<tturnstile>" 15) where
[upred_defs]: "sequent P Q = (Q \<sqsubseteq> P)"

abbreviation sequent_triv ("\<tturnstile> _" [15] 15) where "\<tturnstile> P \<equiv> (true \<tturnstile> P)"

translations
  "\<tturnstile> P" <= "true \<tturnstile> P"

lemma sTrue: "P \<tturnstile> true"
  by pred_auto

lemma sAx: "P \<tturnstile> P"
  by pred_auto

lemma sNotI: "\<Gamma> \<and> P \<tturnstile> false \<Longrightarrow> \<Gamma> \<tturnstile> \<not> P"
  by pred_auto

lemma sConjI: "\<lbrakk> \<Gamma> \<tturnstile> P; \<Gamma> \<tturnstile> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<tturnstile> P \<and> Q"
  by pred_auto

lemma sImplI: "\<lbrakk> (\<Gamma> \<and> P) \<tturnstile> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<tturnstile> (P \<Rightarrow> Q)"
  by pred_auto

end