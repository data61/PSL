theory UnwindingConditions
imports "../Basics/BSPTaxonomy"
  "../../SystemSpecification/StateEventSystems"
begin

locale Unwinding =
fixes SES :: "('s, 'e) SES_rec"
and \<V> :: "'e V_rec"

assumes validSES: "SES_valid SES"
and validVU: "isViewOn \<V> E\<^bsub>SES\<^esub>"

(* sublocale relations for Unwinding *)
sublocale Unwinding \<subseteq> BSPTaxonomyDifferentCorrections "induceES SES" "\<V>"
  by (unfold_locales, simp add: induceES_yields_ES validSES,
    simp add: induceES_def validVU)

(* body of Unwinding *)
context Unwinding
begin

(* output step consistency (osc) *)
definition osc :: "'s rel \<Rightarrow> bool"
where
"osc ur \<equiv> 
  \<forall>s1 \<in> S\<^bsub>SES\<^esub>. \<forall>s1' \<in> S\<^bsub>SES\<^esub>. \<forall>s2' \<in> S\<^bsub>SES\<^esub>. \<forall>e \<in> (E\<^bsub>SES\<^esub> - C\<^bsub>\<V>\<^esub>).
    (reachable SES s1 \<and> reachable SES s1' 
       \<and> s1' e\<longrightarrow>\<^bsub>SES\<^esub> s2' \<and> (s1', s1) \<in> ur)
    \<longrightarrow> (\<exists>s2 \<in> S\<^bsub>SES\<^esub>. \<exists>\<delta>. \<delta> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and> \<delta> \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [e] \<upharpoonleft> V\<^bsub>\<V>\<^esub> 
          \<and> s1 \<delta>\<Longrightarrow>\<^bsub>SES\<^esub> s2 \<and> (s2', s2) \<in> ur)"

(* locally-respects forwards (lrf) *)
definition lrf :: "'s rel \<Rightarrow> bool"
where
"lrf ur \<equiv> 
  \<forall>s \<in> S\<^bsub>SES\<^esub>. \<forall>s' \<in> S\<^bsub>SES\<^esub>. \<forall>c \<in> C\<^bsub>\<V>\<^esub>. 
  ((reachable SES s \<and> s c\<longrightarrow>\<^bsub>SES\<^esub> s') \<longrightarrow> (s', s) \<in> ur)"

(* locally-respects backwards (lrb) *)
definition lrb :: "'s rel \<Rightarrow> bool"
where
"lrb ur \<equiv> \<forall>s \<in> S\<^bsub>SES\<^esub>. \<forall>c \<in> C\<^bsub>\<V>\<^esub>. 
  (reachable SES s \<longrightarrow> (\<exists>s' \<in> S\<^bsub>SES\<^esub>. (s c\<longrightarrow>\<^bsub>SES\<^esub> s' \<and> ((s, s') \<in> ur))))"

(* forward-correctably respects forwards (fcrf) *)
definition fcrf :: "'e Gamma \<Rightarrow> 's rel \<Rightarrow> bool"
where
"fcrf \<Gamma> ur \<equiv> 
  \<forall>c \<in> (C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>). \<forall>v \<in> (V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>). \<forall>s \<in> S\<^bsub>SES\<^esub>. \<forall>s' \<in> S\<^bsub>SES\<^esub>.
    ((reachable SES s \<and> s ([c] @ [v])\<Longrightarrow>\<^bsub>SES\<^esub> s')
      \<longrightarrow> (\<exists>s'' \<in> S\<^bsub>SES\<^esub>. \<exists>\<delta>. (\<forall>d \<in> (set \<delta>). d \<in> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>)) \<and>
             s (\<delta> @ [v])\<Longrightarrow>\<^bsub>SES\<^esub> s'' \<and> (s', s'') \<in> ur))"

(* forward-correctably respects backwards (fcrb) *)
definition fcrb :: "'e Gamma \<Rightarrow> 's rel \<Rightarrow> bool"
where 
"fcrb \<Gamma> ur \<equiv> 
  \<forall>c \<in> (C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>). \<forall>v \<in> (V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>). \<forall>s \<in> S\<^bsub>SES\<^esub>. \<forall>s'' \<in> S\<^bsub>SES\<^esub>.
  ((reachable SES s \<and> s v\<longrightarrow>\<^bsub>SES\<^esub> s'')
    \<longrightarrow> (\<exists>s' \<in> S\<^bsub>SES\<^esub>. \<exists>\<delta>. (\<forall>d \<in> (set \<delta>). d \<in> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>)) \<and>
          s ([c] @ \<delta> @ [v])\<Longrightarrow>\<^bsub>SES\<^esub> s' \<and> (s'', s') \<in> ur))"

(* \<rho>-enabledness *)
definition En :: "'e Rho \<Rightarrow> 's \<Rightarrow> 'e \<Rightarrow> bool"
where
"En \<rho> s e \<equiv> 
  \<exists>\<beta> \<gamma>. \<exists>s' \<in> S\<^bsub>SES\<^esub>. \<exists>s'' \<in> S\<^bsub>SES\<^esub>.
    s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s \<and> (\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)) 
     \<and> s0\<^bsub>SES\<^esub> \<gamma>\<Longrightarrow>\<^bsub>SES\<^esub> s' \<and> s' e\<longrightarrow>\<^bsub>SES\<^esub> s''"

(* locally-respects backwards for enabled events (lrbe) *)
definition lrbe :: "'e Rho \<Rightarrow> 's rel \<Rightarrow> bool"
where
"lrbe \<rho> ur \<equiv> 
  \<forall>s \<in> S\<^bsub>SES\<^esub>. \<forall>c \<in> C\<^bsub>\<V>\<^esub> .  
  ((reachable SES s \<and> (En \<rho> s c)) 
    \<longrightarrow> (\<exists>s' \<in> S\<^bsub>SES\<^esub>. (s c\<longrightarrow>\<^bsub>SES\<^esub> s' \<and> (s, s') \<in> ur)))"

(* forward-correctable respects backwards for enabled events (fcrbe) *)
definition fcrbe :: "'e Gamma \<Rightarrow> 'e Rho \<Rightarrow> 's rel \<Rightarrow> bool"
where
"fcrbe \<Gamma> \<rho> ur \<equiv> 
  \<forall>c \<in> (C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>). \<forall>v \<in> (V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>). \<forall>s \<in> S\<^bsub>SES\<^esub>. \<forall>s'' \<in> S\<^bsub>SES\<^esub>.
  ((reachable SES s \<and> s v\<longrightarrow>\<^bsub>SES\<^esub> s'' \<and> (En \<rho> s c))
    \<longrightarrow> (\<exists>s' \<in> S\<^bsub>SES\<^esub>. \<exists>\<delta>. (\<forall>d \<in> (set \<delta>). d \<in> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>)) \<and>
           s ([c] @ \<delta> @ [v])\<Longrightarrow>\<^bsub>SES\<^esub> s' \<and> (s'', s') \<in> ur))"

end

end
