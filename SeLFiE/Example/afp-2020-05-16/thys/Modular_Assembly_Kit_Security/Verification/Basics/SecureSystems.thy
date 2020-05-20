theory SecureSystems
imports "../../SystemSpecification/StateEventSystems"
  "../../SecuritySpecification/InformationFlowProperties"
begin

locale SecureESIFP =
fixes ES :: "'e ES_rec"
and IFP :: "'e IFP_type"

assumes validES: "ES_valid ES"
and validIFPES: "IFP_valid E\<^bsub>ES\<^esub> IFP"

(* sublocale relations for SecureESIFP *)

(* body of SecureESIFP *)
context SecureESIFP
begin

(* defines whether information flow property IFP 
  is satisfied for event system ES *)
definition ES_sat_IFP :: "bool"
where
"ES_sat_IFP \<equiv> IFPIsSatisfied IFP Tr\<^bsub>ES\<^esub>"

end


locale SecureSESIFP =
fixes SES :: "('s, 'e) SES_rec"
and IFP :: "'e IFP_type"

assumes validSES: "SES_valid SES"
and validIFPSES: "IFP_valid E\<^bsub>SES\<^esub> IFP"

(* sublocale relations for SecureSESIFP *)

(* make theorems from SecureESIFP w.r.t. induceES visible in SecureSESIFP *)
sublocale SecureSESIFP \<subseteq> SecureESIFP "induceES SES" "IFP"
by (unfold_locales, rule induceES_yields_ES, rule validSES,
  simp add: induceES_def, rule validIFPSES)

(* body of SecureSESIFP *)
context SecureSESIFP
begin

abbreviation SES_sat_IFP
where 
"SES_sat_IFP \<equiv> ES_sat_IFP"

end


end
