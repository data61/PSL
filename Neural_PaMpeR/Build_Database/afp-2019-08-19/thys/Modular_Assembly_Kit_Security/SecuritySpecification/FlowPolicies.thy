theory FlowPolicies
imports Views
begin

(* 
  Flow policies
*)
record 'domain FlowPolicy_rec = 
  D :: "'domain set"
  v_rel :: "('domain \<times> 'domain) set"
  n_rel :: "('domain \<times> 'domain) set"
  c_rel :: "('domain \<times> 'domain) set"
(*
  The three relations of a flow policy form a partition of DxD.
  Moreover, the relation v_rel is reflexive.
*)
definition FlowPolicy :: "'domain FlowPolicy_rec \<Rightarrow> bool"
where
"FlowPolicy fp \<equiv> 
   ((v_rel fp) \<union> (n_rel fp) \<union> (c_rel fp) = ((D fp) \<times> (D fp)))
 \<and> (v_rel fp) \<inter> (n_rel fp) = {}
 \<and> (v_rel fp) \<inter> (c_rel fp) = {}
 \<and> (n_rel fp) \<inter> (c_rel fp) = {} 
 \<and> (\<forall>d \<in> (D fp). (d, d) \<in> (v_rel fp))"

(* 
  Domain assignments and the view of a domain 
*)
type_synonym ('e, 'domain) dom_type = "'e \<rightharpoonup> 'domain"

(*
  A domain assignment should only assign domains to actual events.
*)
definition dom :: "('e, 'domain) dom_type \<Rightarrow> 'domain set \<Rightarrow> 'e set \<Rightarrow> bool"
where
"dom domas dset es \<equiv> 
(\<forall>e. \<forall>d. ((domas e = Some d) \<longrightarrow> (e \<in> es \<and> d \<in> dset)))"

(*
  The combination of a domain assignment and a flow policy
  yields a view for each domain.
*)
definition view_dom :: "'domain FlowPolicy_rec \<Rightarrow> 'domain \<Rightarrow> ('e, 'domain) dom_type \<Rightarrow> 'e V_rec"
where
  "view_dom fp d domas \<equiv> 
   \<lparr> V = {e. \<exists>d'. (domas e = Some d' \<and> (d', d) \<in> (v_rel fp))}, 
     N = {e. \<exists>d'. (domas e = Some d' \<and> (d', d) \<in> (n_rel fp))}, 
     C = {e. \<exists>d'. (domas e = Some d' \<and> (d', d) \<in> (c_rel fp))} \<rparr>"

end
