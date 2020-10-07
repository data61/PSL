theory Views
imports Main
begin

(* structural representation of views *)
record 'e V_rec =
  V :: "'e set"
  N :: "'e set"
  C :: "'e set"

(* syntax abbreviations for V_rec *)
abbreviation VrecV :: "'e V_rec \<Rightarrow> 'e set"
("V\<^bsub>_\<^esub>" [100] 1000)
where
"V\<^bsub>v\<^esub> \<equiv> (V v)"

abbreviation VrecN :: "'e V_rec \<Rightarrow> 'e set"
("N\<^bsub>_\<^esub>" [100] 1000)
where
"N\<^bsub>v\<^esub> \<equiv> (N v)"

abbreviation VrecC :: "'e V_rec \<Rightarrow> 'e set"
("C\<^bsub>_\<^esub>" [100] 1000)
where
"C\<^bsub>v\<^esub> \<equiv> (C v)"

(* side conditions for views *)
definition VN_disjoint :: "'e V_rec \<Rightarrow> bool"
where
"VN_disjoint v \<equiv> V\<^bsub>v\<^esub> \<inter> N\<^bsub>v\<^esub> = {}"

definition VC_disjoint :: "'e V_rec \<Rightarrow> bool"
where
"VC_disjoint v \<equiv> V\<^bsub>v\<^esub> \<inter> C\<^bsub>v\<^esub> = {}"

definition NC_disjoint :: "'e V_rec \<Rightarrow> bool"
where
"NC_disjoint v \<equiv> N\<^bsub>v\<^esub> \<inter> C\<^bsub>v\<^esub> = {}"

(* Views are instances of V_rec that satisfy V_valid. *)
definition V_valid :: "'e V_rec \<Rightarrow> bool"
where
"V_valid  v \<equiv> VN_disjoint v \<and> VC_disjoint v \<and> NC_disjoint v"

(* A view is a view on a set of events iff it covers exactly those events and is a valid view*)
definition isViewOn :: "'e V_rec \<Rightarrow> 'e set \<Rightarrow> bool" 
where
"isViewOn \<V> E \<equiv> V_valid \<V> \<and> V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub> = E"

end
