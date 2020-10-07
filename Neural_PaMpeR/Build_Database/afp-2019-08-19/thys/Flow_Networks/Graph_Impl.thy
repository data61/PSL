(* TODO: That's quite specific to the BFS alg. Move to Edka! *)
theory Graph_Impl
imports "Lib/Refine_Add_Fofu" Graph
begin

\<comment> \<open>Fixing capacities to integer values\<close>
type_synonym capacity_impl = int (* TODO: DUP in Network_Impl. Remove here!*)


locale Impl_Succ =
  fixes absG :: "'ga \<Rightarrow> capacity_impl graph" 
  fixes ifT :: "'ig itself"
  fixes succ :: "'ga \<Rightarrow> node \<Rightarrow> node list nres"
  fixes isG :: "'ga \<Rightarrow> 'gi \<Rightarrow> assn"
  fixes succ_impl :: "'gi \<Rightarrow> node \<Rightarrow> node list Heap"
  (*assumes [constraint_rules]: "precise isG"*)
  assumes si_rule[sepref_fr_rules]: "(uncurry succ_impl,(uncurry succ)) \<in> [\<lambda>(c,u). u\<in>Graph.V (absG c)]\<^sub>a isG\<^sup>k *\<^sub>a (pure nat_rel)\<^sup>k \<rightarrow> list_assn (pure nat_rel)"
begin
  lemma this_loc: "Impl_Succ absG succ isG succ_impl" by unfold_locales

  sepref_register "succ" :: "'ig \<Rightarrow> node \<Rightarrow> node list nres" (* TODO: Will not work if succ is not a constant! *) 
end


end
