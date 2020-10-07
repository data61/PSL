theory Gen_Hash
imports "../Intf/Intf_Hash"
begin

definition "prod_bhc bhc1 bhc2 \<equiv> \<lambda>n (a,b). (bhc1 n a * 33 + bhc2 n b) mod n"

lemma prod_bhc_ga[autoref_ga_rules]:
  "\<lbrakk> GEN_ALGO_tag (is_bounded_hashcode R eq1 bhc1); 
     GEN_ALGO_tag (is_bounded_hashcode S eq2 bhc2)\<rbrakk> 
  \<Longrightarrow> is_bounded_hashcode (R\<times>\<^sub>rS) (prod_eq eq1 eq2) (prod_bhc bhc1 bhc2)"
  unfolding is_bounded_hashcode_def prod_bhc_def prod_eq_def[abs_def]
  apply safe
  apply (auto dest: fun_relD simp: Domain_unfold; metis)+
  done

lemma prod_dhs_ga[autoref_ga_rules]:
  "\<lbrakk> GEN_ALGO_tag (is_valid_def_hm_size TYPE('a) n1);
     GEN_ALGO_tag (is_valid_def_hm_size TYPE('b) n2) \<rbrakk>
   \<Longrightarrow> is_valid_def_hm_size TYPE('a*'b) (n1+n2)"
   unfolding is_valid_def_hm_size_def by auto

end
