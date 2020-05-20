theory AuxiliaryLemmas
imports UnwindingConditions
begin


context Unwinding
begin

(* Main lemma on output step consistency 
 (Lemma 5.4.2 in Heiko Mantel's dissertation)*)
lemma osc_property: 
"\<And>s1 s1'. \<lbrakk> osc ur; s1 \<in> S\<^bsub>SES\<^esub>; s1' \<in> S\<^bsub>SES\<^esub>; \<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []; 
  reachable SES s1; reachable SES s1'; enabled SES s1' \<alpha>; (s1', s1) \<in> ur \<rbrakk>
  \<Longrightarrow> (\<exists>\<alpha>'. \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> enabled SES s1 \<alpha>')" 
proof (induct \<alpha>)
  case Nil
  have "[] \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and>
    [] \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [] \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> enabled SES s1 []" 
    by (simp add: enabled_def projection_def)
  thus ?case by (rule exI)
next
  case (Cons e1 \<alpha>1)
  assume osc_true: "osc ur"
  assume s1_in_S: "s1 \<in> S\<^bsub>SES\<^esub>"
  assume s1'_in_S: "s1' \<in> S\<^bsub>SES\<^esub>"
  assume e1\<alpha>1_C_empty: "(e1 # \<alpha>1) \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
  assume reachable_s1: "reachable SES s1"
  assume reachable_s1': "reachable SES s1'"
  assume enabled_s1'_e1\<alpha>1: "enabled SES s1' (e1 # \<alpha>1)"
  assume unwindingrel_s1'_s1: "(s1', s1) \<in> ur"

  have e1\<alpha>1_no_c: "\<forall>a \<in> (set (e1 # \<alpha>1)). a \<in> (E\<^bsub>SES\<^esub> - C\<^bsub>\<V>\<^esub>)"
  proof -
    from reachable_s1' obtain \<beta> 
      where "s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s1'"
      by(simp add: reachable_def, auto)
    moreover
    from enabled_s1'_e1\<alpha>1 obtain s1337
      where "s1' (e1 # \<alpha>1)\<Longrightarrow>\<^bsub>SES\<^esub> s1337"
      by(simp add: enabled_def, auto)
    ultimately have "s0\<^bsub>SES\<^esub> (\<beta> @ (e1 # \<alpha>1))\<Longrightarrow>\<^bsub>SES\<^esub> s1337"
      by(rule path_trans)
    hence "\<beta> @ (e1 # \<alpha>1) \<in> Tr\<^bsub>(induceES SES)\<^esub>"
      by (simp add: induceES_def possible_traces_def enabled_def)
    with validSES induceES_yields_ES[of "SES"] have "\<forall>a \<in> (set (\<beta> @ (e1 # \<alpha>1))). a \<in> E\<^bsub>SES\<^esub>"
      by (simp add: induceES_def ES_valid_def traces_contain_events_def)
    hence "\<forall> a \<in> (set (e1 # \<alpha>1)). a \<in> E\<^bsub>SES\<^esub>"
      by auto
    with e1\<alpha>1_C_empty show ?thesis
      by (simp only: projection_def filter_empty_conv, auto)
  qed

  from enabled_s1'_e1\<alpha>1 obtain s2' where 
    s1'_e1_s2': "s1' e1\<longrightarrow>\<^bsub>SES\<^esub> s2'" 
    by (simp add: enabled_def, split if_split_asm, auto)
  with validSES have s2'_in_S: "s2' \<in> S\<^bsub>SES\<^esub>" 
    by (simp add: SES_valid_def correct_transition_relation_def)
  have reachable_s2': "reachable SES s2'"
  proof -
    from reachable_s1' obtain t where 
      path_to_s1': "s0\<^bsub>SES\<^esub> t\<Longrightarrow>\<^bsub>SES\<^esub> s1'" 
      by (simp add: reachable_def, auto)
    from s1'_e1_s2' have "s1' [e1]\<Longrightarrow>\<^bsub>SES\<^esub> s2'" 
      by simp
    with path_to_s1' have "s0\<^bsub>SES\<^esub> (t @ [e1])\<Longrightarrow>\<^bsub>SES\<^esub> s2'" 
      by (simp add: path_trans)
    thus ?thesis by (simp add: reachable_def, rule exI)
  qed
  from s1'_e1_s2' enabled_s1'_e1\<alpha>1 obtain sn' where 
    "s2' \<alpha>1\<Longrightarrow>\<^bsub>SES\<^esub> sn'" 
    by (simp add: enabled_def, auto)
  hence enabled_s2'_\<alpha>1: "enabled SES s2' \<alpha>1" 
    by (simp add: enabled_def)
  from e1\<alpha>1_no_c have e1_no_c: "e1 \<in> (E\<^bsub>SES\<^esub> - C\<^bsub>\<V>\<^esub>)" 
    by simp
  from e1\<alpha>1_no_c have \<alpha>1_no_c: "\<forall>a\<in>(set \<alpha>1). (a \<in> (E\<^bsub>SES\<^esub> - C\<^bsub>\<V>\<^esub>))" 
    by simp
  hence \<alpha>1_proj_C_empty: "\<alpha>1 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    by (simp add: projection_def)
  from osc_true have 
    "\<lbrakk> s1 \<in> S\<^bsub>SES\<^esub>; s1' \<in> S\<^bsub>SES\<^esub>; s2' \<in> S\<^bsub>SES\<^esub>; 
      e1 \<in> (E\<^bsub>SES\<^esub> - C\<^bsub>\<V>\<^esub>); reachable SES s1; reachable SES s1'; 
      s1' e1\<longrightarrow>\<^bsub>SES\<^esub> s2'; (s1', s1) \<in> ur \<rbrakk> 
     \<Longrightarrow> (\<exists>s2 \<in> S\<^bsub>SES\<^esub>. \<exists>\<delta>. \<delta> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []
        \<and> (\<delta> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = ([e1] \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<and> (s1 \<delta>\<Longrightarrow>\<^bsub>SES\<^esub> s2 \<and> 
       ((s2', s2) \<in> ur)))"
    by (simp add: osc_def)
  with s1_in_S s1'_in_S e1_no_c reachable_s1 reachable_s1' 
    s2'_in_S s1'_e1_s2' unwindingrel_s1'_s1 
  obtain s2 \<delta> where 
    osc_conclusion: 
      "s2 \<in> S\<^bsub>SES\<^esub> \<and> \<delta> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and>
      (\<delta> \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = ([e1] \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<and> s1 \<delta>\<Longrightarrow>\<^bsub>SES\<^esub> s2 \<and> 
      ((s2', s2) \<in> ur)"
    by auto
  hence \<delta>_proj_C_empty: "\<delta> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    by (simp add: projection_def)
  from osc_conclusion have s2_in_S: "s2 \<in> S\<^bsub>SES\<^esub>" 
    by auto
  from osc_conclusion have unwindingrel_s2'_s2: "(s2', s2) \<in> ur" 
    by auto
  have reachable_s2: "reachable SES s2"
  proof -
    from reachable_s1 obtain t where 
      path_to_s1: "s0\<^bsub>SES\<^esub> t\<Longrightarrow>\<^bsub>SES\<^esub> s1" 
      by (simp add: reachable_def, auto)
    from osc_conclusion have "s1 \<delta>\<Longrightarrow>\<^bsub>SES\<^esub> s2" 
      by auto
    with path_to_s1 have "s0\<^bsub>SES\<^esub> (t @ \<delta>)\<Longrightarrow>\<^bsub>SES\<^esub> s2" 
      by (simp add: path_trans)
    thus ?thesis by (simp add: reachable_def, rule exI)
  qed

  from Cons osc_true s2_in_S s2'_in_S \<alpha>1_proj_C_empty
    reachable_s2 reachable_s2' enabled_s2'_\<alpha>1 unwindingrel_s2'_s2
  obtain \<alpha>'' where \<alpha>''_props:
    "\<alpha>'' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and> \<alpha>'' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha>1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> enabled SES s2 \<alpha>''"
    by auto
  with osc_conclusion have  \<delta>\<alpha>''_props:
    "(\<delta> @ \<alpha>'') \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and> 
    (\<delta> @ \<alpha>'') \<upharpoonleft> V\<^bsub>\<V>\<^esub> = (e1#\<alpha>1) \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> enabled SES s1 (\<delta> @ \<alpha>'')"
    by (simp add: projection_def enabled_def, auto, simp add: path_trans)
  hence "(\<delta> @ \<alpha>'') \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    by (simp add: projection_def)
  thus ?case using \<delta>\<alpha>''_props by auto
qed

(* Paths will not bring us out of the domain of states.  *)
lemma path_state_closure: "\<lbrakk> s \<tau>\<Longrightarrow>\<^bsub>SES\<^esub> s'; s \<in> S\<^bsub>SES\<^esub> \<rbrakk> \<Longrightarrow> s' \<in> S\<^bsub>SES\<^esub>"
  (is "\<lbrakk> ?P s \<tau> s'; ?S s SES \<rbrakk> \<Longrightarrow> ?S s' SES ")
proof (induct \<tau> arbitrary: s s')
  case Nil with validSES show ?case 
    by (auto simp add: SES_valid_def correct_transition_relation_def)
next
  case (Cons e \<tau>) thus ?case
  proof -
    assume path_e\<tau>: "?P s (e # \<tau>) s'" 
    assume induct_hypo: "\<And> s s'. \<lbrakk> ?P s \<tau> s'; ?S s SES \<rbrakk> \<Longrightarrow> ?S s' SES"
    
    from path_e\<tau> obtain s'' where s_e_s'': "s e\<longrightarrow>\<^bsub>SES\<^esub> s''" 
      by(simp add: path_def, split if_split_asm, auto)
    with validSES have s''_in_S: "?S s'' SES" 
      by (simp add: SES_valid_def correct_transition_relation_def)
    
    from s_e_s'' path_e\<tau> have path_\<tau>: "?P s'' \<tau> s'" by auto
    
    from path_\<tau> s''_in_S show ?case by (rule induct_hypo)
  qed
qed


(* Theorem 5.4.7 split into two parts *)

(* first part *)
theorem En_to_Adm:
"\<lbrakk> reachable SES s; En \<rho> s e\<rbrakk> 
\<Longrightarrow> \<exists>\<beta>. ( s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s \<and> Adm \<V> \<rho> Tr\<^bsub>(induceES SES)\<^esub> \<beta> e )" 
proof -
  assume "En \<rho> s e"
  then obtain \<beta> \<gamma> s' s'' 
    where "s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s"
    and   "\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)" 
    and   s0_\<gamma>_s': "s0\<^bsub>SES\<^esub> \<gamma>\<Longrightarrow>\<^bsub>SES\<^esub> s'" 
    and   s'_e_s'': "s' e\<longrightarrow>\<^bsub>SES\<^esub> s''"
    by (simp add: En_def, auto)
  moreover 
    from s0_\<gamma>_s' s'_e_s'' have "s0\<^bsub>SES\<^esub> (\<gamma> @ [e])\<Longrightarrow>\<^bsub>SES\<^esub> s''"
      by (rule path_trans_single)
    hence "(\<gamma> @ [e]) \<in> Tr\<^bsub>(induceES SES)\<^esub>"
      by(simp add: induceES_def possible_traces_def enabled_def)
  ultimately show ?thesis
    by (simp add: Adm_def, auto)
qed

(* second part *)
theorem Adm_to_En:
"\<lbrakk> \<beta> \<in> Tr\<^bsub>(induceES SES)\<^esub>; Adm \<V> \<rho> Tr\<^bsub>(induceES SES)\<^esub> \<beta> e \<rbrakk>
\<Longrightarrow> \<exists>s \<in> S\<^bsub>SES\<^esub>. (s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s \<and> En \<rho> s e)"
proof -
  from validSES have s0_in_S: "s0\<^bsub>SES\<^esub> \<in> S\<^bsub>SES\<^esub>"
       by (simp add: SES_valid_def s0_is_state_def) 
  
  assume "\<beta> \<in> Tr\<^bsub>(induceES SES)\<^esub>"
  then obtain s
    where s0_\<beta>_s: "s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s"
    by (simp add: induceES_def possible_traces_def enabled_def, auto)
  from this have s_in_S: "s \<in> S\<^bsub>SES\<^esub>" using s0_in_S
    by (rule path_state_closure)

  assume  "Adm \<V> \<rho> Tr\<^bsub>(induceES SES)\<^esub> \<beta> e"
  then obtain \<gamma>
    where \<rho>\<gamma>_is_\<rho>\<beta>: "\<gamma> \<upharpoonleft> (\<rho> \<V>) = \<beta> \<upharpoonleft> (\<rho> \<V>)"
    and   "\<exists>s''. s0\<^bsub>SES\<^esub> (\<gamma> @ [e])\<Longrightarrow>\<^bsub>SES\<^esub> s''"
    by(simp add: Adm_def induceES_def possible_traces_def enabled_def, auto)
  then obtain s''
    where  s0_\<gamma>e_s'': "s0\<^bsub>SES\<^esub> (\<gamma> @ [e])\<Longrightarrow>\<^bsub>SES\<^esub> s''"
    by auto
  from this have s''_in_S: "s'' \<in> S\<^bsub>SES\<^esub>" using s0_in_S
    by (rule path_state_closure)
  
  from path_split_single[OF s0_\<gamma>e_s''] obtain s' 
    where s0_\<gamma>_s': "s0\<^bsub>SES\<^esub> \<gamma>\<Longrightarrow>\<^bsub>SES\<^esub> s'"
    and s'_e_s'': "s' e\<longrightarrow>\<^bsub>SES\<^esub> s''"
    by auto

  from path_state_closure[OF s0_\<gamma>_s' s0_in_S] have s'_in_S: "s' \<in> S\<^bsub>SES\<^esub>". 
  
  from s'_in_S s''_in_S s0_\<beta>_s \<rho>\<gamma>_is_\<rho>\<beta> s0_\<gamma>_s' s'_e_s'' s_in_S show ?thesis 
    by (simp add: En_def, auto)
qed


(* It is a common pattern in the unwinding theorem proofs to obtain 
 a state from a given trace in a state event system and deduce some of its
 properties. This can be accomplished with the following lemma: 
*)
lemma state_from_induceES_trace: 
  "\<lbrakk>  (\<beta> @ \<alpha>) \<in> Tr\<^bsub>(induceES SES)\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>s \<in> S\<^bsub>SES\<^esub>. s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s \<and> enabled SES s \<alpha> \<and> reachable SES s"
  proof -
    
    assume \<beta>\<alpha>_in_Tr: "(\<beta> @ \<alpha>) \<in> Tr\<^bsub>(induceES SES)\<^esub>"
    then obtain s' where  s0_\<beta>\<alpha>_s':"s0\<^bsub>SES\<^esub> (\<beta> @ \<alpha>)\<Longrightarrow>\<^bsub>SES\<^esub> s'" 
      by (simp add: induceES_def possible_traces_def enabled_def, auto)
    
    from path_split[OF s0_\<beta>\<alpha>_s'] obtain s 
      where s0_\<beta>_s: "s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s" 
      and "s \<alpha>\<Longrightarrow>\<^bsub>SES\<^esub> s'"
      by auto    
    hence enabled_s_\<alpha>: "enabled SES s \<alpha>"
      by (simp add: enabled_def)
    
    from s0_\<beta>_s have reachable_s: "reachable SES s"
      by(simp add: reachable_def, auto)
    
    from validSES have "s0\<^bsub>SES\<^esub> \<in> S\<^bsub>SES\<^esub>"
      by (simp add: SES_valid_def s0_is_state_def)
    with s0_\<beta>_s have s_in_S: "s \<in> S\<^bsub>SES\<^esub>"
      by (rule path_state_closure)
    with s0_\<beta>_s enabled_s_\<alpha> reachable_s show ?thesis
      by auto
  qed

(* Another common pattern in unwinding results: *)
lemma path_split2:"s0\<^bsub>SES\<^esub> (\<beta> @ \<alpha>)\<Longrightarrow>\<^bsub>SES\<^esub> s 
  \<Longrightarrow> \<exists>s' \<in> S\<^bsub>SES\<^esub>. ( s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s' \<and> s' \<alpha>\<Longrightarrow>\<^bsub>SES\<^esub> s \<and> reachable SES s' )"
proof - 
  assume s0_\<beta>\<alpha>_s: "s0\<^bsub>SES\<^esub> (\<beta> @ \<alpha>)\<Longrightarrow>\<^bsub>SES\<^esub> s"

  from path_split[OF s0_\<beta>\<alpha>_s] obtain s' 
    where s0_\<beta>_s': "s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s'"
    and s'_\<alpha>_s: "s' \<alpha>\<Longrightarrow>\<^bsub>SES\<^esub> s"
    by auto
  hence "reachable SES s'"
    by(simp add: reachable_def, auto)  
  moreover
  have "s' \<in> S\<^bsub>SES\<^esub>"
    proof -
      from s0_\<beta>_s' validSES path_state_closure show ?thesis
        by (auto simp add: SES_valid_def s0_is_state_def)
    qed

  ultimately show ?thesis using s'_\<alpha>_s s0_\<beta>_s'
    by(auto)
qed 


(* Variant for singleton lists *)
lemma path_split_single2:
  "s0\<^bsub>SES\<^esub> (\<beta> @ [x])\<Longrightarrow>\<^bsub>SES\<^esub> s
  \<Longrightarrow> \<exists>s' \<in> S\<^bsub>SES\<^esub>. ( s0\<^bsub>SES\<^esub> \<beta>\<Longrightarrow>\<^bsub>SES\<^esub> s' \<and> s' x\<longrightarrow>\<^bsub>SES\<^esub> s \<and> reachable SES s' )"
proof - 
  assume s0_\<beta>x_s: "s0\<^bsub>SES\<^esub> (\<beta> @ [x])\<Longrightarrow>\<^bsub>SES\<^esub> s"

  from path_split2[OF s0_\<beta>x_s] show ?thesis
    by (auto, split if_split_asm, auto)
qed 

      
lemma modified_view_valid: "isViewOn \<lparr>V = (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>), N = {}, C = C\<^bsub>\<V>\<^esub>\<rparr> E\<^bsub>SES\<^esub>"
  using validVU 
    unfolding isViewOn_def V_valid_def VC_disjoint_def VN_disjoint_def NC_disjoint_def by auto
    
end

end
