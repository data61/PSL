subsection \<open>Relation between the Hoare logics in big-O style\<close>
theory DiscussionO
imports SepLogK_Hoare QuantK_Hoare Nielson_Hoare 
begin


(* here we compare quantitative Hoare logic with constant with Nielson's Hoare logic *)

subsubsection \<open>Relation Nielson to quantHoare\<close>
  
  
definition emN :: "qassn \<Rightarrow> Nielson_Hoare.assn2"  where "emN P = (\<lambda>l s. P s < \<infinity>)"  
 
(* quanthoare can be simulated by Nielson  *)  
lemma assumes s: "\<Turnstile>\<^sub>1 { emN P'} c {  %s. (THE e. enat e = P' s - Q' (THE t. (\<exists>n. (c, s) \<Rightarrow> n \<Down> t ) )) \<Down> emN Q' }" (is "\<Turnstile>\<^sub>1 { ?P } c { ?e \<Down> ?Q }")
  shows quantNielson: "\<Turnstile>\<^sub>2\<^sub>' { P' } c { Q' }"
proof -
  from s obtain k where k: "k>0" and qd: "\<And>l s. emN P' l s \<Longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> p \<le> k * ?e s \<and> emN Q' l t)"
    unfolding hoare1_valid_def by blast 
    
  show ?thesis unfolding QuantK_Hoare.hoare2o_valid_def
    apply(rule exI[where x=k])
    apply safe apply fact
  proof -
    fix s
    assume P': "P' s < \<infinity>"
    then have "(emN P') (\<lambda>_. 0) s" unfolding  emN_def by auto
    with qd obtain p t where i: "(c, s) \<Rightarrow> p \<Down> t" and p: "p \<le> k * ?e s" and e: "emN Q' (\<lambda>_. 0) t"
      by blast
    have t: "\<down>\<^sub>s (c, s) = t" using bigstepT_the_state[OF i] by auto   
      
    from P' obtain pre where pre: "P' s = enat pre" by fastforce
    from e have "Q' t < \<infinity>" unfolding emN_def by auto
    then obtain post where post: "Q' t = enat post" by fastforce
      
    have "p > 0" using i bigstep_progress by auto     
      
    thm enat.inject idiff_enat_enat the_equality
    have k: "(THE e. enat e = P' s - Q' (THE t. \<exists>n. (c, s) \<Rightarrow> n \<Down> t)) = pre - post" 
      unfolding t pre post apply(rule the_equality)   
       using idiff_enat_enat by auto 
    with p have ieq: "p \<le> k * (pre - post)" by auto
    then have "p + k * post \<le> k * pre" using \<open>p>0\<close>
      using diff_mult_distrib2 by auto
       then 
    have ii: "enat p + k * Q' t \<le> k * P' s" unfolding post pre by simp                           
    from i ii show "(\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + k * Q' t \<le> k * P' s)" by auto
  qed 
qed
 
  
  
(* Nielson can be simulated by quanthoare *)  
lemma assumes s: "\<Turnstile>\<^sub>2\<^sub>' { %s . emb (\<forall>l. P l s) + enat (e s) } c { %s. emb (\<forall>l. Q l s) }" (is "\<Turnstile>\<^sub>2\<^sub>' { ?P } c { ?Q }")
    and sP: "\<And>l t. P l t \<Longrightarrow> \<forall>l. P l t" (* "support P = {}" *)
    and sQ: "\<And>l t. Q l t \<Longrightarrow> \<forall>l. Q l t" (* "support Q = {}" *)
  shows  NielsonQuant: "\<Turnstile>\<^sub>1 { P } c { e \<Down> Q }" 
proof -
  from s obtain k where k: "k>0" and qd: "\<And>s. ?P s < \<infinity> \<longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k * ?Q t \<le> enat k * ?P s)"
    unfolding QuantK_Hoare.hoare2o_valid_def by blast 
    
  show ?thesis unfolding hoare1_valid_def
    apply(rule exI[where x=k])
    apply safe apply fact
  proof -
    fix l s
    assume P': "P l s"
    then have aP: "\<forall>l. P l s" using sP  by auto
    then have P: "?P s < \<infinity>" by auto
    with qd obtain p t where i: "(c, s) \<Rightarrow> p \<Down> t" and p: "enat p + enat k * ?Q t \<le> enat k * ?P s"
      by blast
    have t: "\<down>\<^sub>s (c, s) = t" using bigstepT_the_state[OF i] by auto   
       
    from P have Q: "Q l t" using p k
      apply auto
      by (metis (full_types) emb.simps(1) enat_ord_simps(2) imult_is_infinity infinity_ileE not_less_zero plus_enat_simps(3))      
    with sQ have "\<forall>l. Q l t" by auto
    then have "?Q t = 0" by auto
    with p have "enat p \<le> enat k * ?P s" by auto
    with aP have p': "p \<le> k * e s" by auto
        
    from i Q p' show "\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> p \<le> k * e s \<and> Q l t" by blast     
  qed
qed



 
subsubsection \<open>Relation SepLogic to quantHoare\<close> 

definition em :: "qassn \<Rightarrow> (pstate_t \<Rightarrow> bool)" where
  "em P = (%(ps,n). (\<forall>ex. P (Partial_Evaluation.emb ps ex) \<le> enat n) )"  (* with equality next lemma also works *)

lemma assumes s: "\<Turnstile>\<^sub>3\<^sub>' { em P} c { em Q }"
shows  "\<Turnstile>\<^sub>2\<^sub>' { P } c { Q }"
proof -
  from s obtain k where k: "0<k" and s': "\<And>ps n. em P (ps, n) \<Longrightarrow> (\<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps'+ ps'' \<and> ps' ## ps'' \<and> k * n = k * e + e' + m \<and> em Q (ps', e))" unfolding hoare3o_valid_def  by auto
  {
    fix s
    assume P: "P s < \<infinity>" 
    then obtain n where n: "P s = enat n"
      by fastforce
    with P have "em P (part s, n)" unfolding em_def by auto 
    with s' obtain ps' ps'' m e e' where c: "(c, part s) \<Rightarrow>\<^sub>A m \<Down> ps' + ps''" and orth: "ps' ## ps''"
              and m: "k * n = k * e + e' + m" and Q: "em Q (ps', e)" by blast
        
    from Q have q: "Q (Partial_Evaluation.emb ps' (Partial_Evaluation.emb ps'' (\<lambda>_. 0))) \<le> enat (e)" unfolding em_def by auto
        
    have z: "(Partial_Evaluation.emb ps' (Partial_Evaluation.emb ps'' (\<lambda>_. 0))) = (Partial_Evaluation.emb (ps'+ps'') (\<lambda>_. 0))"
      unfolding Partial_Evaluation.emb_def  apply (auto simp: plus_fun_def)
      apply (rule ext) subgoal for v apply (cases "ps' v") apply auto using orth    by (auto simp: sep_disj_fun_def domain_conv) done

    from q z have q:  "enat k * Q (Partial_Evaluation.emb (ps'+ps'') (\<lambda>_. 0)) \<le> enat k * enat e" using k
      by (metis i0_lb mult_left_mono) 

    have i: "(c, s) \<Rightarrow> m \<Down> (Partial_Evaluation.emb (ps'+ps'') (\<lambda>_. 0))" using  part_to_full'[OF c] by simp   
                
        
    have ii: "enat m + enat k * Q (Partial_Evaluation.emb (ps'+ps'') (\<lambda>_. 0)) \<le> enat k * P s" unfolding  n using q m
      using enat_ile by fastforce
      
    from i ii have "(\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k * Q t \<le> enat k * P s)" by auto
  } note B=this
  show ?thesis unfolding QuantK_Hoare.hoare2o_valid_def
    apply(rule exI[where x=k], safe) apply fact
    apply (fact B) done
qed 

definition embe :: "(pstate_t \<Rightarrow> bool) \<Rightarrow> qassn" where
    "embe P = (%s. Inf {enat n|n. P (part s, n)} )"
 
lemma assumes s: "\<Turnstile>\<^sub>2\<^sub>' { embe P } c { embe Q }" and full: "\<And>ps n. P (ps,n) \<Longrightarrow> dom ps = UNIV"            
  shows  "\<Turnstile>\<^sub>3\<^sub>' {  P} c { Q }"
proof -
  from s obtain k where k: "k>0" and s: "\<And>s. embe P s < \<infinity> \<longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k * embe Q t \<le> enat k * embe P s)"
    unfolding QuantK_Hoare.hoare2o_valid_def by auto

  { fix ps n
    let ?s =" (Partial_Evaluation.emb ps (\<lambda>_. 0))"
    assume P: "P (ps, n)"
    with full have "dom ps = UNIV" by auto
    then have ps: "part ?s = ps" by simp
    from P have l': "({enat n |n. P (ps, n)} = {}) =  False " by auto
    have t: "embe P ?s < \<infinity>" unfolding embe_def Inf_enat_def ps l'
      apply(rule ccontr) using l' apply auto
      by (metis (mono_tags, lifting) Least_le infinity_ileE)  
    with s obtain t p where c: "(c, ?s) \<Rightarrow> p \<Down> t" and ineq: "enat p + enat k * embe Q t \<le> enat k * embe P ?s" by blast
    from t obtain z where z: "embe P ?s = enat z"
      using less_infinityE by blast 
    with ineq obtain y where y: "embe Q t = enat y"
      using k by fastforce   
    then have l: "embe Q t < \<infinity>" by auto
    then have zz: "({enat n|n. Q (part t, n)} = {}) = False" unfolding embe_def Inf_enat_def apply safe by simp  
    from y have "Q (part t, y)"  unfolding embe_def zz Inf_enat_def apply auto
       using zz apply auto   by (smt Collect_empty_eq LeastI enat.inject)
    
    from full_to_part[OF c] ps have c': "(c, ps) \<Rightarrow>\<^sub>A p \<Down> part t" by auto

    have "\<And>P n. P (n::nat) \<Longrightarrow> (LEAST n. P n) \<le> n" apply(rule Least_le) by auto

    from z P have zn: "z \<le> n" unfolding embe_def ps unfolding embe_def Inf_enat_def l'
      apply auto
      by (metis (mono_tags, lifting) Least_le enat_ord_simps(1))        

    from ineq z y have "enat p + enat k * y \<le> enat k * z" by auto
    then have "p + k * y \<le> k * z" by auto
    also have "\<dots> \<le> k * n"   using zn k by simp
    finally obtain e' where "k * n = k * y + e' + p" using k  by (metis add.assoc add.commute le_iff_add)    

    have "\<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * n = k * e + e' + m \<and> Q (ps', e)"
      apply(rule exI[where x="part t"])
      apply(rule exI[where x="0"])
      apply(rule exI[where x="p"])
      apply(rule exI[where x="y"])
      apply(rule exI[where x="e'"]) apply auto by fact+ 
  }

  show ?thesis unfolding hoare3o_valid_def apply(rule exI[where x=k], safe)
    apply fact by fact
qed

subsection \<open>A General Validity Predicate with Time\<close>

  
definition valid  where
  "valid P c Q n = (\<forall>s. P s \<longrightarrow> (\<exists>s' m. (c, s) \<Rightarrow> m \<Down> s' \<and> m \<le> n \<and> Q s'))"  

definition validk  where
  "validk P c Q n = (\<exists>k>0. (\<forall>s. P s \<longrightarrow> (\<exists>s' m. (c, s) \<Rightarrow> m \<Down> s' \<and> m \<le> k * n \<and> Q s')))"


lemma "validk P c Q n = (\<exists>k>0. valid P c Q (k*n))"
  unfolding valid_def validk_def by simp

subsubsection \<open>Relation between valid predicate and Quantitative Hoare Logic\<close>
  
lemma "\<Turnstile>\<^sub>2\<^sub>' {%s.  emb (P s)  + enat n} c { \<lambda>s.  emb (Q s)  } \<Longrightarrow> \<exists>k>0. valid P c Q (k*n)"
proof -
  assume valid: "\<Turnstile>\<^sub>2\<^sub>' {\<lambda>s. \<up> (P s) + enat n} c {\<lambda>s. \<up> (Q s)}" 
  then obtain k where val: "\<And>s. \<up> (P s) + enat n < \<infinity> \<Longrightarrow> (\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + enat k * \<up> (Q t) \<le> enat k * (\<up> (P s) + enat n))"
    and k: "k>0" unfolding QuantK_Hoare.hoare2o_valid_def by blast
  { 
    fix s
    assume Ps: "P s"
    then have " \<up> (P s) + enat n < \<infinity>" by auto
    with val obtain  t m where
        c: "(c, s) \<Rightarrow> m \<Down> t" and "enat m + k * \<up> (Q t) \<le> k * (\<up> (P s) + enat n)" by blast
    
    then have "m \<le> k * n \<and> Q t" using k
      using Ps add.commute add.right_neutral emb.simps(1) emb.simps(2) enat_ord_simps(1) infinity_ileE plus_enat_simps(3)
      by (metis (full_types) mult_zero_right not_gr_zero times_enat_simps(1) times_enat_simps(4))
        
    with     c      
    have "(\<exists>s' m. (c, s) \<Rightarrow> m \<Down> s' \<and> m \<le>  k * n \<and> Q s')" by blast
  } note bla=this 
  show "\<exists>k>0. valid P c Q (k*n)" unfolding valid_def apply(rule exI[where x=k]) using bla k by auto
qed  
 
lemma valid_quantHoare: "\<exists>k>0. valid P c Q (k*n) \<Longrightarrow> \<Turnstile>\<^sub>2\<^sub>' {%s. emb (P s)  + enat n} c { \<lambda>s. emb (Q s)  }"
proof -
  assume  "\<exists>k>0. valid P c Q (k*n)" 
  then obtain k where valid: "valid P c Q (k*n)" and k: "k>0" by blast
  { 
    fix s
    assume "(%s. emb (P s)  + enat n) s < \<infinity>"
    then have Ps: "P s" apply auto
      by (metis emb.elims enat.distinct(2) enat.simps(5) enat_defs(4)) 
    with valid[unfolded valid_def] obtain t m where
        c: "(c, s) \<Rightarrow> m \<Down> t" and "m \<le> k * n" "Q t" by blast    
    then have "enat m +  k * \<up> (Q t) \<le>  k * (\<up> (P s) + enat n)" using Ps by simp
    with     c      
    have "(\<exists>s' m. (c, s) \<Rightarrow> m \<Down> s' \<and> enat m + enat k * \<up> (Q s') \<le> enat k * (\<up> (P s) + enat n))" by blast
  } note funk=this
  show "\<Turnstile>\<^sub>2\<^sub>' {%s.  emb (P s)  + enat n} c { \<lambda>s. emb (Q s)  }" unfolding QuantK_Hoare.hoare2o_valid_def
    apply(rule exI[where x=k]) using funk k by auto
qed  



subsubsection \<open>Relation between valid predicate and Hoare Logic based on Separation Logic\<close>
    
  
  

definition "embP2 P = (%(ps,n). \<forall>s.  P (Partial_Evaluation.emb ps s) \<and> n = 0)"
definition "embP3 P = (%(ps,n). dom ps = UNIV \<and> (\<forall>s.  P (Partial_Evaluation.emb ps s)) \<and> n = 0)"
  
    
lemma emp: "a + Map.empty = a"
  by (simp add: plus_fun_conv) 
  
lemma oneway: "\<Turnstile>\<^sub>3\<^sub>' {embP3 P ** $n} c {embP2 Q} \<Longrightarrow> validk P c Q n"
proof -
  assume partial_true: "\<Turnstile>\<^sub>3\<^sub>' {embP3 P ** $n} c {embP2 Q}" 
  from partial_true[unfolded hoare3o_valid_def] obtain k where k: "k>0" and
   q : "\<forall>ps na. (embP3 P \<and>* $ n) (ps, na) \<longrightarrow>
                (\<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * na = k * e + e' + m \<and> embP2 Q (ps', e)) " by blast
  { fix s
    assume "P s"
    then have g: " (embP3 P \<and>* $ n) (part s, n)"
      unfolding embP3_def dollar_def sep_conj_def by auto
    from q  g
    obtain ps' ps'' m e e' where pbig: "(c, part s) \<Rightarrow>\<^sub>A m \<Down> ps' + ps''" and orth: "ps' ## ps''"
        and ii: "k * n = k * e + e' + m" and erg: "embP2 Q (ps', e)" by blast
    
    have ii': "m \<le> k * n" using ii by auto    
        
    from part_to_full'[OF pbig] have i: "(c, s ) \<Rightarrow> m \<Down> Partial_Evaluation.emb (ps' + ps'') s" by simp
    
    from erg have z2: "\<And>s. Q (Partial_Evaluation.emb ps' s)" unfolding embP2_def by auto   
    have "Partial_Evaluation.emb (ps' + ps'') s = Partial_Evaluation.emb (ps'' + ps') s"
      using orth  by (simp add: sep_add_commute)
    also have "Partial_Evaluation.emb (ps'' + ps') s = Partial_Evaluation.emb (ps') (Partial_Evaluation.emb (ps'') s)"
      apply rule 
      unfolding emb_def plus_fun_conv map_add_def
      by (metis option.case_eq_if option.simps(5)) 
    finally have z: "Partial_Evaluation.emb (ps' + ps'') s = Partial_Evaluation.emb (ps') (Partial_Evaluation.emb (ps'') s)" .
    have iii: "Q (Partial_Evaluation.emb (ps' + ps'') s)" unfolding z apply (fact) . 
        
    from i ii' iii
      have "\<exists>s' m. (c, s) \<Rightarrow> m \<Down> s' \<and> m \<le> k * n \<and> Q s'" by auto
    }
    with k show "validk P c Q n" unfolding validk_def by blast
qed
   
  
lemma theother: "validk P c Q n \<Longrightarrow> \<Turnstile>\<^sub>3\<^sub>' {embP3 P ** $n} c {embP2 Q }"
proof -
  assume valid: "validk P c Q n" 
  then obtain k where k : "k>0" and v: "(\<forall>s. P s \<longrightarrow> (\<exists>s' m. (c, s) \<Rightarrow> m \<Down> s' \<and> m \<le> k * n \<and> Q s'))"
   unfolding validk_def by blast
  
  { fix ps na
    assume an: "(embP3 P \<and>* $ n) (ps, na)" 
    have dom: "dom ps = UNIV" and Pps: "\<And>s. P (Partial_Evaluation.emb ps s)" and nan: "na = n" using an unfolding sep_conj_def
        by (auto simp: embP3_def dollar_def)
        
    from v Pps
      obtain s' m where big: "(c, (Partial_Evaluation.emb ps (%_. 0))) \<Rightarrow> m \<Down> s'" and ii: "m \<le> k * n" and erg: "Q s'" by blast
                    
          
    have "part (Partial_Evaluation.emb ps (\<lambda>_. 0)) = ps " using dom by simp
    with full_to_part[OF big] have i: "(c, ps) \<Rightarrow>\<^sub>A m \<Down> part s'" by auto 
    
       
    have iii: "embP2 Q (part s', 0)" 
      unfolding embP2_def apply auto by fact 
         
    have "k * na = k * n - m + m" using ii k nan by simp  
        
    have "(\<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * na = k * e + e' + m \<and> embP2 Q (ps', e))"
      apply(rule exI[where x="part s'"])
      apply(rule exI[where x="0"])
      apply(rule exI[where x="m"])
      apply(rule exI[where x="0"])
      apply(rule exI[where x="k * n - m"]) apply auto
      by fact+         
    }
    with k show "\<Turnstile>\<^sub>3\<^sub>' {embP3 P ** $n} c {embP2 Q }" unfolding hoare3o_valid_def by blast
qed
  
  
lemma "validk P c Q n \<longleftrightarrow> \<Turnstile>\<^sub>3\<^sub>' {embP3 P ** $n} c {embP2 Q }"
using oneway and theother by metis



end