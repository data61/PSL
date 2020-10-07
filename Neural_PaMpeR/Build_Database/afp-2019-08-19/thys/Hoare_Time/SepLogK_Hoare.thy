section "Hoare Logic based on Separation Logic and Time Credits (big-O style)" 
theory SepLogK_Hoare
  imports Big_StepT  Partial_Evaluation  Big_StepT_Partial
begin


   
subsection \<open>Definition of Validity\<close>
          
definition hoare3o_valid :: "assn2 \<Rightarrow> com \<Rightarrow> assn2 \<Rightarrow> bool"
  ("\<Turnstile>\<^sub>3\<^sub>' {(1_)}/ (_)/ { (1_)}" 50) where
"\<Turnstile>\<^sub>3\<^sub>' { P } c { Q }  \<longleftrightarrow>
    (\<exists> k>0. (\<forall>ps n. P (ps,n)
 \<longrightarrow> (\<exists>ps' ps'' m e e'. ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'') 
     \<and> ps' ## ps'' \<and> k * n = k * e + e' + m
     \<and> Q (ps',e))))"
 
 


subsection "Hoare Rules"
     
inductive
  hoare3a :: "assn2 \<Rightarrow> com \<Rightarrow> assn2 \<Rightarrow> bool" ("\<turnstile>\<^sub>3\<^sub>a ({(1_)}/ (_)/ { (1_)})" 50)
where

Skip:  "\<turnstile>\<^sub>3\<^sub>a {$1} SKIP { $0}"  |

Assign4:  "\<turnstile>\<^sub>3\<^sub>a { (\<lambda>(ps,t). x\<in>dom ps \<and> vars a \<subseteq> dom ps \<and> Q (ps(x\<mapsto>(paval a ps)),t) ) ** $1} x::=a { Q }" |

If: "\<lbrakk> \<turnstile>\<^sub>3\<^sub>a { \<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b True s } c\<^sub>1 { Q };
       \<turnstile>\<^sub>3\<^sub>a {  \<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b False s } c\<^sub>2 { Q } \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>a { (\<lambda>(s,n). P (s,n) \<and> vars b \<subseteq> dom s) ** $1} IF b THEN c\<^sub>1 ELSE c\<^sub>2 { Q}"   |

Frame:  "\<lbrakk>    \<turnstile>\<^sub>3\<^sub>a { P } C { Q  } \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>a { P ** F } C { Q ** F } "  |

Seq:  "\<lbrakk> \<turnstile>\<^sub>3\<^sub>a { P } C\<^sub>1 { Q } ;  \<turnstile>\<^sub>3\<^sub>a { Q } C\<^sub>2 { R  } \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>a { P } C\<^sub>1 ;; C\<^sub>2 { R } "  |

While:  "\<lbrakk> \<turnstile>\<^sub>3\<^sub>a { (\<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b True s) } C { (\<lambda>(s,n). P (s,n) \<and>  vars b \<subseteq> dom s)  ** $1 }  \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>a { (\<lambda>(s,n). P (s,n) \<and>  vars b \<subseteq> dom s) ** $1 } WHILE b DO C {  \<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b False s } "  |
   
conseqS: "\<lbrakk> \<turnstile>\<^sub>3\<^sub>a {P}c{Q} ; \<And>s n. P' (s,n) \<Longrightarrow> P (s,n) ; \<And>s n. Q (s,n) \<Longrightarrow> Q' (s,n) \<rbrakk> \<Longrightarrow> 
           \<turnstile>\<^sub>3\<^sub>a {P'}c{ Q'}"   
  
inductive
  hoare3b :: "assn2 \<Rightarrow> com \<Rightarrow> assn2 \<Rightarrow> bool" ("\<turnstile>\<^sub>3\<^sub>b ({(1_)}/ (_)/ { (1_)})" 50)
where

import:  "\<turnstile>\<^sub>3\<^sub>a {P} c { Q} \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>b {P} c { Q}"  |


conseq: "\<lbrakk> \<turnstile>\<^sub>3\<^sub>b {P}c{Q} ; \<And>s n. P' (s,n) \<Longrightarrow> P (s,k*n) ; \<And>s n. Q (s,n) \<Longrightarrow> Q' (s,n div k); k>0 \<rbrakk> \<Longrightarrow> 
           \<turnstile>\<^sub>3\<^sub>b {P'}c{ Q'}"   

  
  
inductive
  hoare3' :: "assn2 \<Rightarrow> com \<Rightarrow> assn2 \<Rightarrow> bool" ("\<turnstile>\<^sub>3\<^sub>' ({(1_)}/ (_)/ { (1_)})" 50)
where

Skip:  "\<turnstile>\<^sub>3\<^sub>' {$1} SKIP { $0}"  |


Assign:  "\<turnstile>\<^sub>3\<^sub>' {lmaps_to_expr_x x a v ** $1} x::=a { (%(s,c). dom s = vars a - {x} \<and> c = 0) ** x \<hookrightarrow> v }"  |

Assign':  "\<turnstile>\<^sub>3\<^sub>' {pointsto x v' ** ( pointsto x v \<longrightarrow>* Q)  ** $1} x::= N v { Q }"  |


Assign2:  "\<turnstile>\<^sub>3\<^sub>' {\<exists>v . ( ((\<exists>v'. pointsto x v') ** ( pointsto x v \<longrightarrow>* Q)  ** $1)
                 and sep_true ** (%(ps,n). vars a \<subseteq> dom ps \<and> paval a ps = v  ) )} x::= a { Q }"  |



If: "\<lbrakk> \<turnstile>\<^sub>3\<^sub>' { \<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b True s } c\<^sub>1 { Q };
       \<turnstile>\<^sub>3\<^sub>' {  \<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b False s } c\<^sub>2 { Q } \<rbrakk>
  \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>' { (\<lambda>(s,n). P (s,n) \<and> vars b \<subseteq> dom s) ** $1} IF b THEN c\<^sub>1 ELSE c\<^sub>2 { Q}"   |

Frame:  "\<lbrakk>    \<turnstile>\<^sub>3\<^sub>' { P } C { Q  } \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>' { P ** F } C { Q ** F } "  |

Seq:  "\<lbrakk> \<turnstile>\<^sub>3\<^sub>' { P } C\<^sub>1 { Q } ;  \<turnstile>\<^sub>3\<^sub>' { Q } C\<^sub>2 { R  } \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>' { P } C\<^sub>1 ;; C\<^sub>2 { R } "  |

While:  "\<lbrakk> \<turnstile>\<^sub>3\<^sub>' { (\<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b True s) } C { (\<lambda>(s,n). P (s,n) \<and>  vars b \<subseteq> dom s)  ** $1 }  \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>' { (\<lambda>(s,n). P (s,n) \<and>  vars b \<subseteq> dom s) ** $1 } WHILE b DO C {  \<lambda>(s,n). P (s,n) \<and> lmaps_to_axpr b False s } "  |
   
conseq: "\<lbrakk> \<turnstile>\<^sub>3\<^sub>' {P}c{Q} ; \<And>s n. P' (s,n) \<Longrightarrow> P (s,k*n) ; \<And>s n. Q (s,n) \<Longrightarrow> Q' (s,n div k); k>0 \<rbrakk> \<Longrightarrow> 
           \<turnstile>\<^sub>3\<^sub>' {P'}c{ Q'}"   |

normalize:  "\<lbrakk>    \<turnstile>\<^sub>3\<^sub>' { P ** $m } C { Q  ** $n }; n\<le>m \<rbrakk>
             \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>' { P ** $(m-n) } C { Q } "   | 

Assign''': "\<turnstile>\<^sub>3\<^sub>' {  $1 ** (x \<hookrightarrow> ds) } x ::= (N v) {  (x \<hookrightarrow> v) }" |

Assign'''': "\<lbrakk>  symeval P a v; \<turnstile>\<^sub>3\<^sub>' {P} x ::= (N v) {Q'}  \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>' {P} x ::= a {Q'}" |

Assign4:  "\<turnstile>\<^sub>3\<^sub>' { (\<lambda>(ps,t). x\<in>dom ps \<and> vars a \<subseteq> dom ps \<and> Q (ps(x\<mapsto>(paval a ps)),t) ) ** $1} x::=a { Q }" |

False: "\<turnstile>\<^sub>3\<^sub>' {  \<lambda>(ps,n). False } c {  Q }" |

pureI: "( P \<Longrightarrow>  \<turnstile>\<^sub>3\<^sub>' { Q} c { R}) \<Longrightarrow>  \<turnstile>\<^sub>3\<^sub>' {\<up>P ** Q} c { R}"
   

(* which is more general Assign4 or Assign2 ? *)

definition A4 :: "vname \<Rightarrow> aexp \<Rightarrow> assn2 \<Rightarrow> assn2" 
  where "A4 x a Q = ((\<lambda>(ps,t). x\<in>dom ps \<and> vars a \<subseteq> dom ps \<and> Q (ps(x\<mapsto>(paval a ps)),t) ) ** $1)"
definition A2 :: "vname \<Rightarrow> aexp \<Rightarrow> assn2 \<Rightarrow> assn2" 
  where "A2 x a Q = (\<exists>v . ( ((\<exists>v'. pointsto x v') ** ( pointsto x v \<longrightarrow>* Q)  ** $1)
                 and sep_true ** (%(ps,n). vars a \<subseteq> dom ps \<and> paval a ps = v  ) ))"

    
lemma "A4 x a Q (ps,n) \<Longrightarrow> A2 x a Q (ps,n)"
unfolding A4_def A2_def sep_conj_def dollar_def sep_impl_def pointsto_def apply auto
  apply(rule exI[where x="paval a ps"])
  apply safe
  subgoal for n v
    apply(rule exI[where x="[x \<mapsto> v]::partstate"])
    apply(rule exI[where x=0])
    apply auto apply(rule exI[where x="ps(x:=None)"])
    apply auto
    unfolding sep_disj_fun_def domain_conv apply auto  
    unfolding plus_fun_conv apply auto 
      by (simp add: map_add_upd_left map_upd_triv) 
  subgoal for n v
    apply(rule exI[where x=0])
    apply(rule exI[where x=n])
    apply(rule exI[where x=ps])
    by auto 
  done
          
lemma "A2 x a Q (ps,n) \<Longrightarrow> A4 x a Q (ps,n)"
  unfolding A4_def A2_def sep_conj_def dollar_def sep_impl_def pointsto_def
  apply (auto simp: sep_disj_commute) 
  subgoal for aa ba ab ac bc xa bd apply(rule exI[where x=bd])
    by (auto simp: sep_add_ac  domain_conv sep_disj_fun_def)
  subgoal  for aa ba ab ac bc xa bd apply(rule exI[where x=bd])
    apply (auto simp: sep_add_ac)      
    subgoal apply (auto simp:   domain_conv sep_disj_fun_def)
      by (metis fun_upd_same none_def plus_fun_def)
    subgoal 
      by (metis domD map_add_dom_app_simps(1) plus_fun_conv subsetCE)      
    subgoal 
    proof -
      assume a: "ab + [x \<mapsto> xa] = aa + ac"
      assume b: "ps = aa + ac" and o: "aa ## ac"
      then have b': "ps = ac + aa" by(simp add: sep_add_ac)
      assume vars: "vars a \<subseteq> dom ac"
      have pa: "paval a ps = paval a ac" unfolding b' 
        apply(rule paval_extend) using o vars by (simp_all add: sep_add_ac)
        
      have f: "\<And>f. (ab + [x \<mapsto> xa])(x \<mapsto> f) = ab + [x \<mapsto> f]"
        by (simp add: plus_fun_conv) 
          
      assume "Q (ab + [x \<mapsto> paval a ac], bd)"
      thus "Q ((aa + ac)(x \<mapsto> paval a (aa + ac)), bd)"
        unfolding b[symmetric] pa
        unfolding b a[symmetric] pa f by auto
    qed
    done
  done
    
lemma E_extendsR: "\<turnstile>\<^sub>3\<^sub>a { P } c { F } \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>' { P } c { F }"      
  apply (induct  rule: hoare3a.induct)
    apply(intro hoare3'.Skip)
    apply(intro hoare3'.Assign4)
    subgoal using hoare3'.If by auto
    subgoal using hoare3'.Frame by auto
    subgoal using hoare3'.Seq by auto
    subgoal using hoare3'.While by auto
    subgoal using hoare3'.conseq[where k=1] by simp
    done
  
lemma E_extendsS: "\<turnstile>\<^sub>3\<^sub>b { P } c { F } \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>' { P } c { F }"      
  apply (induct  rule: hoare3b.induct)
    apply(erule E_extendsR) 
    using hoare3'.conseq  by blast
 
      


lemma Skip':  "P = (F ** $1) \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>' { P } SKIP { F }" 
  apply(rule conseq[where k=1])
    apply(rule Frame[where F=F])
     apply(rule Skip)
    by (auto simp: sep_conj_ac)
 
  
subsubsection "experiments with explicit and implicit GarbageCollection"
 
lemma "( (\<forall>ps n. P (ps,n)
 \<longrightarrow> (\<exists>ps' ps'' m e e'. ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'') 
     \<and> ps' ## ps'' \<and>  n =  e + e' + m
     \<and> Q (ps',e))))
  \<longleftrightarrow>   (\<forall>ps n. P (ps,n) \<longrightarrow> (\<exists>ps' m e . ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps')   \<and>  n = e  + m \<and> (Q ** (\<lambda>_. True)) (ps',e)))"

proof (safe)
  fix ps n
  assume "\<forall>ps n. P (ps, n) \<longrightarrow> (\<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> n = e + e' + m \<and> Q (ps', e))"
    "P (ps, n)"
  then obtain ps' ps'' m e e' where C: "(c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> n = e + e' + m \<and> Q (ps', e)" by blast
  show "\<exists>ps' m e. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<and> n = e + m \<and> (Q ** (\<lambda>_. True)) (ps',e)"   unfolding   sep_conj_def
    apply(rule exI[where x="ps' + ps''"])
    apply(rule exI[where x="m"])
    apply(rule exI[where x="e+e'"]) using C   by auto
next
  fix ps n
  assume "\<forall>ps n. P (ps,n) \<longrightarrow> (\<exists>ps' m e . ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps')   \<and>  n = e  + m \<and> (Q ** (\<lambda>_. True)) (ps',e))"
    "P (ps, n)"
  then obtain ps' m e where C: "((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps')   \<and>  n = e  + m" and Q: "(Q ** (\<lambda>_. True)) (ps',e)" by blast
  from Q obtain ps1 ps2 e1 e2 where Q': "Q (ps1,e1)" "ps'=ps1+ps2" "ps1##ps2" "e=e1+e2" unfolding sep_conj_def by auto
  show "\<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> n = e + e' + m \<and> Q (ps', e)"
    apply(rule exI[where x="ps1"])
    apply(rule exI[where x="ps2"])
    apply(rule exI[where x="m"])
    apply(rule exI[where x="e1"])
    apply(rule exI[where x="e2"]) using C Q' by auto
qed
       
subsection \<open>Soundness\<close>

theorem hoareT_sound2_part: assumes "\<turnstile>\<^sub>3\<^sub>' { P }c{ Q  }"
  shows "\<Turnstile>\<^sub>3\<^sub>' { P } c { Q }" using assms        
proof(induction  rule: hoare3'.induct) 
   case (conseq P c Q P' k1 Q')
  then obtain k where p: "\<forall>ps n. P (ps, n) \<longrightarrow> (\<exists>ps' ps'' m e e'. ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'')  \<and> ps' ## ps'' \<and> k * n = k * e + e' + m \<and> Q (ps',e))" and gt0: "k>0"
    unfolding hoare3o_valid_def by blast
      
      
  show ?case    unfolding hoare3o_valid_def
    apply(rule exI[where x="k*k1"])
    apply safe
    using gt0 conseq(4) apply simp
  proof -
    fix ps n
    assume "P' (ps,n)"
    with conseq(2) have "P (ps, k1*n)" by simp
    with p obtain ps' ps'' m e e' where pB: "(c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps''" and orth: "ps' ## ps''"
          and m: "k * (k1 * n) = k*e + e' + m" and Q:  "Q (ps', e)"  by blast
                 
    from Q conseq(3) have Q': "Q' (ps', e div k1)" by auto
      
    have "k * k1 * n = k*e + e' + m" using m by auto
    also have "\<dots> = k*(k1 * (e div k1) + e mod k1) + e' + m" using mod_mult_div_eq by simp
    also have "\<dots> = k*k1*(e div k1) + (k*(e mod k1) + e') + m"
      by (metis add.assoc distrib_left mult.assoc) 
    finally have "k * k1 * n = k * k1 * (e div k1) + (k * (e mod k1) + e') + m" .
      
        
    show "\<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * k1 * n = k * k1 * e + e' + m \<and> Q' (ps', e)"
      apply(rule exI[where x="ps'"])
      apply(rule exI[where x="ps''"])
      apply(rule exI[where x=m])
      apply(rule exI[where x="e div k1"])
      apply(rule exI[where x="k * (e mod k1) + e'"])
      apply safe apply fact apply fact apply fact apply fact done
  qed  
next     
  case (Frame P c Q F)
  from Frame(2)[unfolded hoare3o_valid_def]  obtain k
    where hyp: "\<forall>ps n. P (ps, n) \<longrightarrow> (\<exists>ps' ps'' m e e'. ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'')  \<and> ps' ## ps'' \<and> k * n = k * e + e' + m \<and> Q (ps',e))"
        and k: "k>0"
    unfolding hoare3o_valid_def by blast
      
  show ?case unfolding hoare3o_valid_def apply(rule exI[where x=k]) using k apply simp
  proof(safe)
    fix ps n
    assume "(P \<and>* F) (ps, n)"
    then obtain ps1 ps2 where orth: "ps1 ## ps2" and add: "(ps, n) = ps1 + ps2"
                  and P: "P ps1" and F: "F ps2" unfolding sep_conj_def by blast
    from hyp P have "(\<exists>ps' ps'' m e e'. ((c,fst ps1) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'')  \<and> ps' ## ps'' \<and> k * snd ps1 = k * e + e' + m \<and> Q (ps',e))"
      by simp
    then obtain ps' ps'' m e e' where a: "(c, fst ps1) \<Rightarrow>\<^sub>A m \<Down> ps' + ps''" and orth2[simp]: "ps' ## ps''"
              and m: "k * snd ps1 = k * e + e' + m"  and Q: "Q (ps', e)" by blast                                                      
   
    from big_step_t3_post_dom_conv[OF a] have dom: "dom (ps' + ps'') = dom (fst ps1)" by auto         
        
        
    from add have g: "ps = fst ps1 + fst ps2" and h: "n = snd ps1 + snd ps2" by (auto simp add: plus_prod_def)  
      
    from orth have [simp]: "fst ps2 ## ps'" "fst ps2 ## ps''"
       apply (metis dom map_convs(1) orth2 sep_disj_addD1 sep_disj_commuteI sep_disj_fun_def sep_disj_prod_def) 
      by (metis dom map_convs(1) orth orth2 sep_add_commute sep_disj_addD1 sep_disj_commuteI sep_disj_fun_def sep_disj_prod_def)
        
    then have e: "ps' ## fst ps2" unfolding sep_disj_fun_def using dom   unfolding domain_conv  by blast
        
    have 3: "(Q \<and>* F) (ps'+fst ps2, e+snd ps2)" unfolding sep_conj_def
        apply(rule exI[where x="(ps',e)"])
      apply(rule exI[where x="ps2"])
      apply safe
      subgoal  using orth  unfolding sep_disj_prod_def apply (auto simp: sep_disj_nat_def) 
        apply(rule e) done             
      subgoal unfolding plus_prod_def apply auto done
        apply fact apply fact done
        
    show "\<exists>ps' ps'' m. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> (\<exists>e. (\<exists>e'. k * n = k * e + e' + m) \<and> (Q \<and>* F) (ps', e))" 
      apply(rule exI[where x="ps'+fst ps2"])
      apply(rule exI[where x="ps''"])
      apply(rule exI[where x=m])
    proof safe
      show "(c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + fst ps2 + ps''"
        apply(rule Framer2[OF _ _ g]) apply (fact a)
         using orth apply (auto simp: sep_disj_prod_def)
         by (metis \<open>fst ps2 ## ps''\<close> \<open>fst ps2 ## ps'\<close> orth2 sep_add_assoc sep_add_commute sep_disj_commuteI)   
     next
       show "ps' + fst ps2 ## ps''"
         by (metis dom map_convs(1) orth orth2 sep_add_disjI1 sep_disj_fun_def sep_disj_prod_def)
     next
       show "\<exists>e. (\<exists>e'. k * n = k * e + e' + m) \<and> (Q \<and>* F) (ps' + fst ps2, e)"
         apply(rule exI[where x="e+snd ps2"])
         apply safe
         subgoal proof(rule exI[where x=e'])
           have "k * n = k * snd ps1 + k * snd ps2" unfolding h by (simp add: distrib_left)  
           also have "\<dots> =  k * e + e' + m + k* snd ps2" unfolding m by auto
           finally show "k * n = k * (e + snd ps2) + e' + m"
             by algebra
         qed  apply fact done
     qed 
   qed
next 
  case (False c Q)    
  then show ?case by (auto simp: hoare3o_valid_def) 
next
  case (Assign2 x Q a)
  show ?case 
    unfolding hoare3o_valid_def
    apply (rule exI[where x=1], safe) apply auto
    proof -
      fix ps n v
      assume A: "((\<lambda>s. \<exists>xa. (x \<hookrightarrow> xa) s) \<and>* (x \<hookrightarrow> v \<longrightarrow>* Q) \<and>* $ (Suc 0)) (ps, n)"
      assume B: "((\<lambda>s. True) \<and>* (\<lambda>(ps, n). vars a \<subseteq> dom ps \<and> paval a ps = v)) (ps, n)"
        
        
      from A obtain ps1 ps2 n1 n2 v' where  "ps1 ## ps2" and add1: "ps = ps1 + ps2" and n: "n = n1 + n2" and
         1: "(\<exists>xaa. (x \<hookrightarrow> xaa) (ps1,n1))"
         and 2:  "((x \<hookrightarrow> v \<longrightarrow>* Q) \<and>* $ (Suc 0)) (ps2,n2)"  unfolding sep_conj_def
        by fastforce
          
      from 2 obtain ps2a ps2b n2a n2b where "ps2a ## ps2b" and add2: "ps2 = ps2a + ps2b" and n2: "n2 = n2a + n2b"
        and Q: "(x \<hookrightarrow> v \<longrightarrow>* Q) (ps2a,n2a)" and ps2b: "ps2b=0" and n2b: "n2b=1" unfolding dollar_def sep_conj_def
        by fastforce
          
        
      from 1 obtain v' where n1: "n1=0" and p: "ps1 = ([x \<mapsto> v']::partstate)" 
          and x: "x : dom ps1" by (auto simp: pointsto_def)
      from x add1 have x: "x : dom ps"
        by (simp add: plus_fun_conv subset_iff) 
           
      have f: "([x \<mapsto> v'] + ps2a)(x \<mapsto> v) = ps2a + [x \<mapsto> v]"
        by (smt \<open>\<And>thesis. (\<And>v'. \<lbrakk>n1 = 0; ps1 = [x \<mapsto> v']; x \<in> dom ps1\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>ps1 ## ps2\<close> add2 disjoint_iff_not_equal dom_fun_upd domain_conv fun_upd_upd map_add_upd_left option.distinct(1) plus_fun_conv ps2b sep_add_commute sep_add_zero sep_disj_fun_def) 
        
          
      let ?n' = "n2a + n1"
      from n n2 n2b have n': "n=1+?n'" by simp
      have Q': "Q (ps(x \<mapsto> v), ?n')" using Q n1 unfolding sep_impl_def apply auto
        unfolding pointsto_def apply auto
        subgoal 
          by (metis \<open>ps1 ## ps2\<close> \<open>ps2 = ps2a + ps2b\<close> \<open>ps2b = 0\<close> dom_fun_upd domain_conv option.distinct(1) p sep_add_zero sep_disj_commute sep_disj_fun_def)
        subgoal unfolding add1 p add2 ps2b
          by (auto simp: f)  
        done
            
      from B obtain ps1 ps2 n1 n2 where orth: "ps1 ## ps2" and add: "ps = ps2 + ps1" and n: "n=n1+n2"
          and vars: "vars a \<subseteq> dom ps2" and v: "paval a ps2 = v"
        unfolding sep_conj_def by (auto simp: sep_add_ac)
          
      from vars add have a: "vars a \<subseteq> dom ps"
        by (simp add: plus_fun_conv subset_iff)          
          
      from a x have "vars a \<union> {x} \<subseteq> dom ps" by auto
          
      have "paval a ps = v" unfolding add apply(subst paval_extend)
        using orth vars v by(auto simp: sep_disj_commute)
          
        
      show "\<exists>ps' ps'' m. (x ::= a, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> (\<exists>e. (\<exists>e'. n = e + e' + m) \<and> Q (ps', e))"
        apply(rule exI[where x="ps(x\<mapsto>v)"])
        apply(rule exI[where x=0])
        apply(rule exI[where x="Suc 0"])
        apply auto
        apply(rule big_step_t_part.Assign)
           apply fact+ apply simp 
        apply(rule exI[where x="?n'"])
          apply safe 
          apply(rule exI[where x=0]) using n' apply simp
          using Q' by auto
          
    qed
next
  case Skip
  then show ?case by (auto simp: hoare3o_valid_def dollar_def)   
next
  case (Assign4 x a Q)
  then show ?case
    apply (auto simp: dollar_def sep_conj_def  hoare3o_valid_def ) 
      apply(rule exI[where x=1]) apply auto
      subgoal for ps b y
        apply(rule exI[where x="ps(x \<mapsto> paval a ps)"])
        apply(rule exI[where x="0"])
        apply(rule exI[where x="Suc 0"]) apply auto
          apply(rule exI[where x=b]) by auto
      done
next
  case (Assign' x v' v Q )
  have "\<And>aa. aa ## [x \<mapsto> v'] \<Longrightarrow>
       \<not> aa ## [x \<mapsto> v] \<Longrightarrow> False"   unfolding sep_disj_fun_def domain_def
    apply auto by (smt Collect_conj_eq Collect_empty_eq) 
  have f: "\<And>v'. domain [x \<mapsto> v'] = {x}" unfolding domain_conv by auto 
     
  { fix ps
    assume u: "ps ## [x \<mapsto> v']"
    have 2: "[x \<mapsto> v'] + ps = ps + [x \<mapsto> v']"
          "[x \<mapsto> v] + ps = ps + [x \<mapsto> v]"
         subgoal apply (subst sep_add_commute) using u by (auto simp: sep_add_ac) 
         subgoal apply (subst sep_add_commute) using u apply (auto simp: sep_add_ac)
             unfolding sep_disj_fun_def f by auto  done
    have "(x ::= N v, [x \<mapsto> v'] + ps) \<Rightarrow>\<^sub>A Suc 0 \<Down> [x \<mapsto> v] + ps"
      apply(rule Framer[OF big_step_t_part.Assign])
         apply simp_all using u  by (auto simp: sep_add_ac) 
    then have "(x ::= N v, ps + [x \<mapsto> v']) \<Rightarrow>\<^sub>A Suc 0 \<Down> ps + [x \<mapsto> v]" 
      by (simp only: 2)  
  } note f2 = this
      
  from Assign' show ?case 
    apply (auto simp: dollar_def sep_conj_def pointsto_def sep_impl_def hoare3o_valid_def ) 
    apply(rule exI[where x=1]) apply (auto simp: sep_add_ac) 
    subgoal unfolding sep_disj_fun_def f by auto 
    subgoal for ps n
      apply(rule exI[where x="ps+[x \<mapsto> v]"])
      apply(rule exI[where x="0"])
      apply(rule exI[where x="Suc 0"])
      apply safe 
      subgoal using f2 by auto
      subgoal  by auto 
      subgoal by force
      done
    done
next
  case (Assign x a v)   
  then show ?case unfolding hoare3o_valid_def
    apply(rule exI[where x=1]) 
    apply auto apply (auto simp: dollar_def )
      subgoal for ps n
         apply (subst (asm) separate_othogonal) apply auto
      apply(rule exI[where x="ps(x:=Some v)"])
      apply(rule exI[where x="0"])
      apply(rule exI[where x="1"])
      apply auto 
      apply (auto simp: pointsto_def)  unfolding  sep_conj_def
    subgoal  apply(rule exI[where x="((%y. if y=x then None else ps y) , 0)"])
      apply(rule exI[where x="((%y. if y = x then Some (paval a ps) else None),0)"])
        apply (auto simp: sep_disj_prod_def sep_disj_fun_def plus_fun_def)
      apply (smt domIff domain_conv)
      apply (metis domI insertE option.simps(3))
      using domIff by fastforce
    done  
  done
next
  case (If P b c\<^sub>1 Q c\<^sub>2)
  from If(3)[unfolded hoare3o_valid_def]
    obtain k1 where T: "\<And>ps n. P (ps, n) \<Longrightarrow> vars b \<subseteq> dom ps \<Longrightarrow> pbval b ps
     \<Longrightarrow> (\<exists>ps' ps'' m e e'. (c\<^sub>1, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k1 * n = k1 * e + e' + m \<and> Q (ps', e))"
        and k1: "k1 > 0" by force
  from If(4)[unfolded hoare3o_valid_def]
    obtain k2 where F: "\<And>ps n. P (ps, n) \<Longrightarrow> vars b \<subseteq> dom ps \<Longrightarrow> \<not> pbval b ps
     \<Longrightarrow> (\<exists>ps' ps'' m e e'. (c\<^sub>2, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k2 * n = k2 * e + e' + m \<and> Q (ps', e))"
        and k2: "k2 > 0" by force
        
    show ?case unfolding hoare3o_valid_def apply auto apply (auto simp: dollar_def)   
        apply(rule exI[where x="k1 * k2"]) using k1 k2 apply auto
  proof (goal_cases)
    case (1 ps n)   
    then obtain n' where P: "P (ps, n')" and dom: "vars b \<subseteq> dom ps" and Suc: "n = Suc n'" unfolding sep_conj_def
      by force
    show ?case 
    proof(cases "pbval b ps")
      case True
      with T[OF P dom] obtain ps' ps'' m e e' where d: "(c\<^sub>1, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps''"
            and orth: "ps' ## ps''" and m1:  "k1 * n' = k1 * e + e' + m" and Q:  "Q (ps', e)"
          by blast
        from big_step_t3_post_dom_conv[OF d] have klong: "dom (ps' + ps'') = dom ps" . 
      from k1 obtain k1' where k1': "k1 = Suc k1'"
        using gr0_implies_Suc by blast 
      from k2 obtain k2' where k2': "k2 = Suc k2'"
        using gr0_implies_Suc by blast 
      let ?e1 = "(k2' * (e' + m + k1) + e' + k1')"
      show ?thesis
        apply(rule exI[where x=ps']) 
        apply(rule exI[where x=ps'']) apply(rule exI[where x="m+1"])   
          apply safe
            apply(rule big_step_t_part.IfTrue)
              apply (rule dom)
              apply fact
               apply (rule True)
           apply (rule d)
          apply simp 
         apply fact
        subgoal apply(rule exI[where x="e"])
          apply safe
          subgoal proof (rule exI[where x="?e1"]) 
            have "k1 * k2 * n = k2 * (k1*n)" by auto
            also have "\<dots> = k2 * (k1*n' + k1)" unfolding Suc  by auto
            also have "\<dots> = k2 * (k1 * e + e' + m + k1)" unfolding m1 by auto
            also have "\<dots> = k1 * k2 * e + k2* (e' + m + k1)"  by algebra
            also have "\<dots> = k1 * k2 * e + k2' * (e' + m + k1) + (e' + m + k1)" unfolding k2'
              by simp 
            also have "\<dots> = k1 * k2 * e + k2' * (e' + m + k1) + (e' + k1' + m + 1)" unfolding k1' by simp
            also have "\<dots> = k1 *k2*e + (k2' * (e' + m + k1) + e' + k1') + (m+1)" by algebra  
            finally show "k1 * k2 * n = k1 * k2 * e + ?e1 + (m + 1)" .
          qed  using Q by force   
        done          
    next
      case False
      with F[OF P dom] obtain ps' ps'' m e e' where d: "(c\<^sub>2, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps''"
            and orth: "ps' ## ps''" and m2:  "k2 * n' = k2 * e + e' + m" and Q:  "Q (ps', e)"
          by blast
        from big_step_t3_post_dom_conv[OF d] have klong: "dom (ps' + ps'') = dom ps" . 
      from k1 obtain k1' where k1': "k1 = Suc k1'"
        using gr0_implies_Suc by blast 
      from k2 obtain k2' where k2': "k2 = Suc k2'"
        using gr0_implies_Suc by blast 
      let ?e2 = "(k1' * (e' + m + k2) + e' + k2')"
      show ?thesis
        apply(rule exI[where x=ps']) 
        apply(rule exI[where x=ps'']) apply(rule exI[where x="m+1"])   
          apply safe
            apply(rule big_step_t_part.IfFalse)
              apply (rule dom)
              apply fact
               apply (rule False)
           apply (rule d)
          apply simp 
         apply fact
        subgoal apply(rule exI[where x="e"])
          apply safe
          subgoal proof (rule exI[where x="?e2"]) 
            have "k1 * k2 * n = k1 * (k2*n)" by auto
            also have "\<dots> = k1 * (k2*n' + k2)" unfolding Suc  by auto
            also have "\<dots> = k1 * (k2 * e + e' + m + k2)" unfolding m2 by auto
            also have "\<dots> = k1 * k2 * e + k1* (e' + m + k2)"  by algebra
            also have "\<dots> = k1 * k2 * e + k1' * (e' + m + k2) + (e' + m + k2)" unfolding k1'
              by simp 
            also have "\<dots> = k1 * k2 * e + k1' * (e' + m + k2) + (e' + k2' + m + 1)" unfolding k2' by simp
            also have "\<dots> = k1 *k2*e + (k1' * (e' + m + k2) + e' + k2') + (m+1)" by algebra  
            finally show "k1 * k2 * n = k1 * k2 * e + ?e2 + (m + 1)" .
          qed  using Q by force   
        done
    qed 
  qed
next
  case (Seq P C\<^sub>1 Q C\<^sub>2 R) 
    
  from Seq(3)[unfolded hoare3o_valid_def] obtain k1 where
    1: "(\<forall>ps n. P (ps, n) \<longrightarrow> (\<exists>ps' ps'' m e e'. (C\<^sub>1, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k1 * n = k1 * e + e' + m \<and> Q (ps', e)))"
      and k10: "k1 > 0" by blast
  from Seq(4)[unfolded hoare3o_valid_def]  obtain k2 where 
    2: " (\<forall>ps n. Q (ps, n) \<longrightarrow> (\<exists>ps' ps'' m e e'. (C\<^sub>2, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k2 * n = k2 * e + e' + m \<and> R (ps', e)))"
      and k20: "k2 > 0" by blast
      
  from k10 obtain k1' where k1': "k1 = Suc k1'"
    using gr0_implies_Suc by blast 
  from k20 obtain k2' where k2': "k2 = Suc k2'"
    using gr0_implies_Suc by blast 
        
  show ?case unfolding hoare3o_valid_def
  apply(rule exI[where x="k2*k1"])
  proof safe        
    fix ps n      
    assume "P (ps, n)"
      
    with 1 obtain ps1' ps1'' m1 e1 e1' where C1: "(C\<^sub>1, ps) \<Rightarrow>\<^sub>A m1 \<Down> ps1' + ps1''" and orth: "ps1' ## ps1''"
          and m1: "k1 * n = k1 * e1 + e1' + m1"and Q: "Q (ps1', e1)" by blast
      
    from Q and 2 obtain ps2' ps2'' m2 e2 e2' where C2: "(C\<^sub>2, ps1') \<Rightarrow>\<^sub>A m2 \<Down> ps2' + ps2''" and orth2: "ps2' ## ps2''"
        and m2: "k2 * e1 = k2 * e2 + e2' + m2" and R: "R (ps2', e2)" by blast
    
    let ?ee = "(k1 *e2'  + k2*e1' +k2'*m1+ k1'*m2)"
      
    show "\<exists>ps' ps'' m e e'. (C\<^sub>1;; C\<^sub>2, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k2 * k1 * n = k2 * k1 * e + e' + m \<and> R (ps', e)"
      apply(rule exI[where x=ps2'])
        apply(rule exI[where x="ps2'' + ps1''"])
        apply(rule exI[where x="m1+m2"])
        apply(rule exI[where x="e2"])
      apply(rule exI[where x="?ee"])
    proof safe
      have C2': "(C\<^sub>2, ps1' + ps1'') \<Rightarrow>\<^sub>A m2 \<Down> ps2' + (ps2'' + ps1'')" 
        apply(rule Framer2[OF C2, of ps1'']) apply fact apply simp
          using sep_add_assoc
          by (metis C2 big_step_t3_post_dom_conv map_convs(1) orth orth2 sep_add_commute sep_disj_addD1 sep_disj_commuteI sep_disj_fun_def)
      show "(C\<^sub>1;; C\<^sub>2, ps) \<Rightarrow>\<^sub>A m1 + m2 \<Down> ps2' + (ps2'' + ps1'')"
        using C1 C2' by auto
    next
      show "ps2' ## ps2'' + ps1''"
        by (metis C2 big_step_t3_post_dom_conv map_convs(1) orth orth2 sep_disj_addI3 sep_disj_fun_def)
    next
      have "k2 * k1 * n = k2 * (k1 * n)" by auto
      also have "\<dots> = k2 * (k1 * e1 + e1' + m1)" using m1 by auto
      also have "\<dots> = k1 * k2 * e1 + k2 * (e1' + m1)" by algebra
      also have "\<dots> = k1 * (k2 * e2 + e2' + m2) + k2 * (e1' + m1)" using m2 by auto
      also have "\<dots> = k2 * k1 * e2 + (k1 *e2'  + k2*e1' +k2*m1+ k1*m2)" by algebra
      also have "\<dots> = k2 * k1 * e2 + (k1 *e2'  + k2*e1' +k2'*m1+m1+ k1'*m2+m2)" unfolding k1' k2' by auto
      also have "\<dots> = k2 * k1 * e2 + (k1 *e2'  + k2*e1' +k2'*m1+ k1'*m2)+(m1+m2)"  by auto
      finally show "k2 * k1 * n = k2 * k1 * e2 + ?ee + (m1 + m2)" .
    qed fact 
  qed (simp add: k10 k20)     
next
  case (While P b C) 
     
   {
     assume "\<exists>k>0. \<forall>ps n. (case (ps, n) of (s, n) \<Rightarrow> P (s, n) \<and> lmaps_to_axpr b True s) \<longrightarrow>
                 (\<exists>ps' ps'' m e e'. (C, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * n = k * e + e' + m \<and> ((\<lambda>(s, n). P (s, n) \<and> vars b \<subseteq> dom s) \<and>* $ 1) (ps', e))"
     then obtain k where  While2: "\<forall>ps n. (case (ps, n) of (s, n) \<Rightarrow> P (s, n) \<and> lmaps_to_axpr b True s) \<longrightarrow> (\<exists>ps' ps'' m e e'. (C, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * n = k * e + e' + m \<and> ((\<lambda>(s, n). P (s, n) \<and> vars b \<subseteq> dom s) \<and>* $ 1) (ps', e))" and k: "k>0" by blast
         
  from k obtain k' where k': "k = Suc k'"
    using gr0_implies_Suc by blast
      
    have "\<exists>k>0. \<forall>ps n. ((\<lambda>(s, n). P (s, n) \<and> vars b \<subseteq> dom s) \<and>* $ 1) (ps, n) \<longrightarrow>
                 (\<exists>ps' ps'' m e e'.
                     (WHILE b DO C, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and>
                     ps' ## ps'' \<and> k * n = k * e + e' + m \<and> (case (ps', e) of (s, n) \<Rightarrow> P (s, n) \<and> lmaps_to_axpr b False s))" (* 
    have "\<exists>k>0. \<forall>ps n. ((\<lambda>(s, n). P (s, n) \<and> vars b \<subseteq> dom s) \<and>* $ 1) (ps, n) \<longrightarrow> (\<exists>ps' m. (WHILE b DO C, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<and> m \<le> k * n \<and> (case (ps', n - m) of (s, n) \<Rightarrow> P (s, n) \<and> lmaps_to_axpr b False s))"
   *)   proof (rule exI[where x=k], safe, goal_cases)
    case (2 ps n)  
    from 2 show ?case  
      proof(induct n arbitrary: ps rule: less_induct)
        case (less x ps3) 
          
      show ?case 
      proof(cases "pbval b ps3")
        case True
        from less(2) obtain x' where P: "P (ps3, x')" and dom: "vars b \<subseteq> dom ps3"  and Suc: "x = Suc x'" unfolding sep_conj_def dollar_def by auto 
        from P dom True have 
           g: "((\<lambda>(s, n). P (s, n) \<and> lmaps_to_axpr b True s)) (ps3, x')" 
            unfolding dollar_def by auto  
          from While2 g obtain ps3' ps3'' m e e' where C: "(C, ps3) \<Rightarrow>\<^sub>A m \<Down> ps3' + ps3''" and orth: "ps3' ## ps3''"
                and x: "k * x' = k * e + e' + m" and P': "((\<lambda>(s, n). P (s, n) \<and> vars b \<subseteq> dom s) \<and>* $ 1) (ps3', e)" by blast
          then obtain x''' where P'': "P (ps3', x''')" and domb: "vars b \<subseteq> dom ps3'" and Suc'': "e = Suc x'''"
              unfolding sep_conj_def dollar_def by auto  
              
          from C big_step_t3_post_dom_conv have "dom ps3 = dom (ps3' + ps3'')" by simp
          with dom have dom': "vars b \<subseteq> dom (ps3' + ps3'')" by auto
              
          from C big_step_t3_gt0 have gt0: "m > 0" by auto
            
          have "e < x" using  x Suc gt0
            by (metis k le_add1 le_less_trans less_SucI less_add_same_cancel1 nat_mult_less_cancel1)   
 
          (*have "\<exists>ps' m. (WHILE b DO C, ps3') \<Rightarrow>\<^sub>A m \<Down> ps' \<and> m \<le> k * (x - (1 + m)) \<and> P (ps', (x - (1 + m)) - m) \<and> vars b \<subseteq> dom ps' \<and> \<not> pbval b ps'"
           *)
          have "\<exists>ps' ps'' m e2 e2'. (WHILE b DO C, ps3') \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * e = k * e2 + e2' + m \<and> P (ps', e2) \<and> lmaps_to_axpr b False ps'" 
                 apply(rule less(1))
             apply fact by fact 
              
          then obtain ps4' ps4'' mt et et' where w: "((WHILE b DO C, ps3') \<Rightarrow>\<^sub>A mt \<Down> ps4' + ps4'')"
              and ortho: "ps4' ## ps4''" and m'': "k * e = k * et + et' + mt"
              and P'': "P (ps4', et)" and dom'': "vars b \<subseteq> dom ps4'" and b'': "\<not> pbval b ps4'" by auto
                 
          have "ps4'' ## ps3''" and "ps4' ## ps3''" by (metis big_step_t3_post_dom_conv domain_conv orth ortho sep_add_disjD sep_disj_fun_def w)+  
              
          show ?thesis
            apply(rule exI[where x="ps4'"])
            apply(rule exI[where x="(ps4'' +  ps3'')"])
            apply(rule exI[where x="1 + m + mt"])
            apply(rule exI[where x="et"])
            apply(rule exI[where x=" et'  + k' + e'"])
          proof (safe)
            have "(WHILE b DO C, ps3' + ps3'') \<Rightarrow>\<^sub>A mt \<Down> ps4' + (ps4'' +  ps3'')"
              apply(rule Framer2[OF w, of ps3'']) apply fact
               apply simp 
              apply(rule sep_add_assoc[symmetric])
                by fact+
            show "(WHILE b DO C, ps3) \<Rightarrow>\<^sub>A 1 + m + mt \<Down> ps4' + (ps4'' +  ps3'')"
              apply(rule WhileTrue) apply fact apply fact apply (fact C) apply fact by auto
          next
            show "ps4' ## ps4'' + ps3''"
              by (metis big_step_t3_post_dom_conv domain_conv orth ortho sep_disj_addI3 sep_disj_fun_def w)   
          next 
            have "k * x = k * x' + k" unfolding Suc by auto
            also have "\<dots> = k * e + e' + m + k" unfolding x by simp
            also have "\<dots> = k * et + et' + mt + e' + m + k" using m'' by simp
            also have "\<dots> = k * et + et' + mt + e' + m + 1 + k'" using k' by simp
            also have "\<dots> = k * et + ( et'  + k' + e') + (1 + m + mt)" using k' by simp
            finally show "k * x = k * et + ( et'  + k' + e') + (1 + m + mt)" by simp
          next
            show "P (ps4', et)" by fact
          next
            show "lmaps_to_axpr b False ps4'" apply simp using dom'' b'' .. 
          qed                   
      next
        case False
        from less(2) obtain x' where P: "P (ps3, x')" and dom: "vars b \<subseteq> dom ps3" and Suc: "x = Suc x'" unfolding dollar_def sep_conj_def
          by force
        show ?thesis 
        apply(rule exI[where x=ps3])
        apply(rule exI[where x=0])
        apply(rule exI[where x="Suc 0"])
        apply(rule exI[where x="x'"])
          apply(rule exI[where x="k'"]) apply safe
            apply simp apply (rule big_step_t_part.WhileFalse)
        subgoal using dom by simp 
            apply fact apply simp
        using Suc k k' apply simp
        using P Suc apply simp
          using dom apply auto
          using False apply auto done    
      qed 
        
      qed
       
  qed (fact)
      
      
} with While(2)
  show ?case  unfolding hoare3o_valid_def by simp
next 
  case (Assign''' x ds v)
  then show ?case  
    unfolding hoare3o_valid_def apply auto 
    apply(rule exI[where x=1]) apply auto
    subgoal for ps n apply(rule exI[where x="ps(x\<mapsto>v)"]) apply(rule exI[where x="0"])
      apply(rule exI[where x="Suc 0"]) 
      apply safe 
        apply(rule big_step_t_part.Assign)
        apply (auto) 
         subgoal apply(subst (asm) separate_othogonal_commuted') by(auto simp: dollar_def pointsto_def)
         subgoal apply(subst (asm) separate_othogonal_commuted') by(auto simp: dollar_def pointsto_def)
         done
       done          
next
  case (Assign'''' P a v x Q')
  from Assign''''(3)[unfolded hoare3o_valid_def] obtain k where k: "k>0" and 
   A: " \<forall>ps n. P (ps, n) \<longrightarrow> (\<exists>ps' ps'' m e e'. (x ::= N v, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * n = k * e + e' + m \<and> Q' (ps', e)) "
    by auto
  show ?case   
    unfolding hoare3o_valid_def apply auto 
    apply(rule exI[where x=k]) using k apply auto
    proof (goal_cases)
      case (1 ps n)
      with A obtain ps' ps'' m e e' 
        where " (x ::= N v, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps''" and orth: "ps' ## ps''" and m: "k * n = k * e + e' + m" and Q: "Q' (ps', e)" by metis
      from 1(2) Assign''''(1)[unfolded symeval_def] have "paval' a ps = Some v" by auto
      show ?case apply(rule exI[where x=ps']) apply(rule exI[where x=ps'']) apply(rule exI[where x=m])
          apply safe
          apply(rule avalDirekt3_correct) apply fact+
          apply(rule exI[where x=e]) apply safe
          apply(rule exI[where x=e']) apply fact 
          apply fact done  
    qed 
next
  case (pureI P Q c R)
  show ?case
  proof (cases "P")
    case True
    with pureI(2)[unfolded hoare3o_valid_def] obtain k where k: "k>0" and
     thing: " \<forall>ps n. Q (ps, n) \<longrightarrow> (\<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * n = k * e + e' + m \<and> R (ps', e))" by auto
        
    show ?thesis unfolding hoare3o_valid_def apply(rule exI[where x=k])
      apply safe apply fact
      using thing by fastforce
  next
    case False
    show ?thesis unfolding hoare3o_valid_def apply(rule exI[where x=1])
        using False by auto
    qed 
      next
case (normalize P m C Q n)
  then show ?case unfolding hoare3o_valid_def
  apply(safe) subgoal for k apply(rule exI[where x=k]) apply safe proof (goal_cases)
    case (1 ps N)
    have Q2: "P (ps, N - (m - n))" apply(rule stardiff) by fact
    have mn: "m - n \<le> N" apply(rule stardiff(2)) by fact 
    have P: "(P \<and>* $ m) (ps, N - (m - n) + m)"  unfolding sep_conj_def dollar_def
      apply(rule exI[where x="(ps,N - (m - n))"]) apply(rule exI[where x="(0,m)"])
      apply(auto simp: sep_disj_prod_def sep_disj_nat_def) by fact
    have N: " N - (m - n) + m =  N +n" using normalize(2)
      using mn by auto 
    from P N have P': "(P \<and>* $ m) (ps, N +n)"    by auto
        
    from P' 1(4) obtain ps' ps'' m' e e' where "(C, ps) \<Rightarrow>\<^sub>A m' \<Down> ps' + ps''" and orth: "ps' ## ps''"
        and m': "k * (N +n) = k * e + e' + m'" and Q: "(Q \<and>* $ n) (ps', e)" by blast 
        
    have Q2: "Q (ps', e - n)" apply(rule stardiff) by fact
    
    have en: "e\<ge>n" using Q
      using stardiff(2) by blast     
        
    show ?case
      apply(rule exI[where x="ps'"])
      apply(rule exI[where x="ps''"]) apply(rule exI[where x="m'"])
      apply(rule exI[where x="e - n"])
      apply(rule exI[where x="e'"])
      proof (safe)
        show "(C, ps) \<Rightarrow>\<^sub>A m' \<Down> ps' + ps''" by fact 
      next
        show "ps' ## ps''" by fact
      next
        have "k * N = k * ( (N + n)- n)" by auto
        also have "\<dots> = k*(N + n) - k*n"  using right_diff_distrib' by blast 
        also have "\<dots> = (k * e + e' + m') - k*n" using m' by auto
        also have "\<dots> = k * e - k*n + e' + m'" using en
          by (metis Nat.add_diff_assoc2 ab_semigroup_add_class.add_ac(1) distrib_left le_add1 le_add_diff_inverse)
        also have "\<dots> = k * (e-n) + e' + m'" by (simp add: diff_mult_distrib2)   
        finally show "k * N = k * (e - n) + e' + m'" .
      next
        show "Q (ps', e - n)" by fact
      qed     
    qed
  done
qed
  
    
    
    
thm hoareT_sound2_part E_extendsR
  
lemma hoareT_sound2_partR: "\<turnstile>\<^sub>3\<^sub>a {P} c { Q} \<Longrightarrow> \<Turnstile>\<^sub>3\<^sub>' {P} c {Q}"
  using hoareT_sound2_part E_extendsR by blast
    

subsubsection \<open>nice example\<close>
  
lemma Frame_R:  assumes "\<turnstile>\<^sub>3\<^sub>' { P } C { Q  }" "Frame P' P F"
             shows "\<turnstile>\<^sub>3\<^sub>' { P' } C { Q ** F } "  
  apply(rule conseq[where k=1]) apply(rule Frame) apply(rule assms(1))
      using assms(2) unfolding Frame_def by auto
  
lemma strengthen_post: assumes "\<turnstile>\<^sub>3\<^sub>' {P}c{Q}" "\<And>s. Q s \<Longrightarrow> Q' s"
  shows "\<turnstile>\<^sub>3\<^sub>' {P}c{ Q'}"
  apply(rule conseq[where k=1])
    apply (rule assms(1))
    apply simp apply simp apply fact apply simp done
           
lemmas strongAssign = Assign''''[OF _ strengthen_post, OF _ Frame_R, OF _ Assign''']   
  
        
lemma weakenpre:  "\<lbrakk> \<turnstile>\<^sub>3\<^sub>' {P}c{Q} ; \<And>s. P' s \<Longrightarrow> P s  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>3\<^sub>' {P'}c{ Q}"
  using conseq[where k=1] by auto
    
lemma weakenpreR:  "\<lbrakk> \<turnstile>\<^sub>3\<^sub>a {P}c{Q} ; \<And>s. P' s \<Longrightarrow> P s  \<rbrakk> \<Longrightarrow>
           \<turnstile>\<^sub>3\<^sub>a {P'}c{ Q}"
  using hoare3a.conseqS by auto
   
    
subsection "Completeness"
    
    
definition wp3' :: "com \<Rightarrow> assn2 \<Rightarrow> assn2" ("wp\<^sub>3\<^sub>'") where 
"wp\<^sub>3\<^sub>' c Q  =  (\<lambda>(s,n). \<exists>t m. n\<ge>m \<and> (c,s) \<Rightarrow>\<^sub>A m \<Down> t \<and> Q (t,n-m))" 
    
lemma wp3Skip[simp]: "wp\<^sub>3\<^sub>' SKIP Q = (Q ** $1)"
  apply (auto intro!: ext simp: wp3'_def) 
    unfolding sep_conj_def dollar_def sep_disj_prod_def sep_disj_nat_def apply auto apply force
    subgoal for t n apply(rule exI[where x=t])  apply(rule exI[where x="Suc 0"])
      using big_step_t_part.Skip by auto
    done
 
lemma wp3Assign[simp]: "wp\<^sub>3\<^sub>' (x ::= e) Q = ((\<lambda>(ps,t). vars e \<union> {x} \<subseteq> dom ps \<and> Q (ps(x \<mapsto> paval e ps),t)) ** $1)"
  apply (auto intro!: ext simp: wp3'_def )  
  unfolding sep_conj_def apply (auto simp: sep_disj_prod_def sep_disj_nat_def dollar_def) apply force
    by fastforce  

lemma wpt_Seq[simp]: "wp\<^sub>3\<^sub>' (c\<^sub>1;;c\<^sub>2) Q = wp\<^sub>3\<^sub>' c\<^sub>1 (wp\<^sub>3\<^sub>' c\<^sub>2 Q)"
  apply (auto simp: wp3'_def fun_eq_iff ) 
  subgoal for a b t m1 s2 m2  
      apply(rule exI[where x="s2"])
      apply(rule exI[where x="m1"])
        apply simp
      apply(rule exI[where x="t"])
      apply(rule exI[where x="m2"])
      apply simp done
  subgoal for s m t' m1 t m2
      apply(rule exI[where x="t"])
      apply(rule exI[where x="m1+m2"])
    apply (auto simp: big_step_t_part.Seq) done
      done

lemma wp3If[simp]:
 "wp\<^sub>3\<^sub>' (IF b THEN c\<^sub>1 ELSE c\<^sub>2) Q = ((\<lambda>(ps,t). vars b \<subseteq> dom ps \<and> wp\<^sub>3\<^sub>' (if pbval b ps then c\<^sub>1 else c\<^sub>2) Q (ps,t)) ** $1)"
  apply (auto simp: wp3'_def fun_eq_iff)
  unfolding sep_conj_def apply (auto simp: sep_disj_prod_def sep_disj_nat_def dollar_def)    
  subgoal for a ba t x apply(rule exI[where x="ba - 1"]) apply auto  
    apply(rule exI[where x=t]) apply(rule exI[where x=x]) apply auto done
  subgoal for a ba t x apply(rule exI[where x="ba - 1"]) apply auto 
    apply(rule exI[where x=t]) apply(rule exI[where x=x]) apply auto done
  subgoal for a ba t m
    apply(rule exI[where x=t]) apply(rule exI[where x="Suc m"]) apply auto
    apply(cases "pbval b a")
    subgoal apply simp apply(subst big_step_t_part.IfTrue) using big_step_t3_post_dom_conv by auto 
    subgoal apply simp apply(subst big_step_t_part.IfFalse) using big_step_t3_post_dom_conv by auto  
  done
  done 
             
    
lemma sFTrue: assumes "pbval b ps" "vars b \<subseteq> dom ps"
  shows "wp\<^sub>3\<^sub>' (WHILE b DO c) Q (ps, n) = ((\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then wp\<^sub>3\<^sub>' c (wp\<^sub>3\<^sub>' (WHILE b DO c) Q) (ps, n) else Q (ps, n))) \<and>* $ 1) (ps, n)"
    (is "?wp = (?I \<and>* $ 1) _")
proof 
  assume "wp\<^sub>3\<^sub>' (WHILE b DO c) Q (ps, n)"
  from this[unfolded wp3'_def] obtain ps'' tt where tn: "tt \<le> n" and w1: "(WHILE b DO c, ps) \<Rightarrow>\<^sub>A tt \<Down> ps''" and Q: "Q (ps'', n - tt) " by blast      
  with assms obtain t t' ps' where w2: "(WHILE b DO c, ps') \<Rightarrow>\<^sub>A t' \<Down> ps''" and c: "(c, ps) \<Rightarrow>\<^sub>A t \<Down> ps'" and tt: "tt=1+t+t'" by auto
  
  from tn obtain k where n: "n=tt+k"
    using le_Suc_ex by blast  
      
  from assms show "(?I \<and>* $ 1) (ps,n)"
    unfolding sep_conj_def dollar_def  wp3'_def  apply auto
    apply(rule exI[where x="t+t'+k"])
      apply safe subgoal using n tt by auto
      apply(rule exI[where x="ps'"])
    apply(rule exI[where x="t"])
    using c apply auto
      apply(rule exI[where x="ps''"])
    apply(rule exI[where x="t'"])
    using w2 Q n by auto
next
  assume "(?I \<and>* $ 1) (ps,n)"
  with assms have Q: "wp\<^sub>3\<^sub>' c (wp\<^sub>3\<^sub>' (WHILE b DO c) Q) (ps, n-1)" and n: "n\<ge>1" unfolding dollar_def sep_conj_def by auto
  then obtain t ps' t' ps'' where t: "t \<le> n - 1"  
        and c: "(c, ps) \<Rightarrow>\<^sub>A t \<Down> ps'" and  t': "t' \<le> (n-1) - t" and w: "(WHILE b DO c, ps') \<Rightarrow>\<^sub>A t' \<Down> ps''" 
        and Q: "Q (ps'', ((n-1) - t) - t')"
    unfolding wp3'_def by auto
  show "?wp" unfolding wp3'_def
    apply simp apply(rule exI[where x="ps''"]) apply(rule exI[where x="1+t+t'"])
    apply safe
    subgoal using t t' n by simp
    subgoal using c w assms by auto
    subgoal using Q t t' n by simp
    done      
qed

lemma sFFalse: assumes "~ pbval b ps" "vars b \<subseteq> dom ps"
  shows "wp\<^sub>3\<^sub>' (WHILE b DO c) Q (ps, n) = ((\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then wp\<^sub>3\<^sub>' c (wp\<^sub>3\<^sub>' (WHILE b DO c) Q) (ps, n) else Q (ps, n))) \<and>* $ 1) (ps, n)"
    (is "?wp = (?I \<and>* $ 1) _")
proof 
  assume "wp\<^sub>3\<^sub>' (WHILE b DO c) Q (ps, n)"
  from this[unfolded wp3'_def] obtain ps' t where tn: "t \<le> n" and w1: "(WHILE b DO c, ps) \<Rightarrow>\<^sub>A t \<Down> ps'" and Q: "Q (ps', n - t) " by blast      
  from assms have w2: "(WHILE b DO c, ps) \<Rightarrow>\<^sub>A 1 \<Down> ps" by auto
  from w1 w2 big_step_t_determ2 have t1: "t=1" and pps: "ps=ps'" by auto
  from assms show "(?I \<and>* $ 1) (ps,n)"
    unfolding sep_conj_def dollar_def using t1 tn Q pps apply auto  apply(rule exI[where x="n-1"]) by auto
next
  assume "(?I \<and>* $ 1) (ps,n)"
  with assms have Q: "Q(ps,n-1)" "n\<ge>1" unfolding dollar_def sep_conj_def by auto
  from assms have w2: "(WHILE b DO c, ps) \<Rightarrow>\<^sub>A 1 \<Down> ps" by auto   
  show "?wp" unfolding wp3'_def
    apply auto   apply(rule exI[where x=ps]) apply(rule exI[where x=1])
      using Q w2 by auto  
qed

lemma sF': "wp\<^sub>3\<^sub>' (WHILE b DO c) Q (ps,n) = ((\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then wp\<^sub>3\<^sub>' c (wp\<^sub>3\<^sub>' (WHILE b DO c) Q) (ps, n) else Q (ps, n))) \<and>* $ 1) (ps,n)"   
  apply(cases "vars b \<subseteq> dom ps")
  subgoal apply(cases "pbval b ps") using sFTrue sFFalse by auto
  subgoal   by (auto simp add: dollar_def wp3'_def sep_conj_def) 
      done
    
lemma sF: "wp\<^sub>3\<^sub>' (WHILE b DO c) Q s = ((\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then wp\<^sub>3\<^sub>' c (wp\<^sub>3\<^sub>' (WHILE b DO c) Q) (ps, n) else Q (ps, n))) \<and>* $ 1) s"   
 using sF'
  by (metis (mono_tags, lifting) prod.case_eq_if prod.collapse sep_conj_impl1) 
    
    
    
lemma strengthen_postR: assumes "\<turnstile>\<^sub>3\<^sub>a {P}c{Q}" "\<And>s. Q s \<Longrightarrow> Q' s"
  shows "\<turnstile>\<^sub>3\<^sub>a {P}c{ Q'}"
  apply(rule hoare3a.conseqS)
    apply (rule assms(1))
    apply simp by (fact assms(2))  
    
lemma assumes "\<And>Q. \<turnstile>\<^sub>3\<^sub>a {wp\<^sub>3\<^sub>' c Q} c {Q}"
  shows WhileWpisPre: "\<turnstile>\<^sub>3\<^sub>a {wp\<^sub>3\<^sub>' (WHILE b DO c) Q} WHILE b DO c { Q}"
proof - 
  define I where  "I \<equiv> (\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> (if pbval b ps then wp\<^sub>3\<^sub>' c (wp\<^sub>3\<^sub>' (WHILE b DO c) Q) (ps, n) else Q (ps, n)))"
  define I' where  "I' \<equiv> (\<lambda>(ps, n). (if pbval b ps then wp\<^sub>3\<^sub>' c (wp\<^sub>3\<^sub>' (WHILE b DO c) Q) (ps, n) else Q (ps, n)))"
  have I': "I = (\<lambda>(ps, n). vars b \<subseteq> dom ps \<and> I' (ps, n))" unfolding I_def I'_def by auto
   
  from assms[where Q="(wp\<^sub>3\<^sub>' (WHILE b DO c) Q)"] have 
    c: "\<turnstile>\<^sub>3\<^sub>a {wp\<^sub>3\<^sub>' c (wp\<^sub>3\<^sub>' (WHILE b DO c) Q)} c {(wp\<^sub>3\<^sub>' (WHILE b DO c) Q)}" .
  have c': "\<turnstile>\<^sub>3\<^sub>a { (\<lambda>(s,n). I (s,n) \<and> lmaps_to_axpr b True s) } c { I  ** $1 }"
    apply(rule hoare3a.conseqS)             
      apply(rule c)              
    subgoal apply auto unfolding I_def by auto            
    subgoal  unfolding I_def   using sF by auto 
    done
      
  have c'': "\<turnstile>\<^sub>3\<^sub>a { (\<lambda>(s,n). I (s,n) \<and> lmaps_to_axpr b True s) } c { (\<lambda>(s, n). I (s, n) \<and> vars b \<subseteq> dom s)  ** $1 }"
    apply(rule strengthen_postR[OF c'])
      unfolding I'
      by (smt R case_prod_beta prod.sel(1) prod.sel(2))  
   
    have ka: "(\<lambda>(s, n). I (s, n) \<and> vars b \<subseteq> dom s) = I"
      apply rule unfolding I' by auto
        
  from hoare3a.While[where P="I"] c'' have
    w: "\<turnstile>\<^sub>3\<^sub>a { (\<lambda>(s,n). I (s,n) \<and>  vars b \<subseteq> dom s) ** $1 } WHILE b DO c {  \<lambda>(s,n). I (s,n) \<and> lmaps_to_axpr b False s }" .
        
  show "\<turnstile>\<^sub>3\<^sub>a {wp\<^sub>3\<^sub>' (WHILE b DO c) Q} WHILE b DO c { Q}"       
      apply(rule hoare3a.conseqS)      
      apply(rule w)           
    subgoal unfolding ka using sF I_def by simp  
    subgoal unfolding I_def by auto 
    done
qed
     

lemma wpT_is_pre: "\<turnstile>\<^sub>3\<^sub>a {wp\<^sub>3\<^sub>' c Q} c { Q}"
proof (induction c arbitrary: Q)
  case SKIP
  then show ?case apply auto 
    using hoare3a.Frame[where F=Q and Q="$0" and P="$1", OF hoare3a.Skip]
      by (auto simp: sep.add_ac) 
next
  case (Assign x1 x2) 
  then show ?case using hoare3a.Assign4 by simp 
next               
  case (Seq c1 c2)
  then show ?case apply auto
    apply(subst hoare3a.Seq[rotated]) by auto
next
  case (If x1 c1 c2)
  then show ?case apply auto 
    apply(rule weakenpreR[OF hoare3a.If, where P1="%(ps,n). wp\<^sub>3\<^sub>' (if pbval x1 ps then c1 else c2) Q (ps,n)"])
      apply auto
    subgoal apply(rule hoare3a.conseqS[where P="wp\<^sub>3\<^sub>' c1 Q" and Q=Q]) by auto 
    subgoal apply(rule hoare3a.conseqS[where P="wp\<^sub>3\<^sub>' c2 Q" and Q=Q]) by auto 
  proof -
    fix a b
    assume "((\<lambda>(ps, t). vars x1 \<subseteq> dom ps \<and> wp\<^sub>3\<^sub>' (if pbval x1 ps then c1 else c2) Q (ps, t)) \<and>* $ (Suc 0)) (a, b)"
    then show "((\<lambda>(ps, t). wp\<^sub>3\<^sub>' (if pbval x1 ps then c1 else c2) Q (ps, t) \<and> vars x1 \<subseteq> dom ps) \<and>* $ (Suc 0)) (a, b)"
       unfolding sep_conj_def apply auto apply(case_tac "pbval x1 aa") apply auto done (* strange! *)
  qed 
next
  case (While b c)
  with WhileWpisPre show ?case .
qed  
   
lemma hoare3o_valid_alt: "\<Turnstile>\<^sub>3\<^sub>' { P } c { Q }  \<Longrightarrow>
    (\<exists> k>0. (\<forall>ps n. P (ps,n div k)
 \<longrightarrow> (\<exists>ps' ps'' m e e'. ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'') 
     \<and> ps' ## ps'' \<and> n = e + e' + m
     \<and> Q (ps',e div k))))"  
proof -
  assume "\<Turnstile>\<^sub>3\<^sub>' {P} c { Q}"
  from this[unfolded hoare3o_valid_def] obtain k where k0: "k>0" and 
     P: "\<And>ps n. P (ps, n) \<Longrightarrow> (\<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * n = k * e + e' + m \<and> Q (ps', e)) "
    by blast
  show ?thesis apply(rule exI[where x=k])
      apply safe apply fact
  proof -
    fix ps n
    assume "P (ps, n div k)"
    with P obtain ps' ps'' m e e' where 1: "(c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps''" "ps' ## ps''" and e: "k * (n div k) = k * e + e' + m" and Q: "Q (ps', e)"
      by blast
    have "k * (n div k) \<le> n" using k0
      by simp  
    then obtain e'' where "n = k * (n div k) + e''" using le_Suc_ex by blast
    also have "\<dots> = k * e + e' + e'' + m" using e   by auto 
    finally have "n = k * e + (e'+e'') + m"  and "Q (ps', (k*e) div k)" using Q k0 by auto
    with 1     
     show " \<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> n = e + e' + m \<and> Q (ps', e div k)" by blast
  qed
qed         
              
  
lemma valid_alternative_with_GC: assumes "(\<forall>ps n. P (ps,n)
 \<longrightarrow> (\<exists>ps' ps'' m e e'. ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'') 
     \<and> ps' ## ps'' \<and> n = e + e' + m
     \<and> Q (ps',e))) " shows "(\<forall>ps n. P (ps,n)    
 \<longrightarrow> (\<exists>ps'  m e . ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps'  ) 
      \<and> n = e + m \<and> (Q ** sep_true) (ps',e)))" 
proof safe
  fix ps n
  assume P: "P (ps,n)"
  with assms obtain ps' ps'' m e e' where c: "(c,ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps''" and
     ps: "ps' ## ps''" and n: "n = e + e' + m" and Q: "Q (ps',e)" by blast
  show "\<exists>ps' m e. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<and> n = e + m \<and> (Q \<and>* (\<lambda>s. True)) (ps', e)"
    apply(rule exI[where x="ps' + ps''"])
    apply(rule exI[where x=m])
    apply(rule exI[where x="e+e'"])
    apply safe apply fact apply fact
      unfolding sep_conj_def apply simp apply(rule exI[where x=ps']) apply(rule exI[where x=e])
      apply(rule exI[where x=ps'']) apply safe apply fact apply(rule exI[where x=e']) apply simp
      apply fact done
  qed
     
    
lemma hoare3o_valid_GC: "\<Turnstile>\<^sub>3\<^sub>' {P} c { Q } \<Longrightarrow> \<Turnstile>\<^sub>3\<^sub>' {P} c { Q ** sep_true}"
proof -
  assume "\<Turnstile>\<^sub>3\<^sub>' {P} c { Q }" 
  then obtain k where "k>0" and P: "\<And>ps n. P (ps, n) \<Longrightarrow> (\<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * n = k * e + e' + m \<and> Q (ps', e))"
    unfolding hoare3o_valid_def by blast
  show "\<Turnstile>\<^sub>3\<^sub>' {P} c { Q ** sep_true}" unfolding hoare3o_valid_def
    apply(rule exI[where x=k])
    apply safe apply fact
  proof -
    fix ps n
    assume "P (ps, n)"
    with P obtain ps' ps'' m e e' where "(c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps''"" ps' ## ps'' "" k * n = k * e + e' + m " and Q: " Q (ps', e)"
      by blast

    show "\<exists>ps' ps'' m e e'. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'' \<and> ps' ## ps'' \<and> k * n = k * e + e' + m \<and> (Q \<and>* (\<lambda>s. True)) (ps', e)"    
      apply(rule exI[where x=ps'])
      apply(rule exI[where x=ps''])
      apply(rule exI[where x=m])
      apply(rule exI[where x=e])
      apply(rule exI[where x=e'])
      apply safe apply fact+ unfolding sep_conj_def apply(rule exI[where x="(ps', e)"])  apply(rule exI[where x="0"]) using Q by simp
  qed
qed
  
lemma hoare3a_sound_GC: "\<turnstile>\<^sub>3\<^sub>a {P} c { Q} \<Longrightarrow> \<Turnstile>\<^sub>3\<^sub>' {P} c { Q ** sep_true}" using hoare3o_valid_GC hoareT_sound2_partR by auto  
  
lemma valid_wp: "\<Turnstile>\<^sub>3\<^sub>' {P} c { Q} \<Longrightarrow> (\<exists>k>0. \<forall>s n. P (s, n) \<longrightarrow> wp\<^sub>3\<^sub>' c (\<lambda>(ps, n). (Q ** sep_true) (ps, n div k)) (s, k * n))"
proof -
  let ?P = "\<lambda>k (ps,n). P (ps,n div k)"
  let ?Q = "\<lambda>k (ps,n). Q (ps,n div k)"
  let ?QG = "\<lambda>k (ps,n). (Q ** sep_true) (ps,n div k)"
  assume "\<Turnstile>\<^sub>3\<^sub>' {P} c { Q}" 
  then obtain k where k[simp]: "k>0" and "(\<forall>ps n. P (ps,n div k)
 \<longrightarrow> (\<exists>ps' ps'' m e e'. ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'') 
     \<and> ps' ## ps'' \<and> n = e + e' + m
     \<and> Q (ps',e div k)))" using hoare3o_valid_alt by blast  
  then have "(\<forall>ps n. ?P k (ps,n)
 \<longrightarrow> (\<exists>ps' ps'' m e e'. ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps' + ps'') 
     \<and> ps' ## ps'' \<and> n = e + e' + m
     \<and> ?Q k (ps',e)))" by auto
  then have f: "(\<forall>ps n. ?P k (ps,n) \<longrightarrow> (\<exists>ps'  m e . ((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps'  ) 
      \<and> n = e + m \<and> (?Q k ** sep_true) (ps',e)))"
    apply(rule valid_alternative_with_GC) done
  
      
  have "\<And>s n. P (s, n) \<Longrightarrow> wp\<^sub>3\<^sub>' c (\<lambda>(ps, n). (Q ** sep_true) (ps, n div k)) (s, k * n)" 
    unfolding wp3'_def apply auto
  proof -
    fix ps n
    assume "P (ps,n)"
    then have "P (ps,(k*n) div k)" apply simp done
    with f obtain ps' m e where "((c,ps) \<Rightarrow>\<^sub>A m \<Down> ps'  )" and z: "k * n = e + m"
        and Q: "(?Q k ** sep_true) (ps',e)" by blast
    from z have e: "e = k * n -m " by auto
    from Q[unfolded e sep_conj_def] obtain ps1 ps2 e1 e2 where
      "ps1 ## ps2" "(ps' = ps1 +ps2)" and eq: "k * n - m = e1 +  e2" and Q: "Q (ps1, e1 div k)" by force

    let ?f = "(e1 + e2) div k - (e1 div k + (e2 div k))"
    have kl: "(e1 + e2) div k \<ge> (e1 div k + (e2 div k))" using k
      using div_add1_eq le_iff_add by blast                        
    show "\<exists>t m. m \<le> k * n \<and> (c, ps) \<Rightarrow>\<^sub>A m \<Down> t \<and> (Q \<and>* (\<lambda>s. True)) (t, (k * n - m) div k)"   
      apply(rule exI[where x=ps'])  
      apply(rule exI[where x=m]) apply safe using z apply simp
       apply fact unfolding e unfolding sep_conj_def 
        apply(rule exI[where x="(ps1,e1 div k)"])
      apply(rule exI[where x="(ps2,e2 div k+?f)"]) apply auto apply fact+
      unfolding eq using kl 
      apply force using Q by auto
  qed 
  then show "(\<exists>k>0. \<forall>s n. P (s, n) \<longrightarrow> wp\<^sub>3\<^sub>' c (\<lambda>(ps, n). (Q ** sep_true) (ps, n div k)) (s, k * n))"
    using k by metis
qed
    
    
theorem completeness: "\<Turnstile>\<^sub>3\<^sub>' {P} c { Q} \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>b {P} c { Q ** sep_true}"
proof -
  let ?P = "\<lambda>k (ps,n). P (ps,n div k)"
  let ?Q = "\<lambda>k (ps,n). Q (ps,n div k)"
  let ?QG = "\<lambda>k (ps,n). (Q ** sep_true) (ps,n div k)"
  assume "\<Turnstile>\<^sub>3\<^sub>' {P} c { Q}" 
  then obtain k where k[simp]: "k>0" and P: "\<And>s n. P (s, n) \<Longrightarrow> wp\<^sub>3\<^sub>' c (\<lambda>(ps, n). (Q ** sep_true) (ps, n div k)) (s, k * n)" 
    using valid_wp by blast 
      
  from wpT_is_pre  have R: "\<turnstile>\<^sub>3\<^sub>a {wp\<^sub>3\<^sub>' c (?QG k)} c {?QG k}" by auto
  
  show "\<turnstile>\<^sub>3\<^sub>b {P} c { Q ** sep_true}" 
    apply(rule hoare3b.conseq[OF hoare3b.import[OF R], where k=k])
    subgoal for s n  by (fact P) 
        apply simp by (fact k)
qed
  
  
thm E_extendsR completeness
  
lemma completenessR: "\<Turnstile>\<^sub>3\<^sub>' {P} c { Q} \<Longrightarrow> \<turnstile>\<^sub>3\<^sub>' {P} c { Q ** sep_true}"  
  using E_extendsS completeness by metis


end
