subsection\<open>Logical and structural substitution\<close>
  
theory Substitution
  imports DeBruijn
begin 

primrec
  subst_trm :: "[trm, trm, nat] \<Rightarrow> trm"  ("_[_'/_]\<^sup>T" [300, 0, 0] 300) and
  subst_cmd ::  "[cmd, trm, nat] \<Rightarrow> cmd" ("_[_'/_]\<^sup>C" [300, 0, 0] 300)
where
    subst_LVar: "(`i)[s/k]\<^sup>T = 
          (if k < i then `(i-1) else if k = i then s else (`i))"
    | subst_Lbd: "(\<lambda> T : t)[s/k]\<^sup>T = \<lambda> T : (t[(liftL_trm s 0) / k+1]\<^sup>T)"
    | subst_App: "(t \<degree> u)[s/k]\<^sup>T = t[s/k]\<^sup>T \<degree> u[s/k]\<^sup>T"
    | subst_Mu: "(\<mu> T : c)[s/k]\<^sup>T  = \<mu> T : (c[(liftM_trm s 0) / k]\<^sup>C)"
    | subst_MVar: "(<i> t)[s/k]\<^sup>C = <i> (t[s/k]\<^sup>T)"

text\<open>Substituting a term for the hole in a context.\<close>
  
primrec ctxt_subst :: "ctxt \<Rightarrow> trm \<Rightarrow> trm" where
  "ctxt_subst \<diamond> s = s" |
  "ctxt_subst (E \<^sup>\<bullet> t) s = (ctxt_subst E s)\<degree> t"

lemma ctxt_app_subst:
  shows "ctxt_subst E (ctxt_subst F t) = ctxt_subst (E . F) t"
  by (induction E, auto)
    
text\<open>The structural substitution is based on Geuvers and al.~\cite{DBLP:journals/apal/GeuversKM13}.\<close>

primrec
  struct_subst_trm :: "[trm, nat, nat, ctxt] \<Rightarrow> trm"  ("_[_=_ _]\<^sup>T" [300, 0, 0, 0] 300) and
  struct_subst_cmd ::  "[cmd, nat, nat, ctxt] \<Rightarrow> cmd" ("_[_=_ _]\<^sup>C" [300, 0, 0, 0] 300)
where
  struct_LVar: "(`i)[j=k E]\<^sup>T = (`i)" |
  struct_Lbd: "(\<lambda> T : t)[j=k E]\<^sup>T = (\<lambda> T : (t[j=k (liftL_ctxt E 0)]\<^sup>T))" |
  struct_App: "(t\<degree>s)[j=k E]\<^sup>T = (t[j=k E]\<^sup>T)\<degree>(s[j=k E]\<^sup>T)" |
  struct_Mu: "(\<mu> T : c)[j=k E]\<^sup>T = \<mu> T : (c[(j+1)=(k+1) (liftM_ctxt E 0)]\<^sup>C)" |
  struct_MVar: "(<i> t)[j=k E]\<^sup>C = 
      (if i=j then (<k> (ctxt_subst E (t[j=k E]\<^sup>T))) 
       else (if j<i \<and> i\<le>k then (<i-1> (t[j=k E]\<^sup>T))
             else (if k\<le>i \<and> i<j then (<i+1> (t[j=k E]\<^sup>T))
                   else (<i> (t[j=k E]\<^sup>T)))))"

text\<open>Lifting of lambda and mu variables commute with each other\<close>

lemma liftLM_comm: 
  "liftL_trm (liftM_trm t n) m = liftM_trm (liftL_trm t m) n"
  "liftL_cmd (liftM_cmd c n) m = liftM_cmd (liftL_cmd c m) n"
  by(induct t and c arbitrary: n m and n m) auto

lemma liftLM_comm_ctxt:
  "liftL_ctxt (liftM_ctxt E n) m = liftM_ctxt (liftL_ctxt E m) n"
  by(induct E arbitrary: n m, auto simp add: liftLM_comm)

text\<open>Lifting of $\mu$-variables (almost) commutes.\<close>

lemma liftMM_comm:
  "n\<ge>m \<Longrightarrow> liftM_trm (liftM_trm t n) m = liftM_trm (liftM_trm t m) (Suc n)"
  "n\<ge>m \<Longrightarrow> liftM_cmd (liftM_cmd c n) m = liftM_cmd (liftM_cmd c m) (Suc n)"
  by(induct t and c arbitrary: n m and n m) auto

lemma liftMM_comm_ctxt:
  "liftM_ctxt (liftM_ctxt E n) 0 = liftM_ctxt (liftM_ctxt E 0) (n+1)"
  by(induct E arbitrary: n, auto simp add: liftMM_comm)

text\<open>If a $\mu$ variable $i$ doesn't occur in a term or a context, 
then these remain the same after structural substitution of variable $i$.\<close>

lemma liftM_struct_subst: 
  "liftM_trm t i[i=i F]\<^sup>T = liftM_trm t i"
  "liftM_cmd c i[i=i F]\<^sup>C = liftM_cmd c i"
  by(induct t and c arbitrary: i F and i F) auto

lemma liftM_ctxt_struct_subst:
  "(ctxt_subst (liftM_ctxt E i) t)[i=i F]\<^sup>T = ctxt_subst (liftM_ctxt E i) (t[i=i F]\<^sup>T)"
  by(induct E arbitrary: i t F; force simp add: liftM_struct_subst)

end
