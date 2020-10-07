theory DeBruijn
  imports Syntax
begin
  
subsection\<open>De Bruijn indices\<close>

text\<open>Functions to find the free $\lambda$ and $\mu$ variables in an expression.\<close>

primrec flv_trm :: "trm \<Rightarrow> nat \<Rightarrow> nat set"
    and flv_cmd :: "cmd \<Rightarrow> nat \<Rightarrow> nat set"
where
    "flv_trm (`i) k = (if i\<ge>k then {i-k} else {})"
  | "flv_trm (\<lambda> T : t) k = flv_trm t (k+1)"
  | "flv_trm (s\<degree>t) k = (flv_trm s k) \<union> (flv_trm t k)"
  | "flv_trm (\<mu> T : c) k = flv_cmd c k"
  | "flv_cmd (<i> t) k = flv_trm t k"
    
primrec fmv_trm :: "trm \<Rightarrow> nat \<Rightarrow> nat set"
    and fmv_cmd :: "cmd \<Rightarrow> nat \<Rightarrow> nat set"
where
    "fmv_trm (`i) k = {}"
  | "fmv_trm (\<lambda> T : t) k = fmv_trm t k"
  | "fmv_trm (s\<degree>t) k = (fmv_trm s k) \<union> (fmv_trm t k)"
  | "fmv_trm (\<mu> T : c) k = fmv_cmd c (k+1)"
  | "fmv_cmd (<i> t) k = (if i\<ge>k then {i-k} \<union> (fmv_trm t k) else (fmv_trm t k))"
    
abbreviation lambda_closed :: "_" where
  "lambda_closed t \<equiv> flv_trm t 0 = {}"
  
abbreviation lambda_closedC :: "_" where
  "lambda_closedC c \<equiv> flv_cmd c 0 = {}"
    
text\<open>Free variables in a context.\<close>
  
primrec fmv_ctxt :: "ctxt \<Rightarrow> nat \<Rightarrow> nat set" where
    "fmv_ctxt \<diamond> k = {}"
  | "fmv_ctxt (E \<^sup>\<bullet> t) k = (fmv_ctxt E k) \<union> (fmv_trm t k)"     

text\<open>Shift free $\lambda$ and $\mu$ variables in terms and commands to make substitution capture avoiding.\<close>    
    
primrec
  liftL_trm :: "[trm, nat] \<Rightarrow> trm" and
  liftL_cmd :: "[cmd, nat] \<Rightarrow> cmd"
where
  "liftL_trm (`i) k = (if i<k then `i else `(i+1))" |
  "liftL_trm (\<lambda> T : t) k = \<lambda> T : (liftL_trm t (k+1))" | 
  "liftL_trm (s \<degree> t) k = liftL_trm s k \<degree> liftL_trm t k" |
  "liftL_trm (\<mu> T : c) k = \<mu> T : (liftL_cmd c k)" |
  "liftL_cmd (<i> t) k = <i> (liftL_trm t k)"

primrec
  liftM_trm :: "[trm, nat] \<Rightarrow> trm" and
  liftM_cmd :: "[cmd, nat] \<Rightarrow> cmd"
where
  "liftM_trm (`i) k = `i" |
  "liftM_trm (\<lambda> T : t) k = \<lambda> T : (liftM_trm t k)" |
  "liftM_trm (s \<degree> t) k = liftM_trm s k \<degree> liftM_trm t k" |
  "liftM_trm (\<mu> T : c) k = \<mu> T : (liftM_cmd c (k+1))" |
  "liftM_cmd (<i> t) k =
      (if i<k then (<i> (liftM_trm t k)) else (<i+1> (liftM_trm t k)))"
  
text\<open>Shift free $\lambda$ and $\mu$ variables in contexts to make structural substitution capture avoiding.\<close>
  
primrec liftL_ctxt :: "ctxt \<Rightarrow> nat \<Rightarrow> ctxt" where
  "liftL_ctxt \<diamond> n = \<diamond>" |
  "liftL_ctxt (E \<^sup>\<bullet> t) n = (liftL_ctxt E n) \<^sup>\<bullet> (liftL_trm t n)"

primrec liftM_ctxt :: "ctxt \<Rightarrow> nat \<Rightarrow> ctxt" where
  "liftM_ctxt \<diamond> n = \<diamond>" |
  "liftM_ctxt (E \<^sup>\<bullet> t) n = (liftM_ctxt E n) \<^sup>\<bullet> (liftM_trm t n)"  
  
text\<open>A function to decrement the indices of free $\mu$-variables when a $\mu$ surrounding the
     expression disappears as a result of a reduction\<close>

primrec
  dropM_trm :: "[trm, nat] \<Rightarrow> trm" and
  dropM_cmd :: "[cmd, nat] \<Rightarrow> cmd"
where
    "dropM_trm (`i) k = `i"
  | "dropM_trm (\<lambda> T : t) k = \<lambda> T : (dropM_trm t k)"
  | "dropM_trm (s \<degree> t) k = (dropM_trm s k) \<degree> (dropM_trm t k)"
  | "dropM_trm (\<mu> T : c) k = \<mu> T : (dropM_cmd c (k+1))"
  | "dropM_cmd (<i> t) k = 
      (if i>k then (<i-1> (dropM_trm t k)) else (<i> (dropM_trm t k)))"
    
lemma fmv_liftL: 
  "\<beta> \<notin> fmv_trm t n \<Longrightarrow> \<beta> \<notin> fmv_trm (liftL_trm t m) n"
  "\<beta> \<notin> fmv_cmd c n \<Longrightarrow> \<beta> \<notin> fmv_cmd (liftL_cmd c m) n"
  by(induct t and c arbitrary: m n and m n) auto

lemma fmv_liftL_ctxt:
  "\<beta> \<notin> fmv_ctxt E m \<Longrightarrow> \<beta> \<notin> fmv_ctxt (liftL_ctxt E n) m"
  by(induct E) (fastforce simp add: fmv_liftL)+
    
lemma fmv_suc:
  "\<beta> \<notin> fmv_cmd c (Suc n) \<Longrightarrow> (Suc \<beta>) \<notin> fmv_cmd c n"
  "\<beta> \<notin> fmv_trm t (Suc n) \<Longrightarrow> (Suc \<beta>) \<notin> fmv_trm t n"
proof (induct c and t arbitrary: n and n)
  case (MVar x1 x2)
  then show ?case
    by clarsimp (metis UnI1 UnI2 diff_Suc_1 diff_Suc_eq_diff_pred diff_commute diff_is_0_eq nat.simps(3) not_less_eq_eq singletonI)
qed (force)+

lemma flv_drop:
  "flv_trm t k = {} \<longrightarrow> flv_trm (dropM_trm t j) k = {}"
  "flv_cmd c k = {} \<longrightarrow> flv_cmd (dropM_cmd c j) k = {}"
  by (induct t and c arbitrary: j k and j k) clarsimp+
    
end
