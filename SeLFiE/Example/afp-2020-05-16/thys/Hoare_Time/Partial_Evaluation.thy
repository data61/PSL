section "Partial States"

subsection \<open>Partial evaluation of expressions\<close>    
theory Partial_Evaluation
imports AExp Vars
begin

                      
type_synonym partstate = "(vname \<Rightarrow> val option)"

definition emb :: "partstate \<Rightarrow> state \<Rightarrow> state" where
   "emb ps s = (%v. (case (ps v) of (Some r) \<Rightarrow> r | None \<Rightarrow> s v))"
    
definition part :: "state \<Rightarrow> partstate" where
   "part s = (%v. Some (s v))"
   
lemma emb_part[simp]: "emb (part s) q = s" unfolding emb_def part_def by auto
    
lemma part_emb[simp]: "dom ps = UNIV \<Longrightarrow> part (emb ps q) = ps" unfolding emb_def part_def apply(rule ext)
  by (simp add: domD option.case_eq_if) 
      
   
lemma dom_part[simp]: "dom (part s) = UNIV" unfolding part_def by auto
    
abbreviation optplus :: "int option \<Rightarrow> int option \<Rightarrow> int option"   where "optplus a b \<equiv> (case a of None \<Rightarrow> None | Some a' \<Rightarrow> (case b of None \<Rightarrow> None | Some b' \<Rightarrow> Some (a' + b'))) "
abbreviation opttimes :: "int option \<Rightarrow> int option \<Rightarrow> int option"   where "opttimes a b \<equiv> (case a of None \<Rightarrow> None | Some a' \<Rightarrow> (case b of None \<Rightarrow> None | Some b' \<Rightarrow> Some (a' * b'))) "
abbreviation optdiv :: "int option \<Rightarrow> int option \<Rightarrow> int option"   where "optdiv a b \<equiv> (case a of None \<Rightarrow> None | Some a' \<Rightarrow> (case b of None \<Rightarrow> None | Some b' \<Rightarrow> Some (a' div b'))) "
                                            
fun paval' :: "aexp \<Rightarrow> partstate \<Rightarrow> val option" where
"paval' (N n) s = Some n" |
"paval' (V x) s = s x" |
"paval' (Plus a\<^sub>1 a\<^sub>2) s = optplus (paval' a\<^sub>1 s)   (paval' a\<^sub>2 s)" |
"paval' (Times a\<^sub>1 a\<^sub>2) s = opttimes (paval' a\<^sub>1 s)   (paval' a\<^sub>2 s)" |
"paval' (Div a\<^sub>1 a\<^sub>2) s = optdiv (paval' a\<^sub>1 s)   (paval' a\<^sub>2 s)"
  

lemma "paval' a ps = Some v \<Longrightarrow> vars a \<subseteq> dom ps"
proof(induct a arbitrary: v) 
  case (Plus a1 a2)
  from Plus(3) obtain v1 where 1: "paval' a1 ps = Some v1" 
    by fastforce
  with Plus(3) obtain v2 where 2: "paval' a2 ps = Some v2"
    by fastforce
  from Plus(1)[OF 1] Plus(2)[OF 2] show ?case by auto 
next
  case (Times a1 a2)
  from Times(3) obtain v1 where 1: "paval' a1 ps = Some v1" 
    by fastforce
  with Times(3) obtain v2 where 2: "paval' a2 ps = Some v2"
    by fastforce
  from Times(1)[OF 1] Times(2)[OF 2] show ?case by auto 
next
  case (Div a1 a2)
  from Div(3) obtain v1 where 1: "paval' a1 ps = Some v1" 
    by fastforce
  with Div(3) obtain v2 where 2: "paval' a2 ps = Some v2"
    by fastforce
  from Div(1)[OF 1] Div(2)[OF 2] show ?case by auto 
qed  (simp_all, blast)

lemma paval'_aval: "paval' a ps = Some v \<Longrightarrow> aval a (emb ps s) = v"
proof(induct a arbitrary: v) 
  case (Plus a1 a2)
  from Plus(3) obtain v1 where 1: "paval' a1 ps = Some v1" 
    by fastforce
  with Plus(3) obtain v2 where 2: "paval' a2 ps = Some v2"
    by fastforce
  from Plus(1)[OF 1] Plus(2)[OF 2] Plus(3) 1 2 show ?case by auto
next
  case (Times a1 a2)
  from Times(3) obtain v1 where 1: "paval' a1 ps = Some v1" 
    by fastforce
  with Times(3) obtain v2 where 2: "paval' a2 ps = Some v2"
    by fastforce
  from Times(1)[OF 1] Times(2)[OF 2] Times(3) 1 2 show ?case by auto 
next  
  case (Div a1 a2)
  from Div(3) obtain v1 where 1: "paval' a1 ps = Some v1" 
    by fastforce
  with Div(3) obtain v2 where 2: "paval' a2 ps = Some v2"
    by fastforce
  from Div(1)[OF 1] Div(2)[OF 2] Div(3) 1 2 show ?case by auto 
qed (simp_all add: emb_def)
  
  
fun paval :: "aexp \<Rightarrow> partstate \<Rightarrow> val" where
"paval (N n) s = n" |
"paval (V x) s = the (s x)" |
"paval (Plus a\<^sub>1 a\<^sub>2) s = paval a\<^sub>1 s + paval a\<^sub>2 s" |
"paval (Times a\<^sub>1 a\<^sub>2) s = paval a\<^sub>1 s * paval a\<^sub>2 s" |
"paval (Div a\<^sub>1 a\<^sub>2) s = paval a\<^sub>1 s div paval a\<^sub>2 s"
  
lemma paval_aval: "vars a \<subseteq> dom ps \<Longrightarrow> paval a ps = aval a (\<lambda>v. case ps v of None \<Rightarrow> s v | Some r \<Rightarrow> r)"
  by (induct a, auto)

lemma paval'_paval: "vars a \<subseteq> dom ps \<Longrightarrow> paval' a ps = Some (paval a ps)"
  by (induct a, auto)

lemma paval_paval': "paval' a ps = Some v \<Longrightarrow> paval a ps = v"
proof(induct a arbitrary: v) 
  case (Plus a1 a2)
  from Plus(3) obtain v1 where 1: "paval' a1 ps = Some v1" 
    by fastforce
  with Plus(3) obtain v2 where 2: "paval' a2 ps = Some v2"
    by fastforce
  from Plus(1)[OF 1] Plus(2)[OF 2] Plus(3) 1 2 show ?case by auto 
next
  case (Times a1 a2)
  from Times(3) obtain v1 where 1: "paval' a1 ps = Some v1" 
    by fastforce
  with Times(3) obtain v2 where 2: "paval' a2 ps = Some v2"
    by fastforce
  from Times(1)[OF 1] Times(2)[OF 2] Times(3) 1 2 show ?case by auto 
next  
  case (Div a1 a2)
  from Div(3) obtain v1 where 1: "paval' a1 ps = Some v1" 
    by fastforce
  with Div(3) obtain v2 where 2: "paval' a2 ps = Some v2"
    by fastforce
  from Div(1)[OF 1] Div(2)[OF 2] Div(3) 1 2 show ?case by auto 
qed simp_all
      
  
fun pbval :: "bexp \<Rightarrow> partstate \<Rightarrow> bool" where
"pbval (Bc v) s = v" |
"pbval (Not b) s = (\<not> pbval b s)" |
"pbval (And b\<^sub>1 b\<^sub>2) s = (pbval b\<^sub>1 s \<and> pbval b\<^sub>2 s)" |
"pbval (Less a\<^sub>1 a\<^sub>2) s = (paval a\<^sub>1 s < paval a\<^sub>2 s)"
  

abbreviation optnot  where "optnot a \<equiv> (case a of None \<Rightarrow> None | Some a' \<Rightarrow> Some (~a'))"
                                            
abbreviation optand  where "optand a b \<equiv> (case a of None \<Rightarrow> None | Some a' \<Rightarrow> (case b of None \<Rightarrow> None | Some b' \<Rightarrow> Some (a' \<and> b'))) "
abbreviation optless   where "optless a b \<equiv> (case a of None \<Rightarrow> None | Some a' \<Rightarrow> (case b of None \<Rightarrow> None | Some b' \<Rightarrow> Some (a' < b'))) "
                                            
fun pbval' :: "bexp \<Rightarrow> partstate \<Rightarrow> bool option" where
"pbval' (Bc v) s = Some v" |
"pbval' (Not b) s = (optnot (pbval' b s))" |
"pbval' (And b\<^sub>1 b\<^sub>2) s = (optand (pbval' b\<^sub>1 s) (pbval' b\<^sub>2 s))" |
"pbval' (Less a\<^sub>1 a\<^sub>2) s = (optless (paval' a\<^sub>1 s) (paval' a\<^sub>2 s))"
  

lemma pbval'_pbval: "vars a \<subseteq> dom ps \<Longrightarrow> pbval' a ps = Some (pbval a ps)"
  apply(induct a) apply (auto simp: paval'_paval) done

lemma paval_aval_vars: "vars a \<subseteq> dom ps \<Longrightarrow> paval a ps = aval a (emb ps s)"
  apply(induct a) by(auto simp: emb_def) 

lemma pbval_bval_vars: "vars b \<subseteq> dom ps \<Longrightarrow> pbval b ps = bval b (emb ps s)"
  apply(induct b) apply (simp_all)
  using paval_aval_vars[where s=s] by auto
        
lemma paval'dom: "paval' a ps = Some v \<Longrightarrow> vars a \<subseteq> dom ps"
proof (induct a arbitrary: v)
  case (Plus a1 a2)   
  then show ?case apply auto
    apply fastforce
    by (metis (no_types, lifting) domD option.case_eq_if option.collapse subset_iff) 
next  
  case (Times a1 a2)   
  then show ?case apply auto
    apply fastforce
    by (metis (no_types, lifting) domD option.case_eq_if option.collapse subset_iff) 
next
  case (Div a1 a2)     
  then show ?case apply auto
    apply fastforce
    by (metis (no_types, lifting) domD option.case_eq_if option.collapse subset_iff) 
qed auto

end