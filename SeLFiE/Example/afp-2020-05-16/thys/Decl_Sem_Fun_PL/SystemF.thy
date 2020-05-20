section "Semantics and type soundness for System F"

theory SystemF
  imports Main "HOL-Library.FSet" 
begin

subsection "Syntax and values"
  
type_synonym name = nat

datatype ty = TVar nat | TNat | Fun ty ty (infix "\<rightarrow>" 60) | Forall ty 

datatype exp = EVar name | ENat nat | ELam ty exp | EApp exp exp
  | EAbs exp  | EInst exp ty | EFix ty exp 

datatype val = VNat nat | Fun "(val \<times> val) fset" | Abs "val option" | Wrong

fun val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where
  "(VNat n) \<sqsubseteq> (VNat n') = (n = n')" |
  "(Fun f) \<sqsubseteq> (Fun f') = (fset f \<subseteq> fset f')" |
  "(Abs None) \<sqsubseteq> (Abs None) = True" |
  "Abs (Some v) \<sqsubseteq> Abs (Some v') = v \<sqsubseteq> v'" |
  "Wrong \<sqsubseteq> Wrong = True" |
  "(v::val) \<sqsubseteq> v' = False"  

subsection "Set monad"

definition set_bind :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" where
  "set_bind m f \<equiv> { v. \<exists> v'. v' \<in> m \<and> v \<in> f v' }"
declare set_bind_def[simp]

syntax "_set_bind" :: "[pttrns,'a set,'b] \<Rightarrow> 'c" ("(_ \<leftarrow> _;//_)" 0)
translations "P \<leftarrow> E; F" \<rightleftharpoons> "CONST set_bind E (\<lambda>P. F)"

definition errset_bind :: "val set \<Rightarrow> (val \<Rightarrow> val set) \<Rightarrow> val set" where
  "errset_bind m f \<equiv> { v. \<exists> v'. v' \<in> m \<and> v' \<noteq> Wrong \<and> v \<in> f v' } \<union> {v. v = Wrong \<and> Wrong \<in> m }"
declare errset_bind_def[simp]

syntax "_errset_bind" :: "[pttrns,val set,val] \<Rightarrow> 'c" ("(_ := _;//_)" 0)
translations "P := E; F" \<rightleftharpoons> "CONST errset_bind E (\<lambda>P. F)"

definition return :: "val \<Rightarrow> val set" where
  "return v \<equiv> {v'. v' \<sqsubseteq> v }"
declare return_def[simp]

subsection "Denotational semantics"

type_synonym tyenv = "(val set) list" 
type_synonym env = "val list"

inductive iterate :: "(env \<Rightarrow> val set) \<Rightarrow> env \<Rightarrow> val \<Rightarrow> bool" where
  iterate_none[intro!]: "iterate Ee \<rho> (Fun {||})" |
  iterate_again[intro!]: "\<lbrakk> iterate Ee \<rho> f; f' \<in> Ee (f#\<rho>) \<rbrakk> \<Longrightarrow> iterate Ee \<rho> f'"

abbreviation apply_fun :: "val set \<Rightarrow> val set \<Rightarrow> val set" where
  "apply_fun V1 V2 \<equiv> (v1 := V1; v2 := V2;
                       case v1 of Fun f \<Rightarrow> 
                          (v2',v3') \<leftarrow> fset f;
                          if v2' \<sqsubseteq> v2 then return v3' else {}
                       | _ \<Rightarrow> return Wrong)"  

fun E :: "exp \<Rightarrow> env \<Rightarrow> val set" where
  Enat: "E (ENat n) \<rho> = return (VNat n)" |
  Evar: "E (EVar n) \<rho> = return (\<rho>!n)" |
  Elam: "E (ELam \<tau> e) \<rho> = {v. \<exists> f. v = Fun f \<and> (\<forall> v1 v2'. (v1,v2') \<in> fset f \<longrightarrow>
      (\<exists> v2. v2 \<in> E e (v1#\<rho>) \<and> v2' \<sqsubseteq> v2)) }" |
  Eapp: "E (EApp e1 e2) \<rho> = apply_fun (E e1 \<rho>) (E e2 \<rho>)" |
  Efix: "E (EFix \<tau> e) \<rho> = { v. iterate (E e) \<rho> v }" | 
  Eabs: "E (EAbs e) \<rho> = {v. (\<exists> v'. v = Abs (Some v') \<and> v' \<in> E e \<rho>) 
                               \<or> (v = Abs None \<and> E e \<rho> = {}) }" | 
  Einst: "E (EInst e \<tau>) \<rho> = 
       (v := E e \<rho>;
        case v of
          Abs None \<Rightarrow> {}
        | Abs (Some v') \<Rightarrow> return v'
        | _ \<Rightarrow> return Wrong)"
  
subsection "Types: substitution and semantics"
  
fun shift :: "nat \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> ty" where
  "shift k c TNat = TNat" |
  "shift k c (TVar n) = (if c \<le> n then TVar (n + k) else TVar n)" |
  "shift k c (\<sigma> \<rightarrow> \<sigma>') = (shift k c \<sigma>) \<rightarrow> (shift k c \<sigma>')" |
  "shift k c (Forall \<sigma>) = Forall (shift k (Suc c) \<sigma>)"

fun subst :: "nat \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty" where
  "subst k \<tau> TNat = TNat" |
  "subst k \<tau> (TVar n) = (if k = n then \<tau>
                         else if k < n then TVar (n - 1) 
                         else TVar n)" |
  "subst k \<tau> (\<sigma> \<rightarrow> \<sigma>') = (subst k \<tau> \<sigma>) \<rightarrow> (subst k \<tau> \<sigma>')" |
  "subst k \<tau> (Forall \<sigma>) = Forall (subst (Suc k) (shift (Suc 0) 0 \<tau>) \<sigma>)"

fun T :: "ty \<Rightarrow> tyenv \<Rightarrow> val set" where
 Tnat: "T TNat \<rho> = {v. \<exists> n. v = VNat n }" |
 Tvar: "T (TVar n) \<rho> = (if n < length \<rho> then
                         {v. \<exists> v'. v'\<in>\<rho>!n \<and> v \<sqsubseteq> v' \<and> v \<noteq> Wrong}
                        else {})" |
 Tfun: "T (\<sigma> \<rightarrow> \<tau>) \<rho> = {v. \<exists> f. v = Fun f \<and> 
                        (\<forall> v1 v2'.(v1,v2')\<in>fset f \<longrightarrow>
                          v1\<in>T \<sigma> \<rho>\<longrightarrow>(\<exists> v2. v2 \<in> T \<tau> \<rho> \<and> v2' \<sqsubseteq> v2))}" |
 Tall: "T (Forall \<tau>) \<rho> = {v. (\<exists>v'. v = Abs (Some v') \<and> (\<forall> V. v' \<in> T \<tau> (V#\<rho>)))
                           \<or> v = Abs None }"

subsection "Type system"
  
type_synonym tyctx = "(ty \<times> nat) list \<times> nat"

definition wf_tyvar :: "tyctx \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_tyvar \<Gamma> n \<equiv> n < snd \<Gamma>"
definition push_ty :: "ty \<Rightarrow> tyctx \<Rightarrow> tyctx" where
  "push_ty \<tau> \<Gamma> \<equiv> ((\<tau>,snd \<Gamma>) # fst \<Gamma>, snd \<Gamma>)"
definition push_tyvar :: "tyctx \<Rightarrow> tyctx" where
  "push_tyvar \<Gamma> \<equiv> (fst \<Gamma>, Suc (snd \<Gamma>))"

definition good_ctx :: "tyctx \<Rightarrow> bool" where
  "good_ctx \<Gamma> \<equiv> \<forall> n. n < length (fst \<Gamma>) \<longrightarrow> snd ((fst \<Gamma>) ! n) \<le> snd \<Gamma>"

definition lookup :: "tyctx \<Rightarrow> nat \<Rightarrow> ty option" where
  "lookup \<Gamma> n \<equiv> (if n < length (fst \<Gamma>) then
                    let k = snd \<Gamma> - snd ((fst \<Gamma>)!n) in
                    Some (shift k 0 (fst ((fst \<Gamma>)!n)))
                  else None)"

inductive well_typed :: "tyctx \<Rightarrow> exp \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _" [55,55,55] 54) where
  wtnat[intro!]: "\<Gamma> \<turnstile> ENat n : TNat" |
  wtvar[intro!]: "\<lbrakk> lookup \<Gamma> n = Some \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> EVar n : \<tau>" |
  wtapp[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e : \<sigma> \<rightarrow> \<tau>; \<Gamma> \<turnstile> e' : \<sigma> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> EApp e e' : \<tau>" |
  wtlam[intro!]: "\<lbrakk> push_ty \<sigma> \<Gamma> \<turnstile> e : \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> ELam \<sigma> e : \<sigma> \<rightarrow> \<tau>" |
  wtfix[intro!]: "\<lbrakk> push_ty (\<sigma>\<rightarrow>\<tau>) \<Gamma> \<turnstile> e : \<sigma>\<rightarrow>\<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> EFix (\<sigma> \<rightarrow> \<tau>) e : \<sigma> \<rightarrow> \<tau>" |
  wtabs[intro!]: "\<lbrakk> push_tyvar \<Gamma> \<turnstile> e : \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> EAbs e : Forall \<tau>" |
  wtinst[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e : Forall \<tau> \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> EInst e \<sigma> : (subst 0 \<sigma> \<tau>)"

inductive wfenv :: "env \<Rightarrow> tyenv \<Rightarrow> tyctx \<Rightarrow> bool" ("\<turnstile> _,_ : _" [55,55,55] 54) where
  wfnil[intro!]: "\<turnstile> [],[] : ([],0)" |
  wfvbind[intro!]: "\<lbrakk> \<turnstile> \<rho>,\<eta> : \<Gamma>; v \<in> T \<tau> \<eta> \<rbrakk> \<Longrightarrow> \<turnstile>  (v#\<rho>),\<eta> : push_ty \<tau> \<Gamma>" |
  wftbind[intro!]: "\<lbrakk> \<turnstile> \<rho>,\<eta> : \<Gamma> \<rbrakk> \<Longrightarrow> \<turnstile> \<rho>, (V#\<eta>) : push_tyvar \<Gamma>"

inductive_cases
  wtnat_inv[elim!]: "\<Gamma> \<turnstile> ENat n : \<tau>" and
  wtvar_inv[elim!]: "\<Gamma> \<turnstile> EVar n : \<tau>" and
  wtapp_inv[elim!]: "\<Gamma> \<turnstile> EApp e e' : \<tau>" and
  wtlam_inv[elim!]: "\<Gamma> \<turnstile> ELam \<sigma> e : \<tau>" and
  wtfix_inv[elim!]: "\<Gamma> \<turnstile> EFix \<sigma> e : \<tau>" and
  wtabs_inv[elim!]: "\<Gamma> \<turnstile> EAbs e : \<tau>" and
  wtinst_inv[elim!]: "\<Gamma> \<turnstile> EInst e \<sigma> : \<tau>"

lemma wfenv_good_ctx: "\<turnstile> \<rho>,\<eta> : \<Gamma> \<Longrightarrow> good_ctx \<Gamma>"
proof (induction rule: wfenv.induct)
  case wfnil
  then show ?case by (force simp: good_ctx_def)
next
  case (wfvbind \<rho> \<eta> \<Gamma> v \<tau>)
  then show ?case 
    apply (simp add: good_ctx_def push_ty_def) apply (cases \<Gamma>) apply simp
    apply clarify apply (rename_tac n) apply (case_tac n) apply force apply force done
next
  case (wftbind \<rho> \<eta> \<Gamma> V)
  then show ?case 
    apply (simp add: good_ctx_def push_tyvar_def) apply (cases \<Gamma>) apply simp
    apply clarify apply (rename_tac n) apply (case_tac n) apply auto done
qed

subsection "Well-typed Programs don't go wrong"

lemma nth_append1[simp]: "n < length \<rho>1 \<Longrightarrow> (\<rho>1@\<rho>2)!n = \<rho>1!n"
proof (induction \<rho>1 arbitrary: \<rho>2 n)
  case Nil
  then show ?case by auto
next
  case (Cons a \<rho>1)
  then show ?case by (cases n) auto
qed

lemma nth_append2[simp]: "n \<ge> length \<rho>1 \<Longrightarrow> (\<rho>1@\<rho>2)!n = \<rho>2!(n - length \<rho>1)"
proof (induction \<rho>1 arbitrary: \<rho>2 n)
  case Nil
  then show ?case by auto
next
  case (Cons a \<rho>1)
  then show ?case by (cases n) auto
qed

lemma shift_append_preserves_T_aux: 
  shows "T \<tau> (\<rho>1@\<rho>3) = T (shift (length \<rho>2) (length \<rho>1) \<tau>) (\<rho>1@\<rho>2@\<rho>3)" 
proof (induction \<tau> arbitrary: \<rho>1 \<rho>2 \<rho>3)
  case (Forall \<tau>)
  then show ?case 
    apply simp
    apply (rule equalityI) apply (rule subsetI) apply (simp only: mem_Collect_eq)
     apply (erule disjE) apply (erule exE) apply (erule conjE) apply (rule disjI1)
      apply (rename_tac x v')
      apply (rule_tac x=v' in exI) apply simp apply clarify 
      apply (rename_tac V)
      apply (erule_tac x=V in allE) 
      apply (subgoal_tac "T \<tau> ((V#\<rho>1) @ \<rho>3) =
       T (shift (length \<rho>2) (length (V#\<rho>1)) \<tau>) ((V#\<rho>1) @ \<rho>2 @ \<rho>3)")
       prefer 2 apply blast apply force 
     apply (rule disjI2) apply force
    apply (rule subsetI) apply (simp only: mem_Collect_eq)
    apply (erule disjE) apply (erule exE) apply (erule conjE) apply (rule disjI1)
     apply (rename_tac x v')
     apply (rule_tac x=v' in exI) apply simp apply clarify 
     apply (rename_tac V)
     apply (erule_tac x=V in allE) 
     apply (subgoal_tac "T \<tau> ((V#\<rho>1) @ \<rho>3) =
       T (shift (length \<rho>2) (length (V#\<rho>1)) \<tau>) ((V#\<rho>1) @ \<rho>2 @ \<rho>3)")
      prefer 2 apply blast apply force 
    apply (rule disjI2) apply force done
qed force+
    
lemma shift_append_preserves_T: shows "T \<tau> \<rho>3 = T (shift (length \<rho>2) 0 \<tau>) (\<rho>2@\<rho>3)"
    using shift_append_preserves_T_aux[of \<tau> "[]" \<rho>3 \<rho>2] by auto

lemma drop_shift_preserves_T: 
  assumes k: "k \<le> length \<rho>" shows "T \<tau> (drop k \<rho>) = T (shift k 0 \<tau>) \<rho>"
proof -
  let ?r2 = "take k \<rho>" and ?r3 = "drop k \<rho>"
  have 1: "T \<tau> (?r3) = T (shift (length ?r2) 0 \<tau>) (?r2@?r3)"
    using shift_append_preserves_T_aux[of \<tau> "[]" ?r3 ?r2] by simp  
  have 2: "?r2@?r3 = \<rho>" by simp
  from k have 3: "length ?r2 = k" by simp 
  from 1 2 3 show ?thesis by simp 
qed

lemma shift_cons_preserves_T: shows "T \<tau> \<rho> = T (shift (Suc 0) 0 \<tau>) (b#\<rho>)"
  using drop_shift_preserves_T[of "Suc 0" "b#\<rho>" \<tau>] by simp 
    
lemma compose_shift: shows "shift (j+k) c \<tau> = shift j c (shift k c \<tau>)"
  by (induction \<tau> arbitrary: j k c) auto
    
lemma shift_zero_id[simp]: "shift 0 c \<tau> = \<tau>"
  by (induction \<tau> arbitrary: c) auto 
    
lemma lookup_wfenv: assumes r_g: "\<turnstile> \<rho>,\<eta> : \<Gamma>" and ln: "lookup \<Gamma> n = Some \<tau>"
  shows "\<exists> v. \<rho>!n = v \<and> v \<in> T \<tau> \<eta>"
  using r_g ln
proof (induction \<rho> \<eta> \<Gamma> arbitrary: n \<tau> rule: wfenv.induct)
  case wfnil
  then show ?case unfolding lookup_def by force
next
  case (wfvbind \<rho> \<eta> \<Gamma> v \<tau>')
  from wfvbind(2) have vtp: "v \<in> T \<tau>' \<eta>" .
  show ?case
  proof (cases n)
    case 0
    from 0 wfvbind(4) have t: "\<tau> =  shift 0 0 \<tau>'" unfolding lookup_def by (simp add: push_ty_def) 
    from 0 vtp t show ?thesis by simp 
  next
    case (Suc n')
    let ?G = "push_ty \<tau>' \<Gamma>" 
    from wfvbind(4) Suc obtain \<sigma> k where gnp: "(fst \<Gamma>)!n' = (\<sigma>,k)" and t: "\<tau> = shift (snd \<Gamma> - k) 0 \<sigma>" 
      and npg: "n' < length (fst \<Gamma>)"
      unfolding lookup_def push_ty_def apply (cases "n' < length (fst \<Gamma>)") apply auto
      apply (cases "fst \<Gamma> ! n'") apply auto done  
    from gnp Suc npg t have ln: "lookup \<Gamma> n' = Some \<tau>" unfolding lookup_def by auto 
    from wfvbind(3) ln obtain v' where rnp: "\<rho>!n' = v'" and vt: "v' \<in> T \<tau> \<eta>" by blast
    from Suc rnp vt show ?thesis by simp  
  qed
next
  case (wftbind \<rho> \<eta> \<Gamma> V)
  let ?a = "fst \<Gamma>" and ?b = "snd \<Gamma>"
  obtain \<sigma> k where s: "\<sigma> = fst (fst \<Gamma> ! n)" and k: "k = snd (fst \<Gamma> ! n)" by auto 
  from wftbind(3) s k have t: "\<tau> = shift (Suc ?b - k) 0 \<sigma>" and nl: "n < length (fst \<Gamma>)"
    unfolding push_tyvar_def lookup_def apply auto 
     apply (case_tac "n < length (fst \<Gamma>)", auto)+ done
  let ?t = "shift (?b - k) 0 (fst (?a ! n))"
  from wftbind(3) k have ln: "lookup \<Gamma> n = Some ?t"
    unfolding push_tyvar_def lookup_def
    apply (cases \<Gamma>) apply (rename_tac k' G) apply simp apply (case_tac "n < length k'") by auto 
  from wftbind(2) ln obtain v' where rn_vp: "\<rho> ! n = v'" and vp_t: "v' \<in> T ?t \<eta>" by blast
  from vp_t have "v' \<in> T (shift (Suc 0) 0 ?t) (V # \<eta>)" using shift_cons_preserves_T by auto 
  hence vp_t2: "v' \<in> T (shift (Suc 0 + (?b - k)) 0 (fst (?a!n))) (V # \<eta>)"
    using compose_shift[of "Suc 0" "?b - k" 0 "fst (?a!n)"] by simp
  from wftbind(1) have "good_ctx \<Gamma>" using wfenv_good_ctx by blast
  from this k nl have "?b \<ge> k" unfolding good_ctx_def by auto
  from this have "Suc 0 + (?b - k) = Suc ?b - k" by simp
  from this vp_t2 have vp_t3: "v' \<in> T (shift (Suc ?b - k) 0 (fst (?a!n))) (V # \<eta>)" by simp
  from rn_vp vp_t3 t s show ?case by auto 
qed

lemma less_wrong[elim!]: "\<lbrakk> v \<sqsubseteq> Wrong; v = Wrong \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (case_tac v) auto

lemma less_nat[elim!]: "\<lbrakk> v \<sqsubseteq> VNat n; v = VNat n \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (case_tac v) auto 
    
lemma less_fun[elim!]: "\<lbrakk> v \<sqsubseteq> Fun f; \<And> f'. \<lbrakk> v = Fun f'; fset f' \<subseteq> fset f \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (case_tac v) auto
    
lemma less_refl[simp]: "v \<sqsubseteq> v"
proof (induction v)
    case (Abs v')
    then show ?case by (cases v') auto
qed force+
  
lemma less_trans: fixes v1::val and v2::val and v3::val
  shows "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3"
proof (induction v2 arbitrary: v1 v3)
  case (VNat n)
  then show ?case by (cases v1) auto 
next
  case (Fun t)
  then show ?case
    apply (cases v1)
       apply force 
      apply simp 
      apply (cases v3)
         apply auto done
next
  case (Abs v)
  then show ?case 
    apply (cases v1) apply force apply force apply (case_tac v3) apply force apply force
      apply (rename_tac v' v3') apply simp apply (cases v) apply (case_tac v')
        apply force apply force 
      apply (case_tac v3') apply force apply simp apply (case_tac v') 
       apply force+ done
next
  case Wrong
  then show ?case by auto
qed
    
lemma T_down_closed: assumes vt: "v \<in> T \<tau> \<eta>" and vp_v: "v' \<sqsubseteq> v"
  shows "v' \<in> T \<tau> \<eta>"
  using vt vp_v
proof (induction \<tau> arbitrary: v v' \<eta>)
  case (TVar x v v' \<eta>)
  then show ?case 
    apply simp apply (case_tac "x < length \<eta>")
     apply simp apply clarify 
     apply (rule_tac x=v' in exI)
     apply simp apply (rule conjI) 
      apply (rule less_trans) apply blast apply blast 
     apply (case_tac v')
        apply (case_tac v)
           apply force+ 
      apply (case_tac v)
         apply force+ done
next
  case TNat
  then show ?case by auto
next
  case (Fun \<tau>1 \<tau>2)
  then show ?case apply simp apply clarify apply (rule_tac x=f' in exI) apply fastforce done
next
  case (Forall \<tau> v v' \<eta>)
  then show ?case 
    apply simp apply (erule disjE) apply clarify apply (cases v') apply force apply force
      apply simp apply (rename_tac v'') apply (case_tac v'') apply simp apply simp apply clarify
      apply (erule_tac x=V in allE) apply blast 
     apply force
    apply simp
    apply (case_tac v') apply auto done
qed
 
lemma wrong_not_in_T: "Wrong \<notin> T \<tau> \<eta>"
  by (induction \<tau>) auto
    
lemma fun_app: assumes vmn: "V \<subseteq> T (m \<rightarrow> n) \<eta>" and v2s: "V' \<subseteq> T m \<eta>" 
  shows "apply_fun V V' \<subseteq> T n \<eta>"
  using vmn v2s apply simp apply (rule conjI)
   prefer 2 apply force 
  apply clarify
  apply (erule disjE)
   prefer 2 using wrong_not_in_T apply blast 
  apply clarify apply (rename_tac v'') apply (case_tac v') apply auto
  apply (rename_tac v1 v2) apply (case_tac "v1 \<sqsubseteq> v''") apply auto 
  apply (subgoal_tac "\<forall>v1 v2'.
                (v1, v2') \<in> fset x2 \<longrightarrow> v1 \<in> T m \<eta> \<longrightarrow> (\<exists>v2. v2 \<in> T n \<eta> \<and> v2' \<sqsubseteq> v2)")
   prefer 2 apply blast 
  apply (rename_tac v1 v2)
  apply (erule_tac x=v1 in allE) apply (erule_tac x=v2 in allE) apply (erule impE) apply simp
  apply (erule impE) using T_down_closed apply blast 
  apply clarify  using T_down_closed apply blast
  done   
    
lemma T_eta: "{v. \<exists>v'. v' \<in> T \<sigma> (\<eta>) \<and> v \<sqsubseteq> v' \<and> v \<noteq> Wrong} = T \<sigma> \<eta>"
  apply auto
   using T_down_closed apply blast
  apply (rename_tac v)
  apply (rule_tac x=v in exI)
  apply simp
  using wrong_not_in_T apply blast done
   
lemma compositionality: "T \<tau> (\<eta>1 @ (T \<sigma> (\<eta>1@\<eta>2)) # \<eta>2) = T (subst (length \<eta>1) \<sigma> \<tau>) (\<eta>1@\<eta>2)"
proof (induction \<tau> arbitrary: \<sigma> \<eta>1 \<eta>2)
  case (TVar x)
  then show ?case 
    apply (case_tac "length \<eta>1 = x") apply simp using T_eta apply blast
    apply (case_tac "length \<eta>1 < x") apply (subgoal_tac "\<exists> x'. x = Suc x'") prefer 2 
      apply (cases x) 
       apply force+
    done
next
  case TNat
  then show ?case by auto
next
  case (Fun \<tau>1 \<tau>2)
  then show ?case by auto
next
  case (Forall \<tau>)
  show "T (Forall \<tau>) (\<eta>1 @ T \<sigma> (\<eta>1 @ \<eta>2) # \<eta>2) =
        T (subst (length \<eta>1) \<sigma> (Forall \<tau>)) (\<eta>1 @ \<eta>2)"
    apply simp
    apply (rule equalityI) apply (rule subsetI) apply (simp only: mem_Collect_eq)
     apply (erule disjE) prefer 2 apply force apply (erule exE) apply (erule conjE) apply (rule disjI1)
     apply (rule_tac x=v' in exI) apply simp apply clarify 
     apply (erule_tac x="V" in allE) 
     prefer 2 apply (rule subsetI) apply (simp only: mem_Collect_eq)
     apply (erule disjE) prefer 2 apply force apply (erule exE) apply (erule conjE) apply (rule disjI1)
     apply (rule_tac x=v' in exI) apply simp apply clarify 
     apply (erule_tac x="V" in allE) 
     defer
  proof -
    fix x v' V
    let ?L1 = "length \<eta>1" and ?R1 = "V#\<eta>1" and ?s = "shift (Suc 0) 0 \<sigma>"
    assume 1: "v' \<in> T \<tau> (V # (\<eta>1 @ T \<sigma> (\<eta>1 @ \<eta>2) # \<eta>2))"
    from 1 have a: "v' \<in> T \<tau> (?R1 @ T \<sigma> (\<eta>1@\<eta>2) # \<eta>2)" by simp
        
    have b: "T \<sigma> (\<eta>1@\<eta>2) = T ?s (V#(\<eta>1@\<eta>2))" by (rule shift_cons_preserves_T)
    from a b have c: "v' \<in> T \<tau> (?R1 @ T ?s (?R1 @ \<eta>2) # \<eta>2)" by simp
    from Forall[of ?R1 ?s \<eta>2] have 2: "T \<tau> (?R1 @ T ?s (?R1 @ \<eta>2) # \<eta>2) =
                                  T (subst (length ?R1) ?s \<tau>) (?R1 @ \<eta>2)" by simp
    from c 2 show "v' \<in> T (subst (Suc ?L1) ?s \<tau>) (V # (\<eta>1 @ \<eta>2))" by simp
  next
    fix x v' V
    let ?L1 = "length \<eta>1" and ?R1 = "V#\<eta>1" and ?s = "shift (Suc 0) 0 \<sigma>"
    assume 1: "v' \<in> T (subst (Suc (length \<eta>1)) (shift (Suc 0) 0 \<sigma>) \<tau>) (V # \<eta>1 @ \<eta>2)"
    from Forall[of ?R1 ?s \<eta>2] have 2: "T \<tau> (?R1 @ T ?s (?R1 @ \<eta>2) # \<eta>2) =
                                  T (subst (length ?R1) ?s \<tau>) (?R1 @ \<eta>2)" by simp
    from 1 2 have 3: "v' \<in> T \<tau> (?R1 @ T ?s (?R1 @ \<eta>2) # \<eta>2)" by simp
    have b: "T \<sigma> (\<eta>1@\<eta>2) = T ?s (V#(\<eta>1@\<eta>2))" by (rule shift_cons_preserves_T)
    from 3 b have a: "v' \<in> T \<tau> (?R1 @ T \<sigma> (\<eta>1@\<eta>2) # \<eta>2)" by simp
    from this show "v' \<in> T \<tau> (V # \<eta>1 @ T \<sigma> (\<eta>1 @ \<eta>2) # \<eta>2)" by simp
  qed
qed

lemma iterate_sound:
  assumes it: "iterate Ee \<rho> v" 
    and IH: "\<forall> v. v \<in> T (\<sigma>\<rightarrow>\<tau>) \<eta> \<longrightarrow> Ee (v#\<rho>) \<subseteq> T (\<sigma>\<rightarrow>\<tau>) \<eta>"
  shows "v \<in> T (\<sigma>\<rightarrow>\<tau>) \<eta>" using it IH
proof (induction rule: iterate.induct)
  case (iterate_none Ee \<rho>)
  then show ?case by auto 
next
  case (iterate_again Ee \<rho> f f')
  from iterate_again have f_st: "f \<in> T (\<sigma>\<rightarrow>\<tau>) \<eta>" by blast
  from iterate_again f_st have "Ee (f#\<rho>) \<subseteq> T (\<sigma>\<rightarrow>\<tau>) \<eta>" by blast
  from this iterate_again show ?case by auto
qed
  
theorem welltyped_dont_go_wrong:
  assumes wte: "\<Gamma> \<turnstile> e : \<tau>" and wfr: "\<turnstile> \<rho>,\<eta> : \<Gamma>"
  shows "E e \<rho> \<subseteq> T \<tau> \<eta>"
  using wte wfr
proof (induction \<Gamma> e \<tau> arbitrary: \<rho> \<eta> rule: well_typed.induct)
  case (wtnat \<Gamma> n \<rho> \<eta>)
  then show ?case by auto
next
  case (wtvar \<Gamma> n \<tau> \<rho> \<eta>)
  from wtvar obtain v where lx: "\<rho> ! n = v" and vt: "v \<in> T \<tau> \<eta>"using lookup_wfenv by blast
  from lx vt show ?case apply auto using T_down_closed[of "\<rho>!n" \<tau> "\<eta>"] by blast
next
  case (wtapp \<Gamma> e \<sigma> \<tau> e' \<rho> \<eta>)
  from wtapp have Ee: "E e \<rho> \<subseteq> T (\<sigma> \<rightarrow> \<tau>) \<eta>" by blast 
  from wtapp have Eep: "E e' \<rho> \<subseteq> T \<sigma> \<eta>" by blast  
  from Ee Eep show ?case using fun_app by simp
next
  case (wtlam \<sigma> \<Gamma> e \<tau> \<rho> \<eta>)
  show ?case
    apply simp apply (rule subsetI) apply clarify apply (rule_tac x=f in exI) apply simp
    apply clarify apply (erule_tac x=v1 in allE) apply (erule_tac x=v2' in allE) apply clarify 
  proof -
    fix f v1 v2' v2
    assume v1_T: "v1 \<in> T \<sigma> \<eta>" and v2_E: "v2 \<in> E e (v1#\<rho>)" and v2p_v2: "v2' \<sqsubseteq> v2"
    let ?r = "v1#\<rho>"
    from wtlam(3) v1_T have 1: "\<turnstile> v1#\<rho>,\<eta> : push_ty \<sigma> \<Gamma>" by blast
    from wtlam(2) 1 have IH: "E e (v1#\<rho>) \<subseteq> T \<tau> \<eta>" by blast
    from IH v2_E have v2_T: "v2 \<in> T \<tau> \<eta>" by blast
    from v2_T have v2_Tb: "v2 \<in> T \<tau> \<eta>" by simp
    from v2_Tb v2p_v2 show "\<exists>v2. v2 \<in> T \<tau> \<eta> \<and> v2' \<sqsubseteq> v2 " by blast
  qed
next
  case (wtfix \<sigma> \<tau> \<Gamma> e \<rho> \<eta>)
  have "\<forall> v. iterate (E e) \<rho> v \<longrightarrow> v \<in> T (\<sigma> \<rightarrow> \<tau>) \<eta>"
  proof clarify
    fix v assume it: "iterate (E e) \<rho> v"
    have 1: " \<forall>v. v \<in> T (\<sigma> \<rightarrow> \<tau>) \<eta> \<longrightarrow> E e (v#\<rho>) \<subseteq> T (\<sigma> \<rightarrow> \<tau>) \<eta>" 
    proof clarify
      fix v' v'' assume 2: "v' \<in> T (\<sigma>\<rightarrow>\<tau>) \<eta>" and 3: "v'' \<in> E e (v'#\<rho>)"
      from wtfix(3) 2 have "\<turnstile> (v'#\<rho>),\<eta> : push_ty (\<sigma> \<rightarrow> \<tau>) \<Gamma>" by blast
      from wtfix(2) this have IH: "E e (v'#\<rho>) \<subseteq> T (\<sigma>\<rightarrow>\<tau>) \<eta>" by blast
      from 3 IH have "v'' \<in> T (\<sigma>\<rightarrow>\<tau>)  \<eta>" by blast
      from this show "v'' \<in> T (\<sigma> \<rightarrow> \<tau>) \<eta>" by simp 
    qed
    from it 1 show "v \<in> T (\<sigma> \<rightarrow> \<tau>) \<eta>" using iterate_sound[of "E e" \<rho> v \<sigma> \<tau>] by blast
  qed
  from this show ?case by auto 
next
  case (wtabs \<Gamma> e \<tau> \<rho> \<eta>)
  show ?case apply simp apply (rule subsetI) apply (simp only: mem_Collect_eq)
    apply (erule disjE) apply (erule exE) apply (erule conjE) apply (rule disjI1)
     apply (rule_tac x=v' in exI) apply simp apply clarify prefer 2 apply (rule disjI2)
     apply force
  proof -
    fix x v' V assume 2: "v' \<in> E e \<rho>"
    from wtabs(3) have 3: " \<turnstile> \<rho>,(V#\<eta>) : push_tyvar \<Gamma>" by blast
    from wtabs(2) 3 have IH: "E e \<rho> \<subseteq> T \<tau> (V#\<eta>)" by blast 
    from 2 IH show "v' \<in> T \<tau> (V#\<eta>)" by (case_tac \<rho>) auto
  qed
next
  case (wtinst \<Gamma> e \<tau> \<sigma> \<rho> \<eta>)
  from wtinst(2) wtinst(3) have IH: "E e \<rho> \<subseteq> T (Forall \<tau>) \<eta>" by blast
  show ?case
    apply simp apply (rule conjI) 
     apply (rule subsetI) apply (simp only: mem_Collect_eq) apply (erule exE)
     apply (erule conjE)+
  proof -
    fix x v' assume vp_E: "v' \<in> E e \<rho>" and vp_w: "v' \<noteq> Wrong" and 
      x: "x \<in> (case v' of Abs None \<Rightarrow> {} | Abs (Some xa) \<Rightarrow> return xa
             | _ \<Rightarrow> {v'. v' \<sqsubseteq> Wrong})" 
    from IH vp_E have vp_T: "v' \<in> T (Forall \<tau>) \<eta>" by blast
    from vp_T have "(\<exists>v''. v' = Abs (Some v'') \<and> (\<forall> V. v'' \<in> T \<tau> (V#\<eta>)))
                           \<or> v' = Abs None" by simp
    from this show "x \<in> T (subst 0 \<sigma> \<tau>) \<eta>" 
    proof
      assume "\<exists>v''. v' = Abs (Some v'') \<and> (\<forall> V. v'' \<in> T \<tau> (V#\<eta>))"
      from this obtain v'' where vp: "v' = Abs (Some v'')" and 
        vpp_T: "\<forall> V. v'' \<in> T \<tau> (V#\<eta>)" by blast
      from vp x have x_vpp: "x \<sqsubseteq> v''" by auto
      let ?V = "T \<sigma> \<eta>"
      from vpp_T have "v'' \<in> T \<tau> (?V#\<eta>)" by blast
      from this have "v'' \<in> T (subst 0 \<sigma> \<tau>) \<eta>" using compositionality[of \<tau> "[]" \<sigma>] by simp
      from this x_vpp show "x \<in> T (subst 0 \<sigma> \<tau>) \<eta>" using T_down_closed by blast
    next
      assume vp: "v' = Abs None"
      from vp x show "x \<in> T (subst 0 \<sigma> \<tau>) \<eta>" by simp
    qed
  next
    from IH show "{v. v = Wrong \<and> Wrong \<in> E e \<rho>} \<subseteq> T (subst 0 \<sigma> \<tau>) \<eta>" 
      using wrong_not_in_T by auto
  qed
qed
    
end
  
