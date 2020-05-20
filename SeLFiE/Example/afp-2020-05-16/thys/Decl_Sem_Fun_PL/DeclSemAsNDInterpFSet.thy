section "Declarative semantics as a non-deterministic interpreter"
  
theory DeclSemAsNDInterpFSet
  imports Lambda ValuesFSet
begin
  
subsection "Non-determinism monad"

type_synonym 'a M = "'a set"

definition set_bind :: "'a M \<Rightarrow> ('a \<Rightarrow> 'b M) \<Rightarrow> 'b M" where
  "set_bind m f \<equiv> { v. \<exists> v'. v' \<in> m \<and> v \<in> f v' }"
declare set_bind_def[simp]

syntax "_set_bind" :: "[pttrns,'a M,'b] \<Rightarrow> 'c" ("(_ \<leftarrow> _;//_)" 0)
translations "P \<leftarrow> E; F" \<rightleftharpoons> "CONST set_bind E (\<lambda>P. F)"

definition return :: "'a \<Rightarrow> 'a M" where
  "return v \<equiv> {v}"
declare return_def[simp]

definition zero :: "'a M" where
  "zero \<equiv> {}"
declare zero_def[simp]

no_notation "binomial" (infixl "choose" 65)

definition choose :: "'a set \<Rightarrow> 'a M" where
  "choose S \<equiv> S"
declare choose_def[simp]
 
definition down :: "val \<Rightarrow> val M" where
  "down v \<equiv> (v' \<leftarrow> UNIV; if v' \<sqsubseteq> v then return v' else zero)"
declare down_def[simp]

definition mapM :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b M) \<Rightarrow> ('b fset) M" where
  "mapM as f \<equiv> ffold (\<lambda>a. \<lambda>r. (b \<leftarrow> f a; bs \<leftarrow> r; return (finsert b bs))) (return ({||})) as"
  
subsection "Non-deterministic interpreter"

abbreviation apply_fun :: "val M \<Rightarrow> val M \<Rightarrow> val M" where
  "apply_fun V1 V2 \<equiv> (v1 \<leftarrow> V1; v2 \<leftarrow> V2;
                       case v1 of VFun f \<Rightarrow> 
                          (v2',v3') \<leftarrow> choose (fset f);
                          if v2' \<sqsubseteq> v2 then return v3' else zero
                       | _ \<Rightarrow> zero)"

fun E :: "exp \<Rightarrow> env \<Rightarrow> val set" where
  Enat2: "E (ENat n) \<rho> = return (VNat n)" |
  Evar2: "E (EVar x) \<rho> = (case lookup \<rho> x of None \<Rightarrow> zero | Some v \<Rightarrow> down v)" |
  Elam2: "E (ELam x e) \<rho> = (vs \<leftarrow> choose UNIV; 
                           t \<leftarrow> mapM vs (\<lambda> v. (v' \<leftarrow> E e ((x,v)#\<rho>); return (v, v')));
                           return (VFun t))" |
  Eapp2: "E (EApp e1 e2) \<rho> = apply_fun (E e1 \<rho>) (E e2 \<rho>)" |
  Eprim2: "E (EPrim f e1 e2) \<rho> = (v\<^sub>1 \<leftarrow> E e1 \<rho>; v\<^sub>2 \<leftarrow> E e2 \<rho>;
                                 case (v\<^sub>1,v\<^sub>2) of
                                   (VNat n\<^sub>1, VNat n\<^sub>2) \<Rightarrow> return (VNat (f n\<^sub>1 n\<^sub>2))
                                | (VNat n\<^sub>1, VFun t\<^sub>2) \<Rightarrow> zero
                                | (VFun t\<^sub>1, v\<^sub>2) \<Rightarrow> zero)" |
  Eif2[eta_contract = false]: "E (EIf e1 e2 e3) \<rho> = (v\<^sub>1 \<leftarrow> E e1 \<rho>;
                              case v\<^sub>1 of
                                (VNat n) \<Rightarrow> if n \<noteq> 0 then E e2 \<rho> else E e3 \<rho>
                              | (VFun t) \<Rightarrow> zero)"

end
  
