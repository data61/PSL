theory DeclSemAsDenotFSet
  imports Lambda ValuesFSet
begin
  
section "Declarative semantics as a denotational semantics"

fun E :: "exp \<Rightarrow> env \<Rightarrow> val set" where
  Enat: "E (ENat n) \<rho> = { v. v = VNat n }" |
  Evar: "E (EVar x) \<rho> = { v. \<exists> v'. lookup \<rho> x = Some v' \<and> v \<sqsubseteq> v' }" |
  Elam: "E (ELam x e) \<rho> = { v. \<exists> f. v = VFun f \<and> (\<forall> v1 v2. (v1, v2) \<in> fset f 
    \<longrightarrow> v2 \<in> E e ((x,v1)#\<rho>)) }" |
  Eapp: "E (EApp e1 e2) \<rho> = { v3. \<exists> f v2 v2' v3'. 
      VFun f \<in> E e1 \<rho> \<and> v2 \<in> E e2 \<rho> \<and> (v2', v3') \<in> fset f \<and> v2' \<sqsubseteq> v2 \<and> v3 \<sqsubseteq> v3' }" |
  Eprim: "E (EPrim f e1 e2) \<rho> = { v. \<exists> n1 n2. VNat n1 \<in> E e1 \<rho> 
          \<and> VNat n2 \<in> E e2 \<rho> \<and> v = VNat (f n1 n2) }" |
  Eif: "E (EIf e1 e2 e3) \<rho> = { v. \<exists> n. VNat n \<in> E e1 \<rho>
         \<and> (n = 0 \<longrightarrow> v \<in> E e3 \<rho>) \<and> (n \<noteq> 0 \<longrightarrow> v \<in> E e2 \<rho>) }"

end
  
  
