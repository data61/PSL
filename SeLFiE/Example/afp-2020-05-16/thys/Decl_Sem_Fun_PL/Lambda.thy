section "Syntax of the lambda calculus"

theory Lambda
imports Main
begin
  
type_synonym name = nat

datatype exp = EVar name | ENat nat | ELam name exp | EApp exp exp
  | EPrim "nat \<Rightarrow> nat \<Rightarrow> nat" exp exp | EIf exp exp exp
      
fun lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "lookup [] x = None" |
  "lookup ((y,v)#ls) x = (if (x = y) then Some v else lookup ls x)"

fun FV :: "exp \<Rightarrow> nat set" where
  "FV (EVar x) = {x}" |
  "FV (ENat n) = {}" |
  "FV (ELam x e) = FV e - {x}" |
  "FV (EApp e1 e2) = FV e1 \<union> FV e2" |
  "FV (EPrim f e1 e2) = FV e1 \<union> FV e2" |
  "FV (EIf e1 e2 e3) = FV e1 \<union> FV e2 \<union> FV e3"

fun BV :: "exp \<Rightarrow> nat set" where
  "BV (EVar x) = {}" |
  "BV (ENat n) = {}" |
  "BV (ELam x e) = BV e \<union> {x}" |
  "BV (EApp e1 e2) = BV e1 \<union> BV e2" |
  "BV (EPrim f e1 e2) = BV e1 \<union> BV e2" |
  "BV (EIf e1 e2 e3) = BV e1 \<union> BV e2 \<union> BV e3"

end
