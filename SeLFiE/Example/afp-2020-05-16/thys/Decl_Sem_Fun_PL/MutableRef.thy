section "Semantics of mutable references"

theory MutableRef
  imports Main "HOL-Library.FSet" 
begin

datatype ty = TNat | TFun ty ty (infix "\<rightarrow>" 60) | TPair ty ty | TRef ty

type_synonym name = nat

datatype exp = EVar name | ENat nat | ELam ty exp | EApp exp exp 
  | EPrim "nat \<Rightarrow> nat \<Rightarrow> nat" exp exp | EIf exp exp exp
  | EPair exp exp | EFst exp | ESnd exp
  | ERef exp | ERead exp | EWrite exp exp

subsection "Denotations (values)"
  
datatype val = VNat nat | VFun "(val \<times> val) fset" | VPair val val | VAddr nat | Wrong

type_synonym func = "(val \<times> val) fset"
type_synonym store = "func"

inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where
  vnat_le[intro!]: "(VNat n) \<sqsubseteq> (VNat n)" |
  vaddr_le[intro!]: "(VAddr a) \<sqsubseteq> (VAddr a)" | 
  wrong_le[intro!]: "Wrong \<sqsubseteq> Wrong" |
  vfun_le[intro!]: "t1 |\<subseteq>| t2 \<Longrightarrow> (VFun t1) \<sqsubseteq> (VFun t2)" |
  vpair_le[intro!]: "\<lbrakk> v1 \<sqsubseteq> v1'; v2 \<sqsubseteq> v2' \<rbrakk> \<Longrightarrow> (VPair v1 v2) \<sqsubseteq> (VPair v1' v2')" 

primrec vsize :: "val \<Rightarrow> nat" where
"vsize (VNat n) = 1" |
"vsize (VFun t) = 1 + ffold (\<lambda>((_,v), (_,u)).\<lambda>r. v + u + r) 0
                            (fimage (map_prod (\<lambda> v. (v,vsize v)) (\<lambda> v. (v,vsize v))) t)" |
"vsize (VPair v1 v2) = 1 + vsize v1 + vsize v2" |
"vsize (VAddr a) = 1" |
"vsize Wrong = 1" 

subsection "Non-deterministic state monad"

type_synonym 'a M = "store \<Rightarrow> ('a \<times> store) set"

definition bind :: "'a M \<Rightarrow> ('a \<Rightarrow> 'b M) \<Rightarrow> 'b M" where
  "bind m f \<mu>1 \<equiv> { (v,\<mu>3). \<exists> v' \<mu>2. (v',\<mu>2) \<in> m \<mu>1 \<and> (v,\<mu>3) \<in> f v' \<mu>2 }"
declare bind_def[simp]

syntax "_bind" :: "[pttrns,'a M,'b] \<Rightarrow> 'c" ("(_ \<leftarrow> _;//_)" 0)
translations "P \<leftarrow> E; F" \<rightleftharpoons> "CONST bind E (\<lambda>P. F)"

no_notation "binomial" (infixl "choose" 65)

definition choose :: "'a set \<Rightarrow> 'a M" where
  "choose S \<mu> \<equiv> {(a,\<mu>1). a \<in> S \<and> \<mu>1=\<mu>}"
declare choose_def[simp]
  
definition return :: "'a \<Rightarrow> 'a M" where
  "return v \<mu> \<equiv> { (v,\<mu>) }"
declare return_def[simp]

definition zero :: "'a M" where
  "zero \<mu> \<equiv> {}"
declare zero_def[simp]
   
definition err_bind :: "val M \<Rightarrow> (val \<Rightarrow> val M) \<Rightarrow> val M" where
  "err_bind m f \<equiv> (x \<leftarrow> m; if x = Wrong then return Wrong else f x)"
declare err_bind_def[simp]

syntax "_errset_bind" :: "[pttrns,val M,val] \<Rightarrow> 'c" ("(_ := _;//_)" 0)
translations "P := E; F" \<rightleftharpoons> "CONST err_bind E (\<lambda>P. F)"

definition down :: "val \<Rightarrow> val M" where
  "down v \<mu>1 \<equiv> {(v',\<mu>). v' \<sqsubseteq> v \<and> \<mu> = \<mu>1 }"
declare down_def[simp]

definition get_store :: "store M" where
  "get_store \<mu> \<equiv> { (\<mu>,\<mu>) }"
declare get_store_def[simp]
  
definition put_store :: "store \<Rightarrow> unit M" where
  "put_store \<mu> \<equiv> \<lambda>_. { ((),\<mu>) }"
declare put_store_def[simp]

definition mapM :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b M) \<Rightarrow> ('b fset) M" where
  "mapM as f \<equiv> ffold (\<lambda>a. \<lambda>r. (b \<leftarrow> f a; bs \<leftarrow> r; return (finsert b bs))) (return {||}) as"

definition run :: "store \<Rightarrow> val M \<Rightarrow> (val \<times> store) set" where
  "run \<sigma> m \<equiv> m \<sigma>"
declare run_def[simp]

definition sdom :: "store \<Rightarrow> nat set" where
  "sdom \<mu> \<equiv> {a. \<exists> v. (VAddr a,v) \<in> fset \<mu> }"

definition max_addr :: "store \<Rightarrow> nat" where
  "max_addr \<mu> = ffold (\<lambda>a.\<lambda>r. case a of (VAddr n,_) \<Rightarrow> max n r | _ \<Rightarrow> r) 0 \<mu>"
 
subsection "Denotational semantics"

abbreviation apply_fun :: "val M \<Rightarrow> val M \<Rightarrow> val M" where
  "apply_fun V1 V2 \<equiv> (v1 := V1; v2 := V2;
                       case v1 of VFun f \<Rightarrow> 
                          (p, p') \<leftarrow> choose (fset f); \<mu>0 \<leftarrow> get_store;
                          (case (p,p') of (VPair v (VFun \<mu>), VPair v' (VFun \<mu>')) \<Rightarrow>
                            if v \<sqsubseteq> v2 \<and> (VFun \<mu>) \<sqsubseteq> (VFun \<mu>0) then (_ \<leftarrow> put_store \<mu>'; down v') 
                            else zero
                          | _ \<Rightarrow> zero)
                       | _ \<Rightarrow> return Wrong)"  

fun nvals :: "nat \<Rightarrow> (val fset) M" where
  "nvals 0 = return {||}" |
  "nvals (Suc k) = (v \<leftarrow> choose UNIV; L \<leftarrow> nvals k; return (finsert v L))"

definition vals :: "(val fset) M" where
  "vals \<equiv> (n \<leftarrow> choose UNIV; nvals n)"
declare vals_def[simp]

fun npairs :: "nat \<Rightarrow> func M" where
  "npairs 0 = return {||}" |
  "npairs (Suc k) = (v \<leftarrow> choose UNIV; v' \<leftarrow> choose {v::val. True};
                     P \<leftarrow> npairs k; return (finsert (v,v') P))"  

definition tables :: "func M" where
  "tables \<equiv> (n \<leftarrow> choose {k::nat. True}; npairs n)"
declare tables_def[simp]

definition read :: "nat \<Rightarrow> val M" where
  "read a \<equiv> (\<mu> \<leftarrow> get_store; if a \<in> sdom \<mu> then
                           ((v1,v2) \<leftarrow> choose (fset \<mu>); if v1 = VAddr a then return v2 else zero)
                       else return Wrong)"
declare read_def[simp]

definition update :: "nat \<Rightarrow> val \<Rightarrow> val M" where
  "update a v \<equiv> (\<mu> \<leftarrow> get_store;
                 _ \<leftarrow> put_store (finsert (VAddr a,v) (ffilter (\<lambda>(v,v'). v \<noteq> VAddr a) \<mu>));
                 return (VAddr a))"
declare update_def[simp]

type_synonym env = "val list"    
  
fun E :: "exp \<Rightarrow> env \<Rightarrow> val M" where
  Enat: "E (ENat n) \<rho> = return (VNat n)" |
  Evar: "E (EVar n) \<rho> = (if n < length \<rho> then down (\<rho>!n) else return Wrong)" |
  Elam: "E (ELam A e) \<rho> = (L \<leftarrow> vals; 
                           t \<leftarrow> mapM L (\<lambda> v. (\<mu> \<leftarrow> tables;  (v',\<mu>') \<leftarrow> choose (run \<mu> (E e (v#\<rho>))); 
                                     return (VPair v (VFun \<mu>),VPair v' (VFun \<mu>'))));
                           return (VFun t))" |
  Eapp: "E (EApp e1 e2) \<rho> = apply_fun (E e1 \<rho>) (E e2 \<rho>)" |
  Eprim: "E (EPrim f e1 e2) \<rho> = (v1 := E e1 \<rho>; v2 := E e2 \<rho>;
                                 case (v1, v2) of (VNat n1,VNat n2) \<Rightarrow> return (VNat (f n1 n2))
                                 | _ \<Rightarrow> return Wrong)" |
  Eif: "E (EIf e1 e2 e3) \<rho> = (v1 := E e1 \<rho>; case v1 of VNat n \<Rightarrow> (if n = 0 then E e3 \<rho> else E e2 \<rho>)
                                            | _ \<Rightarrow> return Wrong)" |
  Epair: "E (EPair e1 e2) \<rho> = (v1 := E e1 \<rho>; v2 := E e2 \<rho>; return (VPair v1 v2))" |
  Efst: "E (EFst e) \<rho> = (v:=E e \<rho>; case v of VPair v1 v2 \<Rightarrow> return v1 | _ \<Rightarrow> return Wrong)" |
  Esnd: "E (ESnd e) \<rho> = (v:=E e \<rho>; case v of VPair v1 v2 \<Rightarrow> return v2 | _ \<Rightarrow> return Wrong)" |
  Eref: "E (ERef e) \<rho> = (v:=E e \<rho>; \<mu> \<leftarrow> get_store; a \<leftarrow> choose UNIV;
                         if a \<in> sdom \<mu> then zero
                         else (_ \<leftarrow> put_store (finsert (VAddr a,v) \<mu>);
                               return (VAddr a)))" |
  Eread: "E (ERead e) \<rho> = (v := E e \<rho>; case v of VAddr a \<Rightarrow> read a | _ \<Rightarrow> return Wrong)" |
  Ewrite: "E (EWrite e1 e2) \<rho> = (v1 := E e1 \<rho>; v2 := E e2 \<rho>;
                                 case v1 of VAddr a \<Rightarrow> update a v2 | _ \<Rightarrow> return Wrong)"


  
  

end
  
   
