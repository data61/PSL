(*  Title:       CoreC++
    Author:      Daniel Wasserrab
    Maintainer:  Daniel Wasserrab <wasserra at fmi.uni-passau.de>
    Based on the Jinja theory J/Expr.thy by Tobias Nipkow 
*)

section \<open>Expressions\<close>

theory Expr imports Value begin

subsection \<open>The expressions\<close>


datatype bop = Eq | Add     \<comment> \<open>names of binary operations\<close>

datatype expr
  = new cname            \<comment> \<open>class instance creation\<close>
  | Cast cname expr      \<comment> \<open>dynamic type cast\<close>
  | StatCast cname expr  \<comment> \<open>static type cast\<close>        
                                 ("\<lparr>_\<rparr>_" [80,81] 80)
  | Val val              \<comment> \<open>value\<close>
  | BinOp expr bop expr          ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80)     
     \<comment> \<open>binary operation\<close>
  | Var vname            \<comment> \<open>local variable\<close>
  | LAss vname expr              ("_:=_" [70,70] 70)            
     \<comment> \<open>local assignment\<close>
  | FAcc expr vname path         ("_\<bullet>_{_}" [10,90,99] 90)      
     \<comment> \<open>field access\<close>
  | FAss expr vname path expr    ("_\<bullet>_{_} := _" [10,70,99,70] 70)      
     \<comment> \<open>field assignment\<close>
  | Call expr "cname option" mname "expr list"
     \<comment> \<open>method call\<close>
  | Block vname ty expr          ("'{_:_; _}")
  | Seq expr expr                ("_;;/ _" [61,60] 60)
  | Cond expr expr expr          ("if '(_') _/ else _" [80,79,79] 70)
  | While expr expr              ("while '(_') _" [80,79] 70)
  | throw expr

abbreviation (input)
  DynCall :: "expr \<Rightarrow> mname \<Rightarrow> expr list \<Rightarrow> expr" ("_\<bullet>_'(_')" [90,99,0] 90) where
  "e\<bullet>M(es) == Call e None M es"

abbreviation (input)
  StaticCall :: "expr \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> expr list \<Rightarrow> expr" 
     ("_\<bullet>'(_::')_'(_')" [90,99,99,0] 90) where
  "e\<bullet>(C::)M(es) == Call e (Some C) M es"


text\<open>The semantics of binary operators:\<close>

fun binop :: "bop \<times> val \<times> val \<Rightarrow> val option" where
  "binop(Eq,v\<^sub>1,v\<^sub>2) = Some(Bool (v\<^sub>1 = v\<^sub>2))"
| "binop(Add,Intg i\<^sub>1,Intg i\<^sub>2) = Some(Intg(i\<^sub>1+i\<^sub>2))"
| "binop(bop,v\<^sub>1,v\<^sub>2) = None"

lemma [simp]:
  "(binop(Add,v\<^sub>1,v\<^sub>2) = Some v) = (\<exists>i\<^sub>1 i\<^sub>2. v\<^sub>1 = Intg i\<^sub>1 \<and> v\<^sub>2 = Intg i\<^sub>2 \<and> v = Intg(i\<^sub>1+i\<^sub>2))"
apply(cases v\<^sub>1)
apply auto
apply(cases v\<^sub>2)
apply auto
done

lemma binop_not_ref[simp]:
  "binop(bop,v\<^sub>1,v\<^sub>2) = Some (Ref r) \<Longrightarrow> False"
by(cases bop)auto


subsection\<open>Free Variables\<close> 

primrec
  fv  :: "expr      \<Rightarrow> vname set"
  and fvs :: "expr list \<Rightarrow> vname set" where
  "fv(new C) = {}"
| "fv(Cast C e) = fv e"
|  "fv(\<lparr>C\<rparr>e) = fv e"
| "fv(Val v) = {}"
| "fv(e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(Var V) = {V}"
| "fv(V := e) = {V} \<union> fv e"
| "fv(e\<bullet>F{Cs}) = fv e"
| "fv(e\<^sub>1\<bullet>F{Cs}:=e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(Call e Copt M es) = fv e \<union> fvs es"
| "fv({V:T; e}) = fv e - {V}"
| "fv(e\<^sub>1;;e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(if (b) e\<^sub>1 else e\<^sub>2) = fv b \<union> fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(while (b) e) = fv b \<union> fv e"
| "fv(throw e) = fv e"

| "fvs([]) = {}"
| "fvs(e#es) = fv e \<union> fvs es"

lemma [simp]: "fvs(es\<^sub>1 @ es\<^sub>2) = fvs es\<^sub>1 \<union> fvs es\<^sub>2"
by (induct es\<^sub>1 type:list) auto

lemma [simp]: "fvs(map Val vs) = {}"
by (induct vs) auto


end
