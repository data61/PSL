(*  Title:      Jinja/J/Expr.thy
    Author:     Tobias Nipkow
    Copyright   2003 Technische Universitaet Muenchen
*)

section \<open>Expressions\<close>

theory Expr
imports "../Common/Exceptions"
begin

datatype bop = Eq | Add     \<comment> \<open>names of binary operations\<close>

datatype 'a exp
  = new cname      \<comment> \<open>class instance creation\<close>
  | Cast cname "('a exp)"      \<comment> \<open>type cast\<close>
  | Val val      \<comment> \<open>value\<close>
  | BinOp "('a exp)" bop "('a exp)"     ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80)      \<comment> \<open>binary operation\<close>
  | Var 'a                                               \<comment> \<open>local variable (incl. parameter)\<close>
  | LAss 'a "('a exp)"     ("_:=_" [90,90]90)                    \<comment> \<open>local assignment\<close>
  | FAcc "('a exp)" vname cname     ("_\<bullet>_{_}" [10,90,99]90)      \<comment> \<open>field access\<close>
  | FAss "('a exp)" vname cname "('a exp)"     ("_\<bullet>_{_} := _" [10,90,99,90]90)      \<comment> \<open>field assignment\<close>
  | Call "('a exp)" mname "('a exp list)"     ("_\<bullet>_'(_')" [90,99,0] 90)            \<comment> \<open>method call\<close>
  | Block 'a ty "('a exp)"     ("'{_:_; _}")
  | Seq "('a exp)" "('a exp)"     ("_;;/ _"             [61,60]60)
  | Cond "('a exp)" "('a exp)" "('a exp)"     ("if '(_') _/ else _" [80,79,79]70)
  | While "('a exp)" "('a exp)"     ("while '(_') _"     [80,79]70)
  | throw "('a exp)"
  | TryCatch "('a exp)" cname 'a "('a exp)"     ("try _/ catch'(_ _') _"  [0,99,80,79] 70)

type_synonym
  expr = "vname exp"            \<comment> \<open>Jinja expression\<close>
type_synonym
  J_mb = "vname list \<times> expr"    \<comment> \<open>Jinja method body: parameter names and expression\<close>
type_synonym
  J_prog = "J_mb prog"          \<comment> \<open>Jinja program\<close>

text\<open>The semantics of binary operators:\<close>

fun binop :: "bop \<times> val \<times> val \<Rightarrow> val option" where
  "binop(Eq,v\<^sub>1,v\<^sub>2) = Some(Bool (v\<^sub>1 = v\<^sub>2))"
| "binop(Add,Intg i\<^sub>1,Intg i\<^sub>2) = Some(Intg(i\<^sub>1+i\<^sub>2))"
| "binop(bop,v\<^sub>1,v\<^sub>2) = None"

lemma [simp]:
  "(binop(Add,v\<^sub>1,v\<^sub>2) = Some v) = (\<exists>i\<^sub>1 i\<^sub>2. v\<^sub>1 = Intg i\<^sub>1 \<and> v\<^sub>2 = Intg i\<^sub>2 \<and> v = Intg(i\<^sub>1+i\<^sub>2))"
(*<*)
apply(cases v\<^sub>1)
apply auto
apply(cases v\<^sub>2)
apply auto
done
(*>*)


subsection "Syntactic sugar"

abbreviation (input)
  InitBlock:: "'a \<Rightarrow> ty \<Rightarrow> 'a exp \<Rightarrow> 'a exp \<Rightarrow> 'a exp"   ("(1'{_:_ := _;/ _})") where
  "InitBlock V T e1 e2 == {V:T; V := e1;; e2}"

abbreviation unit where "unit == Val Unit"
abbreviation null where "null == Val Null"
abbreviation "addr a == Val(Addr a)"
abbreviation "true == Val(Bool True)"
abbreviation "false == Val(Bool False)"

abbreviation
  Throw :: "addr \<Rightarrow> 'a exp" where
  "Throw a == throw(Val(Addr a))"

abbreviation
  THROW :: "cname \<Rightarrow> 'a exp" where
  "THROW xc == Throw(addr_of_sys_xcpt xc)"


subsection\<open>Free Variables\<close>

primrec fv :: "expr \<Rightarrow> vname set" and fvs :: "expr list \<Rightarrow> vname set" where
  "fv(new C) = {}"
| "fv(Cast C e) = fv e"
| "fv(Val v) = {}"
| "fv(e\<^sub>1 \<guillemotleft>bop\<guillemotright> e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(Var V) = {V}"
| "fv(LAss V e) = {V} \<union> fv e"
| "fv(e\<bullet>F{D}) = fv e"
| "fv(e\<^sub>1\<bullet>F{D}:=e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(e\<bullet>M(es)) = fv e \<union> fvs es"
| "fv({V:T; e}) = fv e - {V}"
| "fv(e\<^sub>1;;e\<^sub>2) = fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(if (b) e\<^sub>1 else e\<^sub>2) = fv b \<union> fv e\<^sub>1 \<union> fv e\<^sub>2"
| "fv(while (b) e) = fv b \<union> fv e"
| "fv(throw e) = fv e"
| "fv(try e\<^sub>1 catch(C V) e\<^sub>2) = fv e\<^sub>1 \<union> (fv e\<^sub>2 - {V})"
| "fvs([]) = {}"
| "fvs(e#es) = fv e \<union> fvs es"

lemma [simp]: "fvs(es\<^sub>1 @ es\<^sub>2) = fvs es\<^sub>1 \<union> fvs es\<^sub>2"
(*<*)by (induct es\<^sub>1 type:list) auto(*>*)

lemma [simp]: "fvs(map Val vs) = {}"
(*<*)by (induct vs) auto(*>*)

end
