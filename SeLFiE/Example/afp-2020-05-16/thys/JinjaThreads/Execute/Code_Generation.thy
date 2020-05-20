(*  Title:      JinjaThreads/Execute/Code_Generation.thy
    Author:     Andreas Lochbihler
*)

section \<open>Code generator setup\<close>

theory Code_Generation 
imports
  J_Execute
  JVM_Execute2 
  "../Compiler/Preprocessor"
  "../BV/BCVExec"
  "../Compiler/Compiler"
  Coinductive.Lazy_TLList
  "HOL-Library.Code_Target_Int"
  "HOL-Library.Code_Target_Numeral"
begin

text \<open>Avoid module dependency cycles.\<close>
(* FIXME: Eliminate dependency cycle in Isabelle library *) 

code_identifier
  code_module More_Set \<rightharpoonup> (SML) Set
| code_module Set \<rightharpoonup> (SML) Set
| code_module Complete_Lattices \<rightharpoonup> (SML) Set
| code_module Complete_Partial_Order \<rightharpoonup> (SML) Set

text \<open>new code equation for @{term "insort_insert_key"} to avoid module dependency cycle with @{term "set"}.\<close>
lemma insort_insert_key_code [code]:
  "insort_insert_key f x xs = 
  (if List.member (map f xs) (f x) then xs else insort_key f x xs)"
by(simp add: insort_insert_key_def List.member_def split del: if_split)


text \<open>equations on predicate operations for code inlining\<close>

lemma eq_i_o_conv_single: "eq_i_o = Predicate.single"
by(rule ext)(simp add: Predicate.single_bind eq.equation)

lemma eq_o_i_conv_single: "eq_o_i = Predicate.single"
by(rule ext)(simp add: Predicate.single_bind eq.equation)

lemma sup_case_exp_case_exp_same:
  "sup_class.sup 
    (case_exp cNew cNewArray cCast cInstanceOf cVal cBinOp cVar cLAss cAAcc cAAss cALen cFAcc cFAss cCAS cCall cBlock cSync cInSync cSeq cCond cWhile cThrow cTry e)
    (case_exp cNew' cNewArray' cCast' cInstanceOf' cVal' cBinOp' cVar' cLAss' cAAcc' cAAss' cALen' cFAcc' cFAss' cCAS' cCall' cBlock' cSync' cInSync' cSeq' cCond' cWhile' cThrow' cTry' e) =
  (case e of
    new C \<Rightarrow> sup_class.sup (cNew C) (cNew' C)
  | newArray T e \<Rightarrow> sup_class.sup (cNewArray T e) (cNewArray' T e)
  | Cast T e \<Rightarrow> sup_class.sup (cCast T e) (cCast' T e)
  | InstanceOf e T \<Rightarrow> sup_class.sup (cInstanceOf e T) (cInstanceOf' e T)
  | Val v \<Rightarrow> sup_class.sup (cVal v) (cVal' v)
  | BinOp e bop e' \<Rightarrow> sup_class.sup (cBinOp e bop e') (cBinOp' e bop e')
  | Var V \<Rightarrow> sup_class.sup (cVar V) (cVar' V)
  | LAss V e \<Rightarrow> sup_class.sup (cLAss V e) (cLAss' V e)
  | AAcc a e \<Rightarrow> sup_class.sup (cAAcc a e) (cAAcc' a e)
  | AAss a i e \<Rightarrow> sup_class.sup (cAAss a i e) (cAAss' a i e)
  | ALen a \<Rightarrow> sup_class.sup (cALen a) (cALen' a)
  | FAcc e F D \<Rightarrow> sup_class.sup (cFAcc e F D) (cFAcc' e F D)
  | FAss e F D e' \<Rightarrow> sup_class.sup (cFAss e F D e') (cFAss' e F D e')
  | CompareAndSwap e D F e' e'' \<Rightarrow> sup_class.sup (cCAS e D F e' e'') (cCAS' e D F e' e'')
  | Call e M es \<Rightarrow> sup_class.sup (cCall e M es) (cCall' e M es)
  | Block V T vo e \<Rightarrow> sup_class.sup (cBlock V T vo e) (cBlock' V T vo e)
  | Synchronized v e e' \<Rightarrow> sup_class.sup (cSync v e e') (cSync' v e e')
  | InSynchronized v a e \<Rightarrow> sup_class.sup (cInSync v a e) (cInSync' v a e)
  | Seq e e' \<Rightarrow> sup_class.sup (cSeq e e') (cSeq' e e')
  | Cond b e e' \<Rightarrow> sup_class.sup (cCond b e e') (cCond' b e e')
  | While b e \<Rightarrow> sup_class.sup (cWhile b e) (cWhile' b e)
  | throw e \<Rightarrow> sup_class.sup (cThrow e) (cThrow' e)
  | TryCatch e C V e' \<Rightarrow> sup_class.sup (cTry e C V e') (cTry' e C V e'))"
apply(cases e)
apply(simp_all)
done

lemma sup_case_exp_case_exp_other:
  fixes p :: "'a :: semilattice_sup" shows
  "sup_class.sup 
    (case_exp cNew cNewArray cCast cInstanceOf cVal cBinOp cVar cLAss cAAcc cAAss cALen cFAcc cFAss cCAS cCall cBlock cSync cInSync cSeq cCond cWhile cThrow cTry e)
    (sup_class.sup (case_exp cNew' cNewArray' cCast' cInstanceOf' cVal' cBinOp' cVar' cLAss' cAAcc' cAAss' cALen' cFAcc' cFAss' cCAS' cCall' cBlock' cSync' cInSync' cSeq' cCond' cWhile' cThrow' cTry' e) p) =
  sup_class.sup (case e of
    new C \<Rightarrow> sup_class.sup (cNew C) (cNew' C)
  | newArray T e \<Rightarrow> sup_class.sup (cNewArray T e) (cNewArray' T e)
  | Cast T e \<Rightarrow> sup_class.sup (cCast T e) (cCast' T e)
  | InstanceOf e T \<Rightarrow> sup_class.sup (cInstanceOf e T) (cInstanceOf' e T)
  | Val v \<Rightarrow> sup_class.sup (cVal v) (cVal' v)
  | BinOp e bop e' \<Rightarrow> sup_class.sup (cBinOp e bop e') (cBinOp' e bop e')
  | Var V \<Rightarrow> sup_class.sup (cVar V) (cVar' V)
  | LAss V e \<Rightarrow> sup_class.sup (cLAss V e) (cLAss' V e)
  | AAcc a e \<Rightarrow> sup_class.sup (cAAcc a e) (cAAcc' a e)
  | AAss a i e \<Rightarrow> sup_class.sup (cAAss a i e) (cAAss' a i e)
  | ALen a \<Rightarrow> sup_class.sup (cALen a) (cALen' a)
  | FAcc e F D \<Rightarrow> sup_class.sup (cFAcc e F D) (cFAcc' e F D)
  | FAss e F D e' \<Rightarrow> sup_class.sup (cFAss e F D e') (cFAss' e F D e')
  | CompareAndSwap e D F e' e'' \<Rightarrow> sup_class.sup (cCAS e D F e' e'') (cCAS' e D F e' e'')
  | Call e M es \<Rightarrow> sup_class.sup (cCall e M es) (cCall' e M es)
  | Block V T vo e \<Rightarrow> sup_class.sup (cBlock V T vo e) (cBlock' V T vo e)
  | Synchronized v e e' \<Rightarrow> sup_class.sup (cSync v e e') (cSync' v e e')
  | InSynchronized v a e \<Rightarrow> sup_class.sup (cInSync v a e) (cInSync' v a e)
  | Seq e e' \<Rightarrow> sup_class.sup (cSeq e e') (cSeq' e e')
  | Cond b e e' \<Rightarrow> sup_class.sup (cCond b e e') (cCond' b e e')
  | While b e \<Rightarrow> sup_class.sup (cWhile b e) (cWhile' b e)
  | throw e \<Rightarrow> sup_class.sup (cThrow e) (cThrow' e)
  | TryCatch e C V e' \<Rightarrow> sup_class.sup (cTry e C V e') (cTry' e C V e')) p"
apply(cases e)
apply(simp_all add: inf_sup_aci sup.assoc)
done

lemma sup_bot1: "sup_class.sup bot a = (a :: 'a :: {semilattice_sup, order_bot})"
by(rule sup_absorb2)auto

lemma sup_bot2: "sup_class.sup a bot = (a :: 'a :: {semilattice_sup, order_bot})"
by(rule sup_absorb1) auto

lemma sup_case_val_case_val_same:
  "sup_class.sup (case_val cUnit cNull cBool cIntg cAddr v) (case_val cUnit' cNull' cBool' cIntg' cAddr' v) =
   (case v of
     Unit \<Rightarrow> sup_class.sup cUnit cUnit'
   | Null \<Rightarrow> sup_class.sup cNull cNull'
   | Bool b \<Rightarrow> sup_class.sup (cBool b) (cBool' b)
   | Intg i \<Rightarrow> sup_class.sup (cIntg i) (cIntg' i)
   | Addr a \<Rightarrow> sup_class.sup (cAddr a) (cAddr' a))"
apply(cases v)
apply simp_all
done

lemma sup_case_bool_case_bool_same:
  "sup_class.sup (case_bool t f b) (case_bool t' f' b) =
  (if b then sup_class.sup t t' else sup_class.sup f f')"
by simp

lemmas predicate_code_inline [code_unfold] =
  Predicate.single_bind Predicate.bind_single split
  eq_i_o_conv_single eq_o_i_conv_single
  sup_case_exp_case_exp_same sup_case_exp_case_exp_other unit.case
  sup_bot1 sup_bot2 sup_case_val_case_val_same sup_case_bool_case_bool_same

lemma op_case_ty_case_ty_same:
  "f (case_ty cVoid cBoolean cInteger cNT cClass cArray e)
     (case_ty cVoid' cBoolean' cInteger' cNT' cClass' cArray' e) =
  (case e of
     Void \<Rightarrow> f cVoid cVoid'
   | Boolean \<Rightarrow> f cBoolean cBoolean'
   | Integer \<Rightarrow> f cInteger cInteger'
   | NT \<Rightarrow> f cNT cNT'
   | Class C \<Rightarrow> f (cClass C) (cClass' C)
   | Array T \<Rightarrow> f (cArray T) (cArray' T))"
by(simp split: ty.split)

declare op_case_ty_case_ty_same[where f="sup_class.sup", code_unfold]

lemma op_case_bop_case_bop_same:
  "f (case_bop cEq cNotEq cLessThan cLessOrEqual cGreaterThan cGreaterOrEqual cAdd cSubtract cMult cDiv cMod cBinAnd cBinOr cBinXor cShiftLeft cShiftRightZeros cShiftRightSigned bop)
     (case_bop cEq' cNotEq' cLessThan' cLessOrEqual' cGreaterThan' cGreaterOrEqual' cAdd' cSubtract' cMult' cDiv' cMod' cBinAnd' cBinOr' cBinXor' cShiftLeft' cShiftRightZeros' cShiftRightSigned' bop)
  = case_bop (f cEq cEq') (f cNotEq cNotEq') (f cLessThan cLessThan') (f cLessOrEqual cLessOrEqual') (f cGreaterThan cGreaterThan') (f cGreaterOrEqual cGreaterOrEqual') (f cAdd cAdd') (f cSubtract cSubtract') (f cMult cMult') (f cDiv cDiv') (f cMod cMod') (f cBinAnd cBinAnd') (f cBinOr cBinOr') (f cBinXor cBinXor') (f cShiftLeft cShiftLeft') (f cShiftRightZeros cShiftRightZeros') (f cShiftRightSigned cShiftRightSigned') bop"
by(simp split: bop.split)

lemma sup_case_bop_case_bop_other [code_unfold]:
  fixes p :: "'a :: semilattice_sup" shows
  "sup_class.sup (case_bop cEq cNotEq cLessThan cLessOrEqual cGreaterThan cGreaterOrEqual cAdd cSubtract cMult cDiv cMod cBinAnd cBinOr cBinXor cShiftLeft cShiftRightZeros cShiftRightSigned bop)
     (sup_class.sup (case_bop cEq' cNotEq' cLessThan' cLessOrEqual' cGreaterThan' cGreaterOrEqual' cAdd' cSubtract' cMult' cDiv' cMod' cBinAnd' cBinOr' cBinXor' cShiftLeft' cShiftRightZeros' cShiftRightSigned' bop) p)
  = sup_class.sup (case_bop (sup_class.sup cEq cEq') (sup_class.sup cNotEq cNotEq') (sup_class.sup cLessThan cLessThan') (sup_class.sup cLessOrEqual cLessOrEqual') (sup_class.sup cGreaterThan cGreaterThan') (sup_class.sup cGreaterOrEqual cGreaterOrEqual') (sup_class.sup cAdd cAdd') (sup_class.sup cSubtract cSubtract') (sup_class.sup cMult cMult') (sup_class.sup cDiv cDiv') (sup_class.sup cMod cMod') (sup_class.sup cBinAnd cBinAnd') (sup_class.sup cBinOr cBinOr') (sup_class.sup cBinXor cBinXor') (sup_class.sup cShiftLeft cShiftLeft') (sup_class.sup cShiftRightZeros cShiftRightZeros') (sup_class.sup cShiftRightSigned cShiftRightSigned') bop) p"
apply(cases bop)
apply(simp_all add: inf_sup_aci sup.assoc)
done

declare op_case_bop_case_bop_same[where f="sup_class.sup", code_unfold]

end
