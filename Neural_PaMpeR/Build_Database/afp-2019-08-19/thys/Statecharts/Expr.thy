(*  Title:      statecharts/SA/Expr.thy

    Author:     Steffen Helke, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)

section \<open>Label Expressions\<close>
theory Expr
imports Update
begin

datatype ('s,'e)expr = true
                        | In 's
                        | En 'e
                        | NOT "('s,'e)expr"
                        | And "('s,'e)expr" "('s,'e)expr"
                        | Or  "('s,'e)expr" "('s,'e)expr"
 
type_synonym 'd guard = "('d data) => bool"
type_synonym ('e,'d)action = "('e set * 'd pupdate)"
type_synonym ('s,'e,'d)label = "(('s,'e)expr * 'd guard * ('e,'d)action)"
type_synonym ('s,'e,'d)trans = "('s * ('s,'e,'d)label * 's)"

primrec
   eval_expr :: "[('s set * 'e set), ('s,'e)expr] \<Rightarrow> bool" where 
     "eval_expr sc true          = True"
   | "eval_expr sc (En ev)       = (ev \<in> snd sc)"
   | "eval_expr sc (In st)       = (st \<in> fst sc)"
   | "eval_expr sc (NOT e1)      = (\<not> (eval_expr sc e1))"
   | "eval_expr sc (And e1 e2)   = ((eval_expr sc e1) \<and> (eval_expr sc e2))"
   | "eval_expr sc (Or  e1 e2)   = ((eval_expr sc e1) \<or> (eval_expr sc e2))"

primrec
   ExprEvents :: "('s,'e)expr \<Rightarrow> 'e set" where
      "ExprEvents true        = {}"
   |  "ExprEvents (En ev)     = {ev}"
   |  "ExprEvents (In st)     = {}"
   |  "ExprEvents (NOT e)     = (ExprEvents e)"
   |  "ExprEvents (And e1 e2) = ((ExprEvents e1) \<union> (ExprEvents e2))"
   |  "ExprEvents (Or  e1 e2) = ((ExprEvents e1) \<union> (ExprEvents e2))"

(* atomar propositions for Sequential Automata, will be necessary for CTL-interpretation *)

datatype ('s, 'e, dead 'd)atomar =
                          TRUE
                          | FALSE
                          | IN 's
                          | EN 'e
                          | VAL "'d data => bool"

definition
  source     :: "('s,'e,'d)trans => 's" where
  "source t  = fst t"

definition
   Source     :: "('s,'e,'d)trans set => 's set" where
  "Source T == source ` T"

definition
   target     :: "('s,'e,'d)trans => 's" where
  "target t  = snd(snd t)"

definition
   Target     :: "('s,'e,'d)trans set => 's set" where
  "Target T = target ` T"

definition
   label      :: "('s,'e,'d)trans => ('s,'e,'d)label" where
  "label t  = fst (snd t)"

definition
   Label      :: "('s,'e,'d)trans set => ('s,'e,'d)label set" where
  "Label T = label ` T"

definition
   expr       :: "('s,'e,'d)label => ('s,'e)expr" where
  "expr  = fst"

definition
   action     :: "('s,'e,'d)label  => ('e,'d)action" where
  "action = snd o snd"

definition
   Action     :: "('s,'e,'d)label set => ('e,'d)action set" where
  "Action L = action ` L"

definition
   pupdate     :: "('s,'e,'d)label => 'd pupdate" where
  "pupdate   = snd o action"

definition
  PUpdate     :: "('s,'e,'d)label set => ('d pupdate) set" where
  "PUpdate L = pupdate ` L"

definition
   actevent   :: "('s,'e,'d)label => 'e set" where
  "actevent  = fst o action"

definition
   Actevent   :: "('s,'e,'d)label set => ('e set) set" where
  "Actevent L = actevent ` L"

definition
   guard      :: "('s,'e,'d)label  => 'd guard" where  
  "guard = fst o snd"

definition
   Guard      :: "('s,'e,'d)label set => ('d guard) set" where
  "Guard L = guard ` L"

definition
   defaultexpr :: "('s,'e)expr" where 
  "defaultexpr = true"

definition
   defaultaction :: "('e,'d)action" where
  "defaultaction = ({},DefaultPUpdate)"

definition
   defaultguard :: "('d guard)" where
  "defaultguard = (\<lambda> d. True)"

definition
   defaultlabel :: "('s,'e,'d)label" where
  "defaultlabel = (defaultexpr, defaultguard, defaultaction)"

definition
   eval :: "[('s set * 'e set * 'd data), ('s,'e,'d)label] => bool"
                                                       ("_ |= _" [91,90]90) where
  "eval scd l = (let (s,e,d) = scd
                 in
                    ((eval_expr (s,e) (expr l)) \<and> ((guard l) d)))"

lemma Source_EmptySet [simp]:
 "Source {} = {}"
by (unfold Source_def, auto)

lemma Target_EmptySet [simp]:
 "Target {} = {}"
by (unfold Target_def, auto)

lemma Label_EmptySet [simp]:
 "Label {} = {}"
by (unfold Label_def, auto)

lemma Action_EmptySet [simp]:
 "Action {} = {}"
by (unfold Action_def, auto)

lemma PUpdate_EmptySet [simp]:
 "PUpdate {} = {}"
by (unfold PUpdate_def, auto)

lemma Actevent_EmptySet [simp]:
 "Actevent {} = {}"
by (unfold Actevent_def, auto)

lemma Union_Actevent_subset:
  "\<lbrakk> m \<in> M; ((\<Union> (Actevent (Label (Union M)))) \<subseteq> (N::'a set)) \<rbrakk> \<Longrightarrow>
   ((\<Union> (Actevent (Label m))) \<subseteq> N)"
by (unfold Actevent_def Label_def, auto)

lemma action_select [simp]:
 "action (a,b,c) = c"
by (unfold action_def, auto)

lemma label_select [simp]:
 "label (a,b,c) = b"
by (unfold label_def, auto)

lemma target_select [simp]:
 "target (a,b,c) = c"
by (unfold target_def, auto)

lemma actevent_select [simp]:
 "actevent (a,b,(c,d)) = c"
by (unfold actevent_def, auto)

lemma pupdate_select [simp]:
 "pupdate (a,b,c,d) = d"
by (unfold pupdate_def, auto)

lemma source_select [simp]:
 "source (a,b) = a"
by (unfold source_def, auto)

lemma finite_PUpdate [simp]:
 "finite S \<Longrightarrow> finite(PUpdate S)"
by (unfold PUpdate_def, auto)

lemma finite_Label [simp]:
 "finite S \<Longrightarrow> finite(Label S)"
by (unfold Label_def, auto)

lemma fst_defaultaction [simp]:
 "fst defaultaction = {}" 
by (unfold defaultaction_def, auto)

lemma action_defaultlabel [simp]:
 "(action defaultlabel) = defaultaction" 
by (unfold defaultlabel_def action_def, auto)

lemma fst_defaultlabel [simp]:
 "(fst defaultlabel) = defaultexpr" 
by (unfold defaultlabel_def, auto)

lemma ExprEvents_defaultexpr [simp]:
 "(ExprEvents defaultexpr) = {}" 
by (unfold defaultexpr_def, auto)

lemma defaultlabel_defaultexpr [simp]:
 "expr defaultlabel = defaultexpr"
by (unfold defaultlabel_def expr_def, auto)

lemma target_Target [simp]:
  "t \<in> T \<Longrightarrow> target t \<in> Target T"
by (unfold Target_def, auto)

lemma Source_union : "Source s \<union> Source t = Source (s \<union> t)"
apply (unfold Source_def)
apply auto
done

lemma Target_union : "Target s \<union> Target t = Target (s \<union> t)"
apply (unfold Target_def)
apply auto
done

end
