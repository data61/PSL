(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Expr
imports Types
begin

\<comment> \<open>type parameters:\<close>
\<comment> \<open>'val: numbers, boolean constants....\<close>
\<comment> \<open>'id: identifier names\<close>

type_synonym ('val) operation = "'val list \<Rightarrow> 'val"

datatype (dead 'id, dead 'val) Expr =
Const "'val" |
Var "'id" |
Op "'val operation" "(('id, 'val) Expr) list"


\<comment> \<open>defining a simple recursive evaluation function on this datatype\<close>
primrec ExprEval :: "(('id, 'val) Expr, 'id, 'val) Evalfunction"
and ExprEvalL :: "(('id, 'val) Expr) list \<Rightarrow> ('id, 'val) State \<Rightarrow> 'val list"
where
"ExprEval (Const v) m = v" |
"ExprEval (Var x) m = (m x)" |
"ExprEval (Op f arglist) m = (f (ExprEvalL arglist m))" |

"ExprEvalL [] m = []" |
"ExprEvalL (e#V) m = (ExprEval e m)#(ExprEvalL V m)" 

end

