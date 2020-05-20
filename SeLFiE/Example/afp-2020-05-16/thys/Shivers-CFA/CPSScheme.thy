section "Syntax"

theory CPSScheme
  imports Main
begin

text \<open>
First, we define the syntax tree of a program in our toy functional language, using continuation passing style, corresponding to section 3.2 in Shivers' dissertation.
\<close>

text \<open>
We assume that the program to be investigated is already parsed into a syntax tree. Furthermore, we assume that distinct labels were added to distinguish different code positions and that the program has been alphatised, i.e. that each variable name is only bound once. This binding position is, as a convenience, considered part of the variable name.
\<close>

type_synonym label = nat
type_synonym var = "label \<times> string"

definition "binder" :: "var \<Rightarrow> label" where [simp]: "binder v = fst v"

text \<open>
The syntax consists now of lambda abstractions, call expressions and values, which can either be lambdas, variable references, constants or primitive operations. A program is a lambda expression.

Shivers' language has as the set of basic values integers plus a special value for \textit{false}. We simplified this to just the set of integers. The conditional \<open>If\<close> considers zero as false and any other number as true.

Shivers also restricts the values in a call expression: No constant maybe be used as the called value, and no primitive operation may occur as an argument. This restriction is dropped here and just leads to runtime errors when evaluating the program.
\<close>

datatype prim = Plus label | If label label
datatype lambda = Lambda label "var list" call
     and call = App label val "val list"
              | Let label "(var \<times> lambda) list" call
     and val = L lambda | R label var | C label int | P prim

datatype_compat lambda call val

type_synonym prog = lambda

lemmas mutual_lambda_call_var_inducts =
  compat_lambda.induct
  compat_call.induct
  compat_val.induct
  compat_val_list.induct
  compat_nat_char_list_prod_lambda_prod_list.induct
  compat_nat_char_list_prod_lambda_prod.induct

text \<open>
Three example programs. These were generated using the Haskell implementation
of Shivers' algorithm that we wrote as a prototype\cite{HaskProto}.
\<close>

abbreviation "ex1 == (Lambda 1 [(1,''cont'')] (App 2 (R 3 (1,''cont'')) [(C 4 0)]))"
abbreviation "ex2 == (Lambda 1 [(1,''cont'')] (App 2 (P (Plus 3)) [(C 4 1), (C 5 1), (R 6 (1,''cont''))]))"
abbreviation "ex3 == (Lambda 1 [(1,''cont'')] (Let 2 [((2,''rec''),(Lambda 3 [(3,''p''), (3,''i''), (3,''c_'')] (App 4 (P (If 5 6)) [(R 7 (3,''i'')), (L (Lambda 8 [] (App 9 (P (Plus 10)) [(R 11 (3,''p'')), (R 12 (3,''i'')), (L (Lambda 13 [(13,''p_'')] (App 14 (P (Plus 15)) [(R 16 (3,''i'')), (C 17 (- 1)), (L (Lambda 18 [(18,''i_'')] (App 19 (R 20 (2,''rec'')) [(R 21 (13,''p_'')), (R 22 (18,''i_'')), (R 23 (3,''c_''))])))])))]))), (L (Lambda 24 [] (App 25 (R 26 (3,''c_'')) [(R 27 (3,''p''))])))])))] (App 28 (R 29 (2,''rec'')) [(C 30 0), (C 31 10), (R 32 (1,''cont''))])))"
              
end

