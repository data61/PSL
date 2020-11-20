(*  Title:       Safe OCL
    Author:      Denis Nikiforov, March 2019
    Maintainer:  Denis Nikiforov <denis.nikif at gmail.com>
    License:     LGPL
*)
chapter \<open>Normalization\<close>
theory OCL_Normalization
  imports OCL_Typing
begin

(*** Normalization Rules ****************************************************)

section \<open>Normalization Rules\<close>

text \<open>
  The following expression normalization rules includes two kinds of an
  abstract syntax tree transformations:
\begin{itemize}
\item determination of implicit types of variables, iterators, and
      tuple elements,
\item unfolding of navigation shorthands and safe navigation operators,
      described in \autoref{tab:norm_rules}.
\end{itemize}

  The following variables are used in the table:
\begin{itemize}
\item \<^verbatim>\<open>x\<close> is a non-nullable value,
\item \<^verbatim>\<open>n\<close> is a nullable value,
\item \<^verbatim>\<open>xs\<close> is a collection of non-nullable values,
\item \<^verbatim>\<open>ns\<close> is a collection of nullable values. 
\end{itemize}

\begin{table}[h!]
  \begin{center}
    \caption{Expression Normalization Rules}
    \label{tab:norm_rules}
    \begin{threeparttable}
    \begin{tabular}{c|c}
      \textbf{Orig. expr.} & \textbf{Normalized expression}\\
      \hline
      \<^verbatim>\<open>x.op()\<close> & \<^verbatim>\<open>x.op()\<close>\\
      \<^verbatim>\<open>n.op()\<close> & \<^verbatim>\<open>n.op()\<close>\tnote{*}\\
      \<^verbatim>\<open>x?.op()\<close> & ---\\
      \<^verbatim>\<open>n?.op()\<close> & \<^verbatim>\<open>if n <> null then n.oclAsType(T[1]).op() else null endif\<close>\tnote{**}\\
      \<^verbatim>\<open>x->op()\<close> & \<^verbatim>\<open>x.oclAsSet()->op()\<close>\\
      \<^verbatim>\<open>n->op()\<close> & \<^verbatim>\<open>n.oclAsSet()->op()\<close>\\
      \<^verbatim>\<open>x?->op()\<close> & ---\\
      \<^verbatim>\<open>n?->op()\<close> & ---\\
      \hline
      \<^verbatim>\<open>xs.op()\<close> & \<^verbatim>\<open>xs->collect(x | x.op())\<close>\\
      \<^verbatim>\<open>ns.op()\<close> & \<^verbatim>\<open>ns->collect(n | n.op())\<close>\tnote{*}\\
      \<^verbatim>\<open>xs?.op()\<close> & ---\\
      \<^verbatim>\<open>ns?.op()\<close> & \<^verbatim>\<open>ns->selectByKind(T[1])->collect(x | x.op())\<close>\\
      \<^verbatim>\<open>xs->op()\<close> & \<^verbatim>\<open>xs->op()\<close>\\
      \<^verbatim>\<open>ns->op()\<close> & \<^verbatim>\<open>ns->op()\<close>\\
      \<^verbatim>\<open>xs?->op()\<close> & ---\\
      \<^verbatim>\<open>ns?->op()\<close> & \<^verbatim>\<open>ns->selectByKind(T[1])->op()\<close>\\
    \end{tabular}
    \begin{tablenotes}
    \item[*] The resulting expression will be ill-typed if the operation is unsafe.
    An unsafe operation is an operation which is well-typed for
    a non-nullable source only.
    \item[**] It would be a good idea to prohibit such a transformation
    for safe operations. A safe operation is an operation which is well-typed
    for a nullable source. However, it is hard to define safe operations
    formally considering operations overloading, complex relations between
    operation parameters types (please see the typing rules for the equality
    operator), and user-defined operations.
    \end{tablenotes}
    \end{threeparttable}
  \end{center}
\end{table}

  Please take a note that name resolution of variables, types,
  attributes, and associations is out of scope of this section.
  It should be done on a previous phase during transformation
  of a concrete syntax tree to an abstract syntax tree.\<close>

fun string_of_nat :: "nat \<Rightarrow> string" where
  "string_of_nat n = (if n < 10 then [char_of (48 + n)]
      else string_of_nat (n div 10) @ [char_of (48 + (n mod 10))])"

definition "new_vname \<equiv> String.implode \<circ> string_of_nat \<circ> fcard \<circ> fmdom"

inductive normalize
    :: "('a :: ocl_object_model) type env \<Rightarrow> 'a expr \<Rightarrow> 'a expr \<Rightarrow> bool"
    ("_ \<turnstile> _ \<Rrightarrow>/ _" [51,51,51] 50) and
    normalize_call ("_ \<turnstile>\<^sub>C _ \<Rrightarrow>/ _" [51,51,51] 50) and
    normalize_expr_list ("_ \<turnstile>\<^sub>L _ \<Rrightarrow>/ _" [51,51,51] 50)
    where
 LiteralN:
  "\<Gamma> \<turnstile> Literal a \<Rrightarrow> Literal a"
|ExplicitlyTypedLetN:
  "\<Gamma> \<turnstile> init\<^sub>1 \<Rrightarrow> init\<^sub>2 \<Longrightarrow>
   \<Gamma>(v \<mapsto>\<^sub>f \<tau>) \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Let v (Some \<tau>) init\<^sub>1 body\<^sub>1 \<Rrightarrow> Let v (Some \<tau>) init\<^sub>2 body\<^sub>2"
|ImplicitlyTypedLetN:
  "\<Gamma> \<turnstile> init\<^sub>1 \<Rrightarrow> init\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E init\<^sub>2 : \<tau> \<Longrightarrow>
   \<Gamma>(v \<mapsto>\<^sub>f \<tau>) \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Let v None init\<^sub>1 body\<^sub>1 \<Rrightarrow> Let v (Some \<tau>) init\<^sub>2 body\<^sub>2"
|VarN:
  "\<Gamma> \<turnstile> Var v \<Rrightarrow> Var v"
|IfN:
  "\<Gamma> \<turnstile> a\<^sub>1 \<Rrightarrow> a\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> b\<^sub>1 \<Rrightarrow> b\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> c\<^sub>1 \<Rrightarrow> c\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> If a\<^sub>1 b\<^sub>1 c\<^sub>1 \<Rrightarrow> If a\<^sub>2 b\<^sub>2 c\<^sub>2"

|MetaOperationCallN:
  "\<Gamma> \<turnstile> MetaOperationCall \<tau> op \<Rrightarrow> MetaOperationCall \<tau> op"
|StaticOperationCallN:
  "\<Gamma> \<turnstile>\<^sub>L params\<^sub>1 \<Rrightarrow> params\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> StaticOperationCall \<tau> op params\<^sub>1 \<Rrightarrow> StaticOperationCall \<tau> op params\<^sub>2"

|OclAnyDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<le> OclAny[?] \<or> \<tau> \<le> Tuple fmempty \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 DotCall call\<^sub>1 \<Rrightarrow> Call src\<^sub>2 DotCall call\<^sub>2"
|OclAnySafeDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   OclVoid[?] \<le> \<tau> \<Longrightarrow>
   (\<Gamma>, to_required_type \<tau>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   src\<^sub>3 = TypeOperationCall src\<^sub>2 DotCall OclAsTypeOp (to_required_type \<tau>) \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 SafeDotCall call\<^sub>1 \<Rrightarrow>
       If (OperationCall src\<^sub>2 DotCall NotEqualOp [NullLiteral])
          (Call src\<^sub>3 DotCall call\<^sub>2)
          NullLiteral"
|OclAnyArrowCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   \<tau> \<le> OclAny[?] \<or> \<tau> \<le> Tuple fmempty \<Longrightarrow>
   src\<^sub>3 = OperationCall src\<^sub>2 DotCall OclAsSetOp [] \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>3 : \<sigma> \<Longrightarrow>
   (\<Gamma>, \<sigma>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 ArrowCall call\<^sub>1 \<Rrightarrow> Call src\<^sub>3 ArrowCall call\<^sub>2"

|CollectionArrowCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   element_type \<tau> _ \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 ArrowCall call\<^sub>1 \<Rrightarrow> Call src\<^sub>2 ArrowCall call\<^sub>2"
|CollectionSafeArrowCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   OclVoid[?] \<le> \<sigma> \<Longrightarrow>
   src\<^sub>3 = TypeOperationCall src\<^sub>2 ArrowCall SelectByKindOp
              (to_required_type \<sigma>) \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>3 : \<rho> \<Longrightarrow>
   (\<Gamma>, \<rho>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 SafeArrowCall call\<^sub>1 \<Rrightarrow> Call src\<^sub>3 ArrowCall call\<^sub>2"
|CollectionDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   (\<Gamma>, \<sigma>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 DotCall call\<^sub>1 \<Rrightarrow>
    CollectIteratorCall src\<^sub>2 ArrowCall [it] (Some \<sigma>) (Call (Var it) DotCall call\<^sub>2)"
|CollectionSafeDotCallN:
  "\<Gamma> \<turnstile> src\<^sub>1 \<Rrightarrow> src\<^sub>2 \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E src\<^sub>2 : \<tau> \<Longrightarrow>
   element_type \<tau> \<sigma> \<Longrightarrow>
   OclVoid[?] \<le> \<sigma> \<Longrightarrow>
   \<rho> = to_required_type \<sigma> \<Longrightarrow>
   src\<^sub>3 = TypeOperationCall src\<^sub>2 ArrowCall SelectByKindOp \<rho> \<Longrightarrow>
   (\<Gamma>, \<rho>) \<turnstile>\<^sub>C call\<^sub>1 \<Rrightarrow> call\<^sub>2 \<Longrightarrow>
   it = new_vname \<Gamma> \<Longrightarrow>
   \<Gamma> \<turnstile> Call src\<^sub>1 SafeDotCall call\<^sub>1 \<Rrightarrow>
    CollectIteratorCall src\<^sub>3 ArrowCall [it] (Some \<rho>) (Call (Var it) DotCall call\<^sub>2)"

|TypeOperationN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C TypeOperation op ty \<Rrightarrow> TypeOperation op ty"
|AttributeN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Attribute attr \<Rrightarrow> Attribute attr"
|AssociationEndN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C AssociationEnd role from \<Rrightarrow> AssociationEnd role from"
|AssociationClassN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C AssociationClass \<A> from \<Rrightarrow> AssociationClass \<A> from"
|AssociationClassEndN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C AssociationClassEnd role \<Rrightarrow> AssociationClassEnd role"
|OperationN:
  "\<Gamma> \<turnstile>\<^sub>L params\<^sub>1 \<Rrightarrow> params\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Operation op params\<^sub>1 \<Rrightarrow> Operation op params\<^sub>2"
|TupleElementN:
  "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C TupleElement elem \<Rrightarrow> TupleElement elem"

|ExplicitlyTypedIterateN:
  "\<Gamma> \<turnstile> res_init\<^sub>1 \<Rrightarrow> res_init\<^sub>2 \<Longrightarrow>
   \<Gamma> ++\<^sub>f fmap_of_list (map (\<lambda>it. (it, \<sigma>)) its) \<turnstile>
      Let res res_t\<^sub>1 res_init\<^sub>1 body\<^sub>1 \<Rrightarrow> Let res res_t\<^sub>2 res_init\<^sub>2 body\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its (Some \<sigma>) res res_t\<^sub>1 res_init\<^sub>1 body\<^sub>1 \<Rrightarrow>
      Iterate its (Some \<sigma>) res res_t\<^sub>2 res_init\<^sub>2 body\<^sub>2"
|ImplicitlyTypedIterateN:
  "element_type \<tau> \<sigma> \<Longrightarrow>
   \<Gamma> \<turnstile> res_init\<^sub>1 \<Rrightarrow> res_init\<^sub>2 \<Longrightarrow>
   \<Gamma> ++\<^sub>f fmap_of_list (map (\<lambda>it. (it, \<sigma>)) its) \<turnstile>
      Let res res_t\<^sub>1 res_init\<^sub>1 body\<^sub>1 \<Rrightarrow> Let res res_t\<^sub>2 res_init\<^sub>2 body\<^sub>2 \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its None res res_t\<^sub>1 res_init\<^sub>1 body\<^sub>1 \<Rrightarrow>
      Iterate its (Some \<sigma>) res res_t\<^sub>2 res_init\<^sub>2 body\<^sub>2"

|ExplicitlyTypedIteratorN:
  "\<Gamma> ++\<^sub>f fmap_of_list (map (\<lambda>it. (it, \<sigma>)) its) \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2  \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its (Some \<sigma>) body\<^sub>1 \<Rrightarrow> Iterator iter its (Some \<sigma>) body\<^sub>2"
|ImplicitlyTypedIteratorN:
  "element_type \<tau> \<sigma> \<Longrightarrow>
   \<Gamma> ++\<^sub>f fmap_of_list (map (\<lambda>it. (it, \<sigma>)) its) \<turnstile> body\<^sub>1 \<Rrightarrow> body\<^sub>2  \<Longrightarrow>
   (\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its None body\<^sub>1 \<Rrightarrow> Iterator iter its (Some \<sigma>) body\<^sub>2"

|ExprListNilN:
  "\<Gamma> \<turnstile>\<^sub>L [] \<Rrightarrow> []"
|ExprListConsN:
  "\<Gamma> \<turnstile> x \<Rrightarrow> y \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> ys \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>L x # xs \<Rrightarrow> y # ys"

(*** Elimination Rules ******************************************************)

section \<open>Elimination Rules\<close>

inductive_cases LiteralNE [elim]: "\<Gamma> \<turnstile> Literal a \<Rrightarrow> b"
inductive_cases LetNE [elim]: "\<Gamma> \<turnstile> Let v t init body \<Rrightarrow> b"
inductive_cases VarNE [elim]: "\<Gamma> \<turnstile> Var v \<Rrightarrow> b"
inductive_cases IfNE [elim]: "\<Gamma> \<turnstile> If a b c \<Rrightarrow> d"

inductive_cases MetaOperationCallNE [elim]: "\<Gamma> \<turnstile> MetaOperationCall \<tau> op \<Rrightarrow> b"
inductive_cases StaticOperationCallNE [elim]: "\<Gamma> \<turnstile> StaticOperationCall \<tau> op as \<Rrightarrow> b"
inductive_cases DotCallNE [elim]: "\<Gamma> \<turnstile> Call src DotCall call \<Rrightarrow> b"
inductive_cases SafeDotCallNE [elim]: "\<Gamma> \<turnstile> Call src SafeDotCall call \<Rrightarrow> b"
inductive_cases ArrowCallNE [elim]: "\<Gamma> \<turnstile> Call src ArrowCall call \<Rrightarrow> b"
inductive_cases SafeArrowCallNE [elim]: "\<Gamma> \<turnstile> Call src SafeArrowCall call \<Rrightarrow> b"

inductive_cases CallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C call \<Rrightarrow> b"
inductive_cases OperationCallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Operation op as \<Rrightarrow> call"
inductive_cases IterateCallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its its_ty res res_t res_init body \<Rrightarrow> call"
inductive_cases IteratorCallNE [elim]: "(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its its_ty body \<Rrightarrow> call"

inductive_cases ExprListNE [elim]: "\<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> ys"

(*** Simplification Rules ***************************************************)

section \<open>Simplification Rules\<close>

inductive_simps normalize_alt_simps:
"\<Gamma> \<turnstile> Literal a \<Rrightarrow> b"
"\<Gamma> \<turnstile> Let v t init body \<Rrightarrow> b"
"\<Gamma> \<turnstile> Var v \<Rrightarrow> b"
"\<Gamma> \<turnstile> If a b c \<Rrightarrow> d"

"\<Gamma> \<turnstile> MetaOperationCall \<tau> op \<Rrightarrow> b"
"\<Gamma> \<turnstile> StaticOperationCall \<tau> op as \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src DotCall call \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src SafeDotCall call \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src ArrowCall call \<Rrightarrow> b"
"\<Gamma> \<turnstile> Call src SafeArrowCall call \<Rrightarrow> b"

"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C call \<Rrightarrow> b"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Operation op as \<Rrightarrow> call"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterate its its_ty res res_t res_init body \<Rrightarrow> call"
"(\<Gamma>, \<tau>) \<turnstile>\<^sub>C Iterator iter its its_ty body \<Rrightarrow> call"

"\<Gamma> \<turnstile>\<^sub>L [] \<Rrightarrow> ys"
"\<Gamma> \<turnstile>\<^sub>L x # xs \<Rrightarrow> ys"

(*** Determinism ************************************************************)

section \<open>Determinism\<close>

lemma any_has_not_element_type:
  "element_type \<tau> \<sigma> \<Longrightarrow> \<tau> \<le> OclAny[?] \<or> \<tau> \<le> Tuple fmempty \<Longrightarrow> False"
  by (erule element_type.cases; auto)

lemma any_has_not_element_type':
  "element_type \<tau> \<sigma> \<Longrightarrow> OclVoid[?] \<le> \<tau> \<Longrightarrow> False"
  by (erule element_type.cases; auto)

lemma
  normalize_det:
    "\<Gamma> \<turnstile> expr \<Rrightarrow> expr\<^sub>1 \<Longrightarrow>
     \<Gamma> \<turnstile> expr \<Rrightarrow> expr\<^sub>2 \<Longrightarrow> expr\<^sub>1 = expr\<^sub>2" and
  normalize_call_det:
    "\<Gamma>_\<tau> \<turnstile>\<^sub>C call \<Rrightarrow> call\<^sub>1 \<Longrightarrow>
     \<Gamma>_\<tau> \<turnstile>\<^sub>C call \<Rrightarrow> call\<^sub>2 \<Longrightarrow> call\<^sub>1 = call\<^sub>2" and
  normalize_expr_list_det:
    "\<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> ys \<Longrightarrow>
     \<Gamma> \<turnstile>\<^sub>L xs \<Rrightarrow> zs \<Longrightarrow> ys = zs"
  for \<Gamma> :: "('a :: ocl_object_model) type env"
  and \<Gamma>_\<tau> :: "('a :: ocl_object_model) type env \<times> 'a type"
proof (induct arbitrary: expr\<^sub>2 and call\<^sub>2 and zs
       rule: normalize_normalize_call_normalize_expr_list.inducts)
  case (LiteralN \<Gamma> a) thus ?case by auto
next
  case (ExplicitlyTypedLetN \<Gamma> init\<^sub>1 init\<^sub>2 v \<tau> body\<^sub>1 body\<^sub>2) thus ?case
    by blast
next
  case (ImplicitlyTypedLetN \<Gamma> init\<^sub>1 init\<^sub>2 \<tau> v body\<^sub>1 body\<^sub>2) thus ?case
    by (metis (mono_tags, lifting) LetNE option.distinct(1) typing_det)
next
  case (VarN \<Gamma> v) thus ?case by auto
next
  case (IfN \<Gamma> a\<^sub>1 a\<^sub>2 b\<^sub>1 b\<^sub>2 c\<^sub>1 c\<^sub>2) thus ?case
    apply (insert IfN.prems)
    apply (erule IfNE)
    by (simp add: IfN.hyps)
next
  case (MetaOperationCallN \<Gamma> \<tau> op) thus ?case by auto
next
  case (StaticOperationCallN \<Gamma> params\<^sub>1 params\<^sub>2 \<tau> op) thus ?case by blast
next
  case (OclAnyDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> call\<^sub>1 call\<^sub>2) show ?case
    apply (insert OclAnyDotCallN.prems)
    apply (erule DotCallNE)
    using OclAnyDotCallN.hyps typing_det apply metis
    using OclAnyDotCallN.hyps any_has_not_element_type typing_det by metis
next
  case (OclAnySafeDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> call\<^sub>1 call\<^sub>2) show ?case
    apply (insert OclAnySafeDotCallN.prems)
    apply (erule SafeDotCallNE)
    using OclAnySafeDotCallN.hyps typing_det comp_apply
    apply (metis (no_types, lifting) list.simps(8) list.simps(9))
    using OclAnySafeDotCallN.hyps typing_det any_has_not_element_type'
    by metis
next
  case (OclAnyArrowCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> src\<^sub>3 \<sigma> call\<^sub>1 call\<^sub>2) show ?case
    apply (insert OclAnyArrowCallN.prems)
    apply (erule ArrowCallNE)
    using OclAnyArrowCallN.hyps typing_det comp_apply apply metis
    using OclAnyArrowCallN.hyps typing_det any_has_not_element_type
    by metis
next
  case (CollectionArrowCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> uu call\<^sub>1 call\<^sub>2) show ?case
    apply (insert CollectionArrowCallN.prems)
    apply (erule ArrowCallNE)
    using CollectionArrowCallN.hyps typing_det any_has_not_element_type
    apply metis
    using CollectionArrowCallN.hyps typing_det by metis
next
  case (CollectionSafeArrowCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> \<sigma> src\<^sub>3 \<rho> call\<^sub>1 call\<^sub>2) show ?case
    apply (insert CollectionSafeArrowCallN.prems)
    apply (erule SafeArrowCallNE)
    using CollectionSafeArrowCallN.hyps typing_det element_type_det by metis
next
  case (CollectionDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> \<sigma> call\<^sub>1 call\<^sub>2 it) show ?case
    apply (insert CollectionDotCallN.prems)
    apply (erule DotCallNE)
    using CollectionDotCallN.hyps typing_det any_has_not_element_type
    apply metis
    using CollectionDotCallN.hyps typing_det element_type_det by metis
next
  case (CollectionSafeDotCallN \<Gamma> src\<^sub>1 src\<^sub>2 \<tau> \<sigma> src\<^sub>3 call\<^sub>1 call\<^sub>2 it) show ?case
    apply (insert CollectionSafeDotCallN.prems)
    apply (erule SafeDotCallNE)
    using CollectionSafeDotCallN.hyps typing_det any_has_not_element_type'
    apply metis
    using CollectionSafeDotCallN.hyps typing_det element_type_det by metis
next
  case (TypeOperationN \<Gamma> \<tau> op ty) thus ?case by auto
next
  case (AttributeN \<Gamma> \<tau> attr) thus ?case by auto
next
  case (AssociationEndN \<Gamma> \<tau> role "from") thus ?case by auto
next
  case (AssociationClassN \<Gamma> \<tau> \<A> "from") thus ?case by auto
next
  case (AssociationClassEndN \<Gamma> \<tau> role) thus ?case by auto
next
  case (OperationN \<Gamma> params\<^sub>1 params\<^sub>2 \<tau> op) thus ?case by blast
next
  case (TupleElementN \<Gamma> \<tau> elem) thus ?case by auto
next
  case (ExplicitlyTypedIterateN
    \<Gamma> res_init\<^sub>1 res_init\<^sub>2 \<sigma> its res res_t\<^sub>1 body\<^sub>1 res_t\<^sub>2 body\<^sub>2 \<tau>)
  show ?case
    apply (insert ExplicitlyTypedIterateN.prems)
    apply (erule IterateCallNE)
    using ExplicitlyTypedIterateN.hyps element_type_det by blast+
next
  case (ImplicitlyTypedIterateN
    \<tau> \<sigma> \<Gamma> res_init\<^sub>1 res_init\<^sub>2 its res res_t\<^sub>1 body\<^sub>1 res_t\<^sub>2 body\<^sub>2)
  show ?case
    apply (insert ImplicitlyTypedIterateN.prems)
    apply (erule IterateCallNE)
    using ImplicitlyTypedIterateN.hyps element_type_det by blast+
next
  case (ExplicitlyTypedIteratorN \<Gamma> \<sigma> its body\<^sub>1 body\<^sub>2 \<tau> iter)
  show ?case
    apply (insert ExplicitlyTypedIteratorN.prems)
    apply (erule IteratorCallNE)
    using ExplicitlyTypedIteratorN.hyps element_type_det by blast+
next
  case (ImplicitlyTypedIteratorN \<tau> \<sigma> \<Gamma> its body\<^sub>1 body\<^sub>2 iter)
  show ?case
    apply (insert ImplicitlyTypedIteratorN.prems)
    apply (erule IteratorCallNE)
    using ImplicitlyTypedIteratorN.hyps element_type_det by blast+
next
  case (ExprListNilN \<Gamma>) thus ?case
    using normalize_expr_list.cases by auto
next
  case (ExprListConsN \<Gamma> x y xs ys) thus ?case by blast
qed

(*** Normalized Expressions Typing ******************************************)

section \<open>Normalized Expressions Typing\<close>

text \<open>
  Here is the final typing rules.\<close>

inductive nf_typing ("(1_/ \<turnstile>/ (_ :/ _))" [51,51,51] 50) where
  "\<Gamma> \<turnstile> expr \<Rrightarrow> expr\<^sub>N \<Longrightarrow>
   \<Gamma> \<turnstile>\<^sub>E expr\<^sub>N : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> expr : \<tau>"

lemma nf_typing_det:
  "\<Gamma> \<turnstile> expr : \<tau> \<Longrightarrow>
   \<Gamma> \<turnstile> expr : \<sigma> \<Longrightarrow> \<tau> = \<sigma>"
  by (metis nf_typing.cases normalize_det typing_det)

(*** Code Setup *************************************************************)

section \<open>Code Setup\<close>

code_pred normalize .

code_pred nf_typing .

definition "check_type \<Gamma> expr \<tau> \<equiv>
  Predicate.eval (nf_typing_i_i_i \<Gamma> expr \<tau>) ()"

definition "synthesize_type \<Gamma> expr \<equiv>
  Predicate.singleton (\<lambda>_. OclInvalid)
    (Predicate.map errorable (nf_typing_i_i_o \<Gamma> expr))"

text \<open>
  It is the only usage of the @{text OclInvalid} type.
  This type is not required to define typing rules.
  It is only required to make the typing function total.\<close>

end
