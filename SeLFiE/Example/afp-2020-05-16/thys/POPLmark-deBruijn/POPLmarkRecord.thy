(*  Title:      POPLmark/POPLmarkRecord.thy
    Author:     Stefan Berghofer, TU Muenchen, 2005
*)

theory POPLmarkRecord
imports Basis
begin

section \<open>Extending the calculus with records\<close>

text \<open>
\label{sec:record-calculus}
We now describe how the calculus introduced in the previous section can
be extended with records. An important point to note is that many of the
definitions and proofs developed for the simple calculus can be reused.
\<close>


subsection \<open>Types and Terms\<close>

text \<open>
In order to represent records, we also need a type of {\it field names}.
For this purpose, we simply use the type of {\it strings}. We extend the
datatype of types of System \fsub{} by a new constructor \<open>RcdT\<close>
representing record types.
\<close>

type_synonym name = string

datatype type =
    TVar nat
  | Top
  | Fun type type    (infixr "\<rightarrow>" 200)
  | TyAll type type  ("(3\<forall><:_./ _)" [0, 10] 10)
  | RcdT "(name \<times> type) list"

type_synonym fldT = "name \<times> type"
type_synonym rcdT = "(name \<times> type) list"

datatype binding = VarB type | TVarB type

type_synonym env = "binding list"

primrec is_TVarB :: "binding \<Rightarrow> bool"
where
  "is_TVarB (VarB T) = False"
| "is_TVarB (TVarB T) = True"

primrec type_ofB :: "binding \<Rightarrow> type"
where
  "type_ofB (VarB T) = T"
| "type_ofB (TVarB T) = T"

primrec mapB :: "(type \<Rightarrow> type) \<Rightarrow> binding \<Rightarrow> binding"
where
  "mapB f (VarB T) = VarB (f T)"
| "mapB f (TVarB T) = TVarB (f T)"

text \<open>
A record type is essentially an association list, mapping names of record fields
to their types.
The types of bindings and environments remain unchanged. The datatype \<open>trm\<close>
of terms is extended with three new constructors \<open>Rcd\<close>, \<open>Proj\<close>,
and \<open>LET\<close>, denoting construction of a new record, selection of
a specific field of a record (projection), and matching of a record against
a pattern, respectively. A pattern, represented by datatype \<open>pat\<close>,
can be either a variable matching any value of a given type, or a nested
record pattern. Due to the encoding of variables using de Bruijn indices,
a variable pattern only consists of a type.
\<close>

datatype pat = PVar type | PRcd "(name \<times> pat) list"

datatype trm =
    Var nat
  | Abs type trm   ("(3\<lambda>:_./ _)" [0, 10] 10)
  | TAbs type trm  ("(3\<lambda><:_./ _)" [0, 10] 10)
  | App trm trm    (infixl "\<bullet>" 200)
  | TApp trm type  (infixl "\<bullet>\<^sub>\<tau>" 200)
  | Rcd "(name \<times> trm) list"
  | Proj trm name  ("(_.._)" [90, 91] 90)
  | LET pat trm trm ("(LET (_ =/ _)/ IN (_))" 10)

type_synonym fld = "name \<times> trm"
type_synonym rcd = "(name \<times> trm) list"
type_synonym fpat = "name \<times> pat"
type_synonym rpat = "(name \<times> pat) list"

text \<open>
In order to motivate the typing and evaluation rules for the \<open>LET\<close>, it is
important to note that an expression of the form
@{text [display] "LET PRcd [(l\<^sub>1, PVar T\<^sub>1), \<dots>, (l\<^sub>n, PVar T\<^sub>n)] = Rcd [(l\<^sub>1, v\<^sub>1), \<dots>, (l\<^sub>n, v\<^sub>n)] IN t"}
can be treated like a nested abstraction \<open>(\<lambda>:T\<^sub>1. \<dots> \<lambda>:T\<^sub>n. t) \<bullet> v\<^sub>1 \<bullet> \<dots> \<bullet> v\<^sub>n\<close>
\<close>


subsection \<open>Lifting and Substitution\<close>

primrec psize :: "pat \<Rightarrow> nat" ("\<parallel>_\<parallel>\<^sub>p")
  and rsize :: "rpat \<Rightarrow> nat" ("\<parallel>_\<parallel>\<^sub>r")
  and fsize :: "fpat \<Rightarrow> nat" ("\<parallel>_\<parallel>\<^sub>f")
where
  "\<parallel>PVar T\<parallel>\<^sub>p = 1"
| "\<parallel>PRcd fs\<parallel>\<^sub>p = \<parallel>fs\<parallel>\<^sub>r"
| "\<parallel>[]\<parallel>\<^sub>r = 0"
| "\<parallel>f \<Colon> fs\<parallel>\<^sub>r = \<parallel>f\<parallel>\<^sub>f + \<parallel>fs\<parallel>\<^sub>r"
| "\<parallel>(l, p)\<parallel>\<^sub>f = \<parallel>p\<parallel>\<^sub>p"

primrec liftT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type" ("\<up>\<^sub>\<tau>")
  and liftrT :: "nat \<Rightarrow> nat \<Rightarrow> rcdT \<Rightarrow> rcdT" ("\<up>\<^sub>r\<^sub>\<tau>")
  and liftfT :: "nat \<Rightarrow> nat \<Rightarrow> fldT \<Rightarrow> fldT" ("\<up>\<^sub>f\<^sub>\<tau>")
where
  "\<up>\<^sub>\<tau> n k (TVar i) = (if i < k then TVar i else TVar (i + n))"
| "\<up>\<^sub>\<tau> n k Top = Top"
| "\<up>\<^sub>\<tau> n k (T \<rightarrow> U) = \<up>\<^sub>\<tau> n k T \<rightarrow> \<up>\<^sub>\<tau> n k U"
| "\<up>\<^sub>\<tau> n k (\<forall><:T. U) = (\<forall><:\<up>\<^sub>\<tau> n k T. \<up>\<^sub>\<tau> n (k + 1) U)"
| "\<up>\<^sub>\<tau> n k (RcdT fs) = RcdT (\<up>\<^sub>r\<^sub>\<tau> n k fs)"
| "\<up>\<^sub>r\<^sub>\<tau> n k [] = []"
| "\<up>\<^sub>r\<^sub>\<tau> n k (f \<Colon> fs) = \<up>\<^sub>f\<^sub>\<tau> n k f \<Colon> \<up>\<^sub>r\<^sub>\<tau> n k fs"
| "\<up>\<^sub>f\<^sub>\<tau> n k (l, T) = (l, \<up>\<^sub>\<tau> n k T)"

primrec liftp :: "nat \<Rightarrow> nat \<Rightarrow> pat \<Rightarrow> pat" ("\<up>\<^sub>p")
  and liftrp :: "nat \<Rightarrow> nat \<Rightarrow> rpat \<Rightarrow> rpat" ("\<up>\<^sub>r\<^sub>p")
  and liftfp :: "nat \<Rightarrow> nat \<Rightarrow> fpat \<Rightarrow> fpat" ("\<up>\<^sub>f\<^sub>p")
where
  "\<up>\<^sub>p n k (PVar T) = PVar (\<up>\<^sub>\<tau> n k T)"
| "\<up>\<^sub>p n k (PRcd fs) = PRcd (\<up>\<^sub>r\<^sub>p n k fs)"
| "\<up>\<^sub>r\<^sub>p n k [] = []"
| "\<up>\<^sub>r\<^sub>p n k (f \<Colon> fs) = \<up>\<^sub>f\<^sub>p n k f \<Colon> \<up>\<^sub>r\<^sub>p n k fs"
| "\<up>\<^sub>f\<^sub>p n k (l, p) = (l, \<up>\<^sub>p n k p)"

primrec lift :: "nat \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm" ("\<up>")
  and liftr :: "nat \<Rightarrow> nat \<Rightarrow> rcd \<Rightarrow> rcd" ("\<up>\<^sub>r")
  and liftf :: "nat \<Rightarrow> nat \<Rightarrow> fld \<Rightarrow> fld" ("\<up>\<^sub>f")
where
  "\<up> n k (Var i) = (if i < k then Var i else Var (i + n))"
| "\<up> n k (\<lambda>:T. t) = (\<lambda>:\<up>\<^sub>\<tau> n k T. \<up> n (k + 1) t)"
| "\<up> n k (\<lambda><:T. t) = (\<lambda><:\<up>\<^sub>\<tau> n k T. \<up> n (k + 1) t)"
| "\<up> n k (s \<bullet> t) = \<up> n k s \<bullet> \<up> n k t"
| "\<up> n k (t \<bullet>\<^sub>\<tau> T) = \<up> n k t \<bullet>\<^sub>\<tau> \<up>\<^sub>\<tau> n k T"
| "\<up> n k (Rcd fs) = Rcd (\<up>\<^sub>r n k fs)"
| "\<up> n k (t..a) = (\<up> n k t)..a"
| "\<up> n k (LET p = t IN u) = (LET \<up>\<^sub>p n k p = \<up> n k t IN \<up> n (k + \<parallel>p\<parallel>\<^sub>p) u)"
| "\<up>\<^sub>r n k [] = []"
| "\<up>\<^sub>r n k (f \<Colon> fs) = \<up>\<^sub>f n k f \<Colon> \<up>\<^sub>r n k fs"
| "\<up>\<^sub>f n k (l, t) = (l, \<up> n k t)"

primrec substTT :: "type \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>\<tau>" [300, 0, 0] 300)
  and substrTT :: "rcdT \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> rcdT"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>r\<^sub>\<tau>" [300, 0, 0] 300)
  and substfTT :: "fldT \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> fldT"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>f\<^sub>\<tau>" [300, 0, 0] 300)
where
  "(TVar i)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> =
     (if k < i then TVar (i - 1) else if i = k then \<up>\<^sub>\<tau> k 0 S else TVar i)"
| "Top[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = Top"
| "(T \<rightarrow> U)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> \<rightarrow> U[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>"
| "(\<forall><:T. U)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = (\<forall><:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. U[k+1 \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>)"
| "(RcdT fs)[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau> = RcdT (fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>\<tau>)"
| "[][k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>\<tau> = []"
| "(f \<Colon> fs)[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>\<tau> = f[k \<mapsto>\<^sub>\<tau> S]\<^sub>f\<^sub>\<tau> \<Colon> fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>\<tau>"
| "(l, T)[k \<mapsto>\<^sub>\<tau> S]\<^sub>f\<^sub>\<tau> = (l, T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>)"

primrec substpT :: "pat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> pat"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>p" [300, 0, 0] 300)
  and substrpT :: "rpat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> rpat"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>r\<^sub>p" [300, 0, 0] 300)
  and substfpT :: "fpat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> fpat"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>f\<^sub>p" [300, 0, 0] 300)
where
  "(PVar T)[k \<mapsto>\<^sub>\<tau> S]\<^sub>p = PVar (T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>)"
| "(PRcd fs)[k \<mapsto>\<^sub>\<tau> S]\<^sub>p = PRcd (fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>p)"
| "[][k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>p = []"
| "(f \<Colon> fs)[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>p = f[k \<mapsto>\<^sub>\<tau> S]\<^sub>f\<^sub>p \<Colon> fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r\<^sub>p"
| "(l, p)[k \<mapsto>\<^sub>\<tau> S]\<^sub>f\<^sub>p = (l, p[k \<mapsto>\<^sub>\<tau> S]\<^sub>p)"

primrec decp :: "nat \<Rightarrow> nat \<Rightarrow> pat \<Rightarrow> pat"  ("\<down>\<^sub>p")
where
  "\<down>\<^sub>p 0 k p = p"
| "\<down>\<^sub>p (Suc n) k p = \<down>\<^sub>p n k (p[k \<mapsto>\<^sub>\<tau> Top]\<^sub>p)"

text \<open>
In addition to the lifting and substitution functions already needed for the
basic calculus, we also have to define lifting and substitution functions
for patterns, which we denote by @{term "\<up>\<^sub>p n k p"} and @{term "T[k \<mapsto>\<^sub>\<tau> S]\<^sub>p"},
respectively. The extension of the existing lifting and substitution
functions to records is fairly standard.
\<close>

primrec subst :: "trm \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> trm"  ("_[_ \<mapsto> _]" [300, 0, 0] 300)
  and substr :: "rcd \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> rcd"  ("_[_ \<mapsto> _]\<^sub>r" [300, 0, 0] 300)
  and substf :: "fld \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> fld"  ("_[_ \<mapsto> _]\<^sub>f" [300, 0, 0] 300)
where
  "(Var i)[k \<mapsto> s] =
     (if k < i then Var (i - 1) else if i = k then \<up> k 0 s else Var i)"
| "(t \<bullet> u)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet> u[k \<mapsto> s]"
| "(t \<bullet>\<^sub>\<tau> T)[k \<mapsto> s] = t[k \<mapsto> s] \<bullet>\<^sub>\<tau> T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
| "(\<lambda>:T. t)[k \<mapsto> s] = (\<lambda>:T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>. t[k+1 \<mapsto> s])"
| "(\<lambda><:T. t)[k \<mapsto> s] = (\<lambda><:T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>. t[k+1 \<mapsto> s])"
| "(Rcd fs)[k \<mapsto> s] = Rcd (fs[k \<mapsto> s]\<^sub>r)"
| "(t..a)[k \<mapsto> s] = (t[k \<mapsto> s])..a"
| "(LET p = t IN u)[k \<mapsto> s] = (LET \<down>\<^sub>p 1 k p = t[k \<mapsto> s] IN u[k + \<parallel>p\<parallel>\<^sub>p \<mapsto> s])"
| "[][k \<mapsto> s]\<^sub>r = []"
| "(f \<Colon> fs)[k \<mapsto> s]\<^sub>r = f[k \<mapsto> s]\<^sub>f \<Colon> fs[k \<mapsto> s]\<^sub>r"
| "(l, t)[k \<mapsto> s]\<^sub>f = (l, t[k \<mapsto> s])"

text \<open>
Note that the substitution function on terms is defined simultaneously
with a substitution function @{term "fs[k \<mapsto> s]\<^sub>r"} on records (i.e.\ lists
of fields), and a substitution function @{term "f[k \<mapsto> s]\<^sub>f"} on fields.
To avoid conflicts with locally bound variables, we have to add an offset
@{term "\<parallel>p\<parallel>\<^sub>p"} to @{term k} when performing substitution in the body of
the \<open>LET\<close> binder, where @{term "\<parallel>p\<parallel>\<^sub>p"} is the number of variables
in the pattern @{term p}.
\<close>

primrec substT :: "trm \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> trm"  ("_[_ \<mapsto>\<^sub>\<tau> _]" [300, 0, 0] 300)
  and substrT :: "rcd \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> rcd"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>r" [300, 0, 0] 300)
  and substfT :: "fld \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> fld"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>f" [300, 0, 0] 300)
where
  "(Var i)[k \<mapsto>\<^sub>\<tau> S] = (if k < i then Var (i - 1) else Var i)"
| "(t \<bullet> u)[k \<mapsto>\<^sub>\<tau> S] = t[k \<mapsto>\<^sub>\<tau> S] \<bullet> u[k \<mapsto>\<^sub>\<tau> S]"
| "(t \<bullet>\<^sub>\<tau> T)[k \<mapsto>\<^sub>\<tau> S] = t[k \<mapsto>\<^sub>\<tau> S] \<bullet>\<^sub>\<tau> T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>"
| "(\<lambda>:T. t)[k \<mapsto>\<^sub>\<tau> S] = (\<lambda>:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. t[k+1 \<mapsto>\<^sub>\<tau> S])"
| "(\<lambda><:T. t)[k \<mapsto>\<^sub>\<tau> S] = (\<lambda><:T[k \<mapsto>\<^sub>\<tau> S]\<^sub>\<tau>. t[k+1 \<mapsto>\<^sub>\<tau> S])"
| "(Rcd fs)[k \<mapsto>\<^sub>\<tau> S] = Rcd (fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r)"
| "(t..a)[k \<mapsto>\<^sub>\<tau> S] = (t[k \<mapsto>\<^sub>\<tau> S])..a"
| "(LET p = t IN u)[k \<mapsto>\<^sub>\<tau> S] =
     (LET p[k \<mapsto>\<^sub>\<tau> S]\<^sub>p = t[k \<mapsto>\<^sub>\<tau> S] IN u[k + \<parallel>p\<parallel>\<^sub>p \<mapsto>\<^sub>\<tau> S])"
| "[][k \<mapsto>\<^sub>\<tau> S]\<^sub>r = []"
| "(f \<Colon> fs)[k \<mapsto>\<^sub>\<tau> S]\<^sub>r = f[k \<mapsto>\<^sub>\<tau> S]\<^sub>f \<Colon> fs[k \<mapsto>\<^sub>\<tau> S]\<^sub>r"
| "(l, t)[k \<mapsto>\<^sub>\<tau> S]\<^sub>f = (l, t[k \<mapsto>\<^sub>\<tau> S])"

primrec liftE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env" ("\<up>\<^sub>e")
where
  "\<up>\<^sub>e n k [] = []"
| "\<up>\<^sub>e n k (B \<Colon> \<Gamma>) = mapB (\<up>\<^sub>\<tau> n (k + \<parallel>\<Gamma>\<parallel>)) B \<Colon> \<up>\<^sub>e n k \<Gamma>"

primrec substE :: "env \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> env"  ("_[_ \<mapsto>\<^sub>\<tau> _]\<^sub>e" [300, 0, 0] 300)
where
  "[][k \<mapsto>\<^sub>\<tau> T]\<^sub>e = []"
| "(B \<Colon> \<Gamma>)[k \<mapsto>\<^sub>\<tau> T]\<^sub>e = mapB (\<lambda>U. U[k + \<parallel>\<Gamma>\<parallel> \<mapsto>\<^sub>\<tau> T]\<^sub>\<tau>) B \<Colon> \<Gamma>[k \<mapsto>\<^sub>\<tau> T]\<^sub>e"

text \<open>
For the formalization of the reduction
rules for \<open>LET\<close>, we need a function \mbox{\<open>t[k \<mapsto>\<^sub>s us]\<close>}
for simultaneously substituting terms @{term us} for variables with
consecutive indices:
\<close>

primrec substs :: "trm \<Rightarrow> nat \<Rightarrow> trm list \<Rightarrow> trm"  ("_[_ \<mapsto>\<^sub>s _]" [300, 0, 0] 300)
where
  "t[k \<mapsto>\<^sub>s []] = t"
| "t[k \<mapsto>\<^sub>s u \<Colon> us] = t[k + \<parallel>us\<parallel> \<mapsto> u][k \<mapsto>\<^sub>s us]"

primrec decT :: "nat \<Rightarrow> nat \<Rightarrow> type \<Rightarrow> type"  ("\<down>\<^sub>\<tau>")
where
  "\<down>\<^sub>\<tau> 0 k T = T"
| "\<down>\<^sub>\<tau> (Suc n) k T = \<down>\<^sub>\<tau> n k (T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>)"

primrec decE :: "nat \<Rightarrow> nat \<Rightarrow> env \<Rightarrow> env"  ("\<down>\<^sub>e")
where
  "\<down>\<^sub>e 0 k \<Gamma> = \<Gamma>"
| "\<down>\<^sub>e (Suc n) k \<Gamma> = \<down>\<^sub>e n k (\<Gamma>[k \<mapsto>\<^sub>\<tau> Top]\<^sub>e)"

primrec decrT :: "nat \<Rightarrow> nat \<Rightarrow> rcdT \<Rightarrow> rcdT"  ("\<down>\<^sub>r\<^sub>\<tau>")
where
  "\<down>\<^sub>r\<^sub>\<tau> 0 k fTs = fTs"
| "\<down>\<^sub>r\<^sub>\<tau> (Suc n) k fTs = \<down>\<^sub>r\<^sub>\<tau> n k (fTs[k \<mapsto>\<^sub>\<tau> Top]\<^sub>r\<^sub>\<tau>)"

text \<open>
The lemmas about substitution and lifting are very similar to those needed
for the simple calculus without records, with the difference that most
of them have to be proved simultaneously with a suitable property for
records.
\<close>

lemma liftE_length [simp]: "\<parallel>\<up>\<^sub>e n k \<Gamma>\<parallel> = \<parallel>\<Gamma>\<parallel>"
  by (induct \<Gamma>) simp_all

lemma substE_length [simp]: "\<parallel>\<Gamma>[k \<mapsto>\<^sub>\<tau> U]\<^sub>e\<parallel> = \<parallel>\<Gamma>\<parallel>"
  by (induct \<Gamma>) simp_all

lemma liftE_nth [simp]:
  "(\<up>\<^sub>e n k \<Gamma>)\<langle>i\<rangle> = map_option (mapB (\<up>\<^sub>\<tau> n (k + \<parallel>\<Gamma>\<parallel> - i - 1))) (\<Gamma>\<langle>i\<rangle>)"
  apply (induct \<Gamma> arbitrary: i)
  apply simp
  apply simp
  apply (case_tac i)
  apply simp
  apply simp
  done

lemma substE_nth [simp]:
  "(\<Gamma>[0 \<mapsto>\<^sub>\<tau> T]\<^sub>e)\<langle>i\<rangle> = map_option (mapB (\<lambda>U. U[\<parallel>\<Gamma>\<parallel> - i - 1 \<mapsto>\<^sub>\<tau> T]\<^sub>\<tau>)) (\<Gamma>\<langle>i\<rangle>)"
  apply (induct \<Gamma> arbitrary: i)
  apply simp
  apply simp
  apply (case_tac i)
  apply simp
  apply simp
  done

lemma liftT_liftT [simp]:
  "i \<le> j \<Longrightarrow> j \<le> i + m \<Longrightarrow> \<up>\<^sub>\<tau> n j (\<up>\<^sub>\<tau> m i T) = \<up>\<^sub>\<tau> (m + n) i T"
  "i \<le> j \<Longrightarrow> j \<le> i + m \<Longrightarrow> \<up>\<^sub>r\<^sub>\<tau> n j (\<up>\<^sub>r\<^sub>\<tau> m i rT) = \<up>\<^sub>r\<^sub>\<tau> (m + n) i rT"
  "i \<le> j \<Longrightarrow> j \<le> i + m \<Longrightarrow> \<up>\<^sub>f\<^sub>\<tau> n j (\<up>\<^sub>f\<^sub>\<tau> m i fT) = \<up>\<^sub>f\<^sub>\<tau> (m + n) i fT"
  by (induct T and rT and fT arbitrary: i j m n and i j m n and i j m n
    rule: liftT.induct liftrT.induct liftfT.induct) simp_all

lemma liftT_liftT' [simp]:
  "i + m \<le> j \<Longrightarrow> \<up>\<^sub>\<tau> n j (\<up>\<^sub>\<tau> m i T) = \<up>\<^sub>\<tau> m i (\<up>\<^sub>\<tau> n (j - m) T)"
  "i + m \<le> j \<Longrightarrow> \<up>\<^sub>r\<^sub>\<tau> n j (\<up>\<^sub>r\<^sub>\<tau> m i rT) = \<up>\<^sub>r\<^sub>\<tau> m i (\<up>\<^sub>r\<^sub>\<tau> n (j - m) rT)"
  "i + m \<le> j \<Longrightarrow> \<up>\<^sub>f\<^sub>\<tau> n j (\<up>\<^sub>f\<^sub>\<tau> m i fT) = \<up>\<^sub>f\<^sub>\<tau> m i (\<up>\<^sub>f\<^sub>\<tau> n (j - m) fT)"
  apply (induct T and rT and fT arbitrary: i j m n and i j m n and i j m n
    rule: liftT.induct liftrT.induct liftfT.induct)
  apply simp_all
  apply arith
  apply (subgoal_tac "Suc j - m = Suc (j - m)")
  apply simp
  apply arith
  done

lemma lift_size [simp]:
  "size (\<up>\<^sub>\<tau> n k T) = size T"
  "size_list (size_prod (\<lambda>x. 0) size) (\<up>\<^sub>r\<^sub>\<tau> n k rT) = size_list (size_prod (\<lambda>x. 0) size) rT"
  "size_prod (\<lambda>x. 0) size (\<up>\<^sub>f\<^sub>\<tau> n k fT) = size_prod (\<lambda>x. 0) size fT"
  by (induct T and rT and fT arbitrary: k and k and k
    rule: liftT.induct liftrT.induct liftfT.induct) simp_all

lemma liftT0 [simp]:
  "\<up>\<^sub>\<tau> 0 i T = T"
  "\<up>\<^sub>r\<^sub>\<tau> 0 i rT = rT"
  "\<up>\<^sub>f\<^sub>\<tau> 0 i fT = fT"
  by (induct T and rT and fT arbitrary: i and i and i
    rule: liftT.induct liftrT.induct liftfT.induct) simp_all

lemma liftp0 [simp]:
  "\<up>\<^sub>p 0 i p = p"
  "\<up>\<^sub>r\<^sub>p 0 i fs = fs"
  "\<up>\<^sub>f\<^sub>p 0 i f = f"
  by (induct p and fs and f arbitrary: i and i and i
    rule: liftp.induct liftrp.induct liftfp.induct) simp_all

lemma lift0 [simp]:
  "\<up> 0 i t = t"
  "\<up>\<^sub>r 0 i fs = fs"
  "\<up>\<^sub>f 0 i f = f"
  by (induct t and fs and f arbitrary: i and i and i
    rule: lift.induct liftr.induct liftf.induct) simp_all

theorem substT_liftT [simp]:
  "k \<le> k' \<Longrightarrow> k' < k + n \<Longrightarrow> (\<up>\<^sub>\<tau> n k T)[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> = \<up>\<^sub>\<tau> (n - 1) k T"
  "k \<le> k' \<Longrightarrow> k' < k + n \<Longrightarrow> (\<up>\<^sub>r\<^sub>\<tau> n k rT)[k' \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau> = \<up>\<^sub>r\<^sub>\<tau> (n - 1) k rT"
  "k \<le> k' \<Longrightarrow> k' < k + n \<Longrightarrow> (\<up>\<^sub>f\<^sub>\<tau> n k fT)[k' \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau> = \<up>\<^sub>f\<^sub>\<tau> (n - 1) k fT"
  by (induct T and rT and fT arbitrary: k k' and k k' and k k'
    rule: liftT.induct liftrT.induct liftfT.induct) simp_all

theorem liftT_substT [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>\<tau> n k (T[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) = \<up>\<^sub>\<tau> n k T[k' + n \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>r\<^sub>\<tau> n k (rT[k' \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>) = \<up>\<^sub>r\<^sub>\<tau> n k rT[k' + n \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>"
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>f\<^sub>\<tau> n k (fT[k' \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau>) = \<up>\<^sub>f\<^sub>\<tau> n k fT[k' + n \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau>"
  apply (induct T and rT and fT arbitrary: k k' and k k' and k k'
    rule: liftT.induct liftrT.induct liftfT.induct)
  apply simp_all
  done

theorem liftT_substT' [simp]:
  "k' < k \<Longrightarrow>
     \<up>\<^sub>\<tau> n k (T[k' \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) = \<up>\<^sub>\<tau> n (k + 1) T[k' \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n (k - k') U]\<^sub>\<tau>"
  "k' < k \<Longrightarrow>
     \<up>\<^sub>r\<^sub>\<tau> n k (rT[k' \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>) = \<up>\<^sub>r\<^sub>\<tau> n (k + 1) rT[k' \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n (k - k') U]\<^sub>r\<^sub>\<tau>"
  "k' < k \<Longrightarrow>
     \<up>\<^sub>f\<^sub>\<tau> n k (fT[k' \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau>) = \<up>\<^sub>f\<^sub>\<tau> n (k + 1) fT[k' \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n (k - k') U]\<^sub>f\<^sub>\<tau>"
  apply (induct T and rT and fT arbitrary: k k' and k k' and k k'
    rule: liftT.induct liftrT.induct liftfT.induct)
  apply simp_all
  apply arith
  done

lemma liftT_substT_Top [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>\<tau> n k' (T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>) = \<up>\<^sub>\<tau> n (Suc k') T[k \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>r\<^sub>\<tau> n k' (rT[k \<mapsto>\<^sub>\<tau> Top]\<^sub>r\<^sub>\<tau>) = \<up>\<^sub>r\<^sub>\<tau> n (Suc k') rT[k \<mapsto>\<^sub>\<tau> Top]\<^sub>r\<^sub>\<tau>"
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>f\<^sub>\<tau> n k' (fT[k \<mapsto>\<^sub>\<tau> Top]\<^sub>f\<^sub>\<tau>) = \<up>\<^sub>f\<^sub>\<tau> n (Suc k') fT[k \<mapsto>\<^sub>\<tau> Top]\<^sub>f\<^sub>\<tau>"
  apply (induct T and rT and fT arbitrary: k k' and k k' and k k'
    rule: liftT.induct liftrT.induct liftfT.induct)
  apply simp_all
  apply arith
  done

theorem liftE_substE [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>e n k (\<Gamma>[k' \<mapsto>\<^sub>\<tau> U]\<^sub>e) = \<up>\<^sub>e n k \<Gamma>[k' + n \<mapsto>\<^sub>\<tau> U]\<^sub>e"
  apply (induct \<Gamma> arbitrary: k k' and k k' and k k')
  apply simp_all
  apply (case_tac a)
  apply (simp_all add: ac_simps)
  done

lemma liftT_decT [simp]:
  "k \<le> k' \<Longrightarrow> \<up>\<^sub>\<tau> n k' (\<down>\<^sub>\<tau> m k T) = \<down>\<^sub>\<tau> m k (\<up>\<^sub>\<tau> n (m + k') T)"
  by (induct m arbitrary: T) simp_all

lemma liftT_substT_strange:
  "\<up>\<^sub>\<tau> n k T[n + k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> = \<up>\<^sub>\<tau> n (Suc k) T[k \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n 0 U]\<^sub>\<tau>"
  "\<up>\<^sub>r\<^sub>\<tau> n k rT[n + k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau> = \<up>\<^sub>r\<^sub>\<tau> n (Suc k) rT[k \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n 0 U]\<^sub>r\<^sub>\<tau>"
  "\<up>\<^sub>f\<^sub>\<tau> n k fT[n + k \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau> = \<up>\<^sub>f\<^sub>\<tau> n (Suc k) fT[k \<mapsto>\<^sub>\<tau> \<up>\<^sub>\<tau> n 0 U]\<^sub>f\<^sub>\<tau>"
  apply (induct T and rT and fT arbitrary: n k and n k and n k
    rule: liftT.induct liftrT.induct liftfT.induct)
  apply simp_all
  apply (thin_tac "\<And>x. PROP P x" for P :: "_ \<Rightarrow> prop")
  apply (drule_tac x=n in meta_spec)
  apply (drule_tac x="Suc k" in meta_spec)
  apply simp
  done

lemma liftp_liftp [simp]:
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>p n' k' (\<up>\<^sub>p n k p) = \<up>\<^sub>p (n + n') k p"
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>r\<^sub>p n' k' (\<up>\<^sub>r\<^sub>p n k rp) = \<up>\<^sub>r\<^sub>p (n + n') k rp"
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>f\<^sub>p n' k' (\<up>\<^sub>f\<^sub>p n k fp) = \<up>\<^sub>f\<^sub>p (n + n') k fp"
  by (induct p and rp and fp arbitrary: k k' and k k' and k k'
    rule: liftp.induct liftrp.induct liftfp.induct) simp_all

lemma liftp_psize[simp]:
  "\<parallel>\<up>\<^sub>p n k p\<parallel>\<^sub>p = \<parallel>p\<parallel>\<^sub>p"
  "\<parallel>\<up>\<^sub>r\<^sub>p n k fs\<parallel>\<^sub>r = \<parallel>fs\<parallel>\<^sub>r"
  "\<parallel>\<up>\<^sub>f\<^sub>p n k f\<parallel>\<^sub>f = \<parallel>f\<parallel>\<^sub>f"
  by (induct p and fs and f rule: liftp.induct liftrp.induct liftfp.induct) simp_all

lemma lift_lift [simp]:
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up> n' k' (\<up> n k t) = \<up> (n + n') k t"
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>r n' k' (\<up>\<^sub>r n k fs) = \<up>\<^sub>r (n + n') k fs"
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>f n' k' (\<up>\<^sub>f n k f) = \<up>\<^sub>f (n + n') k f"
 by (induct t and fs and f arbitrary: k k' and k k' and k k'
   rule: lift.induct liftr.induct liftf.induct) simp_all

lemma liftE_liftE [simp]:
  "k \<le> k' \<Longrightarrow> k' \<le> k + n \<Longrightarrow> \<up>\<^sub>e n' k' (\<up>\<^sub>e n k \<Gamma>) = \<up>\<^sub>e (n + n') k \<Gamma>"
  apply (induct \<Gamma> arbitrary: k k')
  apply simp_all
  apply (case_tac a)
  apply simp_all
  done

lemma liftE_liftE' [simp]:
  "i + m \<le> j \<Longrightarrow> \<up>\<^sub>e n j (\<up>\<^sub>e m i \<Gamma>) = \<up>\<^sub>e m i (\<up>\<^sub>e n (j - m) \<Gamma>)"
  apply (induct \<Gamma> arbitrary: i j m n)
  apply simp_all
  apply (case_tac a)
  apply simp_all
  done

lemma substT_substT:
  "i \<le> j \<Longrightarrow>
     T[Suc j \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>[i \<mapsto>\<^sub>\<tau> U[j - i \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>]\<^sub>\<tau> = T[i \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>[j \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>"
  "i \<le> j \<Longrightarrow>
     rT[Suc j \<mapsto>\<^sub>\<tau> V]\<^sub>r\<^sub>\<tau>[i \<mapsto>\<^sub>\<tau> U[j - i \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>]\<^sub>r\<^sub>\<tau> = rT[i \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>[j \<mapsto>\<^sub>\<tau> V]\<^sub>r\<^sub>\<tau>"
  "i \<le> j \<Longrightarrow>
     fT[Suc j \<mapsto>\<^sub>\<tau> V]\<^sub>f\<^sub>\<tau>[i \<mapsto>\<^sub>\<tau> U[j - i \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>]\<^sub>f\<^sub>\<tau> = fT[i \<mapsto>\<^sub>\<tau> U]\<^sub>f\<^sub>\<tau>[j \<mapsto>\<^sub>\<tau> V]\<^sub>f\<^sub>\<tau>"
  apply (induct T and rT and fT arbitrary: i j U V and i j U V and i j U V
    rule: liftT.induct liftrT.induct liftfT.induct)
  apply (simp_all add: diff_Suc split: nat.split)
  apply (thin_tac "\<And>x. PROP P x" for P :: "_ \<Rightarrow> prop")
  apply (drule_tac x="Suc i" in meta_spec)
  apply (drule_tac x="Suc j" in meta_spec)
  apply simp
  done

lemma substT_decT [simp]:
  "k \<le> j \<Longrightarrow> (\<down>\<^sub>\<tau> i k T)[j \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> = \<down>\<^sub>\<tau> i k (T[i + j \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>)"
  by (induct i arbitrary: T j) (simp_all add: substT_substT [symmetric])

lemma substT_decT' [simp]:
  "i \<le> j \<Longrightarrow> \<down>\<^sub>\<tau> k (Suc j) T[i \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau> = \<down>\<^sub>\<tau> k j (T[i \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>)"
  by (induct k arbitrary: i j T) (simp_all add: substT_substT [of _ _ _ _ Top, simplified])

lemma substE_substE:
  "i \<le> j \<Longrightarrow> \<Gamma>[Suc j \<mapsto>\<^sub>\<tau> V]\<^sub>e[i \<mapsto>\<^sub>\<tau> U[j - i \<mapsto>\<^sub>\<tau> V]\<^sub>\<tau>]\<^sub>e = \<Gamma>[i \<mapsto>\<^sub>\<tau> U]\<^sub>e[j \<mapsto>\<^sub>\<tau> V]\<^sub>e"
  apply (induct \<Gamma>)
  apply (case_tac [2] a)
  apply (simp_all add: substT_substT [symmetric])
  done

lemma substT_decE [simp]:
  "i \<le> j \<Longrightarrow> \<down>\<^sub>e k (Suc j) \<Gamma>[i \<mapsto>\<^sub>\<tau> Top]\<^sub>e = \<down>\<^sub>e k j (\<Gamma>[i \<mapsto>\<^sub>\<tau> Top]\<^sub>e)"
  by (induct k arbitrary: i j \<Gamma>) (simp_all add: substE_substE [of _ _ _ _ Top, simplified])

lemma liftE_app [simp]: "\<up>\<^sub>e n k (\<Gamma> @ \<Delta>) = \<up>\<^sub>e n (k + \<parallel>\<Delta>\<parallel>) \<Gamma> @ \<up>\<^sub>e n k \<Delta>"
  by (induct \<Gamma> arbitrary: k) (simp_all add: ac_simps)

lemma substE_app [simp]:
  "(\<Gamma> @ \<Delta>)[k \<mapsto>\<^sub>\<tau> T]\<^sub>e = \<Gamma>[k + \<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> T]\<^sub>e @ \<Delta>[k \<mapsto>\<^sub>\<tau> T]\<^sub>e"
  by (induct \<Gamma>) (simp_all add: ac_simps)

lemma substs_app [simp]: "t[k \<mapsto>\<^sub>s ts @ us] = t[k + \<parallel>us\<parallel> \<mapsto>\<^sub>s ts][k \<mapsto>\<^sub>s us]"
  by (induct ts arbitrary: t k) (simp_all add: ac_simps)

theorem decE_Nil [simp]: "\<down>\<^sub>e n k [] = []"
  by (induct n) simp_all

theorem decE_Cons [simp]:
  "\<down>\<^sub>e n k (B \<Colon> \<Gamma>) = mapB (\<down>\<^sub>\<tau> n (k + \<parallel>\<Gamma>\<parallel>)) B \<Colon> \<down>\<^sub>e n k \<Gamma>"
  apply (induct n arbitrary: B \<Gamma>)
  apply (case_tac B)
  apply (case_tac [3] B)
  apply simp_all
  done

theorem decE_app [simp]:
  "\<down>\<^sub>e n k (\<Gamma> @ \<Delta>) = \<down>\<^sub>e n (k + \<parallel>\<Delta>\<parallel>) \<Gamma> @ \<down>\<^sub>e n k \<Delta>"
  by (induct n arbitrary: \<Gamma> \<Delta>) simp_all

theorem decT_liftT [simp]:
  "k \<le> k' \<Longrightarrow> k' + m \<le> k + n \<Longrightarrow> \<down>\<^sub>\<tau> m k' (\<up>\<^sub>\<tau> n k \<Gamma>) = \<up>\<^sub>\<tau> (n - m) k \<Gamma>"
  apply (induct m arbitrary: n)
  apply (subgoal_tac [2] "k' + m \<le> k + (n - Suc 0)")
  apply simp_all
  done

theorem decE_liftE [simp]:
  "k \<le> k' \<Longrightarrow> k' + m \<le> k + n \<Longrightarrow> \<down>\<^sub>e m k' (\<up>\<^sub>e n k \<Gamma>) = \<up>\<^sub>e (n - m) k \<Gamma>"
  apply (induct \<Gamma> arbitrary: k k')
  apply (case_tac [2] a)
  apply simp_all
  done

theorem liftE0 [simp]: "\<up>\<^sub>e 0 k \<Gamma> = \<Gamma>"
  apply (induct \<Gamma>)
  apply (case_tac [2] a)
  apply simp_all
  done

lemma decT_decT [simp]: "\<down>\<^sub>\<tau> n k (\<down>\<^sub>\<tau> n' (k + n) T) = \<down>\<^sub>\<tau> (n + n') k T"
  by (induct n arbitrary: k T) simp_all

lemma decE_decE [simp]: "\<down>\<^sub>e n k (\<down>\<^sub>e n' (k + n) \<Gamma>) = \<down>\<^sub>e (n + n') k \<Gamma>"
  by (induct n arbitrary: k \<Gamma>) simp_all

lemma decE_length [simp]: "\<parallel>\<down>\<^sub>e n k \<Gamma>\<parallel> = \<parallel>\<Gamma>\<parallel>"
  by (induct \<Gamma>) simp_all

lemma liftrT_assoc_None [simp]: "(\<up>\<^sub>r\<^sub>\<tau> n k fs\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fs\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fs rule: list.induct) auto

lemma liftrT_assoc_Some: "fs\<langle>l\<rangle>\<^sub>? = \<lfloor>T\<rfloor> \<Longrightarrow> \<up>\<^sub>r\<^sub>\<tau> n k fs\<langle>l\<rangle>\<^sub>? = \<lfloor>\<up>\<^sub>\<tau> n k T\<rfloor>"
  by (induct fs rule: list.induct) auto

lemma liftrp_assoc_None [simp]: "(\<up>\<^sub>r\<^sub>p n k fps\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fps\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fps rule: list.induct) auto

lemma liftr_assoc_None [simp]: "(\<up>\<^sub>r n k fs\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fs\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fs rule: list.induct) auto

lemma unique_liftrT [simp]: "unique (\<up>\<^sub>r\<^sub>\<tau> n k fs) = unique fs"
  by (induct fs rule: list.induct) auto

lemma substrTT_assoc_None [simp]: "(fs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>\<langle>a\<rangle>\<^sub>? = \<bottom>) = (fs\<langle>a\<rangle>\<^sub>? = \<bottom>)"
  by (induct fs rule: list.induct) auto

lemma substrTT_assoc_Some [simp]:
  "fs\<langle>a\<rangle>\<^sub>? = \<lfloor>T\<rfloor> \<Longrightarrow> fs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>\<langle>a\<rangle>\<^sub>? = \<lfloor>T[k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>\<rfloor>"
  by (induct fs rule: list.induct) auto

lemma substrT_assoc_None [simp]: "(fs[k \<mapsto>\<^sub>\<tau> P]\<^sub>r\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fs\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fs rule: list.induct) auto

lemma substrp_assoc_None [simp]: "(fps[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>p\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fps\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fps rule: list.induct) auto

lemma substr_assoc_None [simp]: "(fs[k \<mapsto> u]\<^sub>r\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fs\<langle>l\<rangle>\<^sub>? = \<bottom>)"
  by (induct fs rule: list.induct) auto

lemma unique_substrT [simp]: "unique (fs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>) = unique fs"
  by (induct fs rule: list.induct) auto

lemma liftrT_set: "(a, T) \<in> set fs \<Longrightarrow> (a, \<up>\<^sub>\<tau> n k T) \<in> set (\<up>\<^sub>r\<^sub>\<tau> n k fs)"
  by (induct fs rule: list.induct) auto

lemma liftrT_setD:
  "(a, T) \<in> set (\<up>\<^sub>r\<^sub>\<tau> n k fs) \<Longrightarrow> \<exists>T'. (a, T') \<in> set fs \<and> T = \<up>\<^sub>\<tau> n k T'"
  by (induct fs rule: list.induct) auto

lemma substrT_set: "(a, T) \<in> set fs \<Longrightarrow> (a, T[k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>) \<in> set (fs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>)"
  by (induct fs rule: list.induct) auto

lemma substrT_setD:
  "(a, T) \<in> set (fs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau>) \<Longrightarrow> \<exists>T'. (a, T') \<in> set fs \<and> T = T'[k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  by (induct fs rule: list.induct) auto


subsection \<open>Well-formedness\<close>

text \<open>
The definition of well-formedness is extended with a rule stating that a
record type @{term "RcdT fs"} is well-formed, if for all fields @{term "(l, T)"}
contained in the list @{term fs}, the type @{term T} is well-formed, and
all labels @{term l} in @{term fs} are {\it unique}.
\<close>

inductive
  well_formed :: "env \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile>\<^sub>w\<^sub>f _" [50, 50] 50)
where
  wf_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i"
| wf_Top: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f Top"
| wf_arrow: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<rightarrow> U"
| wf_all: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> TVarB T \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f (\<forall><:T. U)"
| wf_RcdT: "unique fs \<Longrightarrow> \<forall>(l, T)\<in>set fs. \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs"

inductive
  well_formedE :: "env \<Rightarrow> bool"  ("_ \<turnstile>\<^sub>w\<^sub>f" [50] 50)
  and well_formedB :: "env \<Rightarrow> binding \<Rightarrow> bool"  ("_ \<turnstile>\<^sub>w\<^sub>f\<^sub>B _" [50, 50] 50)
where
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<equiv> \<Gamma> \<turnstile>\<^sub>w\<^sub>f type_ofB B"
| wf_Nil: "[] \<turnstile>\<^sub>w\<^sub>f"
| wf_Cons: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"

inductive_cases well_formed_cases:
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f Top"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<rightarrow> U"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f (\<forall><:T. U)"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f (RcdT fTs)"

inductive_cases well_formedE_cases:
  "B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"

lemma wf_TVarB: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> TVarB T \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  by (rule wf_Cons) simp_all

lemma wf_VarB: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> VarB T \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  by (rule wf_Cons) simp_all

lemma map_is_TVarb:
  "map is_TVarB \<Gamma>' = map is_TVarB \<Gamma> \<Longrightarrow>
    \<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor> \<Longrightarrow> \<exists>T. \<Gamma>'\<langle>i\<rangle> = \<lfloor>TVarB T\<rfloor>"
  apply (induct \<Gamma> arbitrary: \<Gamma>' T i)
  apply simp
  apply (auto split: nat.split_asm)
  apply (case_tac z)
  apply simp_all
  done

lemma wf_equallength:
  assumes H: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T"
  shows "map is_TVarB \<Gamma>' = map is_TVarB \<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>w\<^sub>f T" using H
  apply (induct arbitrary: \<Gamma>')
  apply (auto intro: well_formed.intros dest: map_is_TVarb)+
  apply (fastforce intro: well_formed.intros)
  done

lemma wfE_replace:
  "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B' \<Longrightarrow> is_TVarB B' = is_TVarB B \<Longrightarrow>
     \<Delta> @ B' \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  apply (induct \<Delta>)
  apply simp
  apply (erule wf_Cons)
  apply (erule well_formedE_cases)
  apply assumption
  apply simp
  apply (erule well_formedE_cases)
  apply (rule wf_Cons)
  apply (case_tac a)
  apply simp
  apply (rule wf_equallength)
  apply assumption
  apply simp
  apply simp
  apply (rule wf_equallength)
  apply assumption
  apply simp
  apply simp
  done

lemma wf_weaken:
  assumes H: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f T"
  shows "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T"
  using H
  apply (induct "\<Delta> @ \<Gamma>" T arbitrary: \<Delta>)
  apply simp_all
  apply (rule conjI)
  apply (rule impI)
  apply (rule wf_TVar)
  apply simp
  apply (rule impI)
  apply (rule wf_TVar)
  apply (subgoal_tac "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)")
  apply simp
  apply arith
  apply (rule wf_Top)
  apply (rule wf_arrow)
  apply simp
  apply simp
  apply (rule wf_all)
  apply simp
  apply (drule_tac x="TVarB T \<Colon> \<Delta>" in meta_spec)
  apply simp
  \<comment> \<open>records\<close>
  apply (rule wf_RcdT)
  apply simp
  apply (rule ballpI)
  apply (drule liftrT_setD)
  apply (erule exE conjE)+
  apply (drule_tac x=l and y="T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>" in bpspec)
  apply simp+
  done

lemma wf_weaken': "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T"
  apply (induct \<Delta>)
  apply simp_all
  apply (drule_tac B=a in wf_weaken [of "[]", simplified])
  apply simp
  done

lemma wfE_weaken: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow> \<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  apply (induct \<Delta>)
  apply simp
  apply (rule wf_Cons)
  apply assumption+
  apply simp
  apply (rule wf_Cons)
  apply (erule well_formedE_cases)
  apply (case_tac a)
  apply simp
  apply (rule wf_weaken)
  apply assumption
  apply simp
  apply (rule wf_weaken)
  apply assumption
  apply (erule well_formedE_cases)
  apply simp
  done

lemma wf_liftB:
  assumes H: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  shows "\<Gamma>\<langle>i\<rangle> = \<lfloor>VarB T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> (Suc i) 0 T"
  using H
  apply (induct arbitrary: i)
  apply simp
  apply (simp split: nat.split_asm)
  apply (frule_tac B="VarB T" in wf_weaken [of "[]", simplified])
  apply simp+
  apply (rename_tac nat)
  apply (drule_tac x=nat in meta_spec)
  apply simp
  apply (frule_tac T="\<up>\<^sub>\<tau> (Suc nat) 0 T" in wf_weaken [of "[]", simplified])
  apply simp
  done

theorem wf_subst:
  "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  "\<forall>(l, T) \<in> set (rT::rcdT). \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow>
     \<forall>(l, T) \<in> set rT. \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f snd (fT::fldT) \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow>
     \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f snd fT[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau>"
  apply (induct T and rT and fT arbitrary: \<Delta> and \<Delta> and \<Delta>
    rule: liftT.induct liftrT.induct liftfT.induct)
  apply (rename_tac nat \<Delta>)
  apply simp_all
  apply (rule conjI)
  apply (rule impI)
  apply (drule_tac \<Gamma>=\<Gamma> and \<Delta>="\<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e" in wf_weaken')
  apply simp
  apply (rule impI conjI)+
  apply (erule well_formed_cases)
  apply (rule wf_TVar)
  apply (simp split: nat.split_asm)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> nat - Suc 0")
  apply (rename_tac nata)
  apply (subgoal_tac "nat - Suc \<parallel>\<Delta>\<parallel> = nata")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply (rule impI)
  apply (erule well_formed_cases)
  apply (rule wf_TVar)
  apply simp
  apply (rule wf_Top)
  apply (erule well_formed_cases)
  apply (rule wf_arrow)
  apply simp+
  apply (rename_tac type1 type2 \<Delta>)
  apply (erule well_formed_cases)
  apply (rule wf_all)
  apply simp
  apply (thin_tac "\<And>x. PROP P x" for P :: "_ \<Rightarrow> prop")
  apply (drule_tac x="TVarB type1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (erule well_formed_cases)
  apply (rule wf_RcdT)
  apply simp
  apply (rule ballpI)
  apply (drule substrT_setD)
  apply (erule exE conjE)+
  apply (drule meta_spec)
  apply (drule meta_mp)
  apply assumption
  apply (thin_tac "\<forall>x \<in> S. P x" for S P)
  apply (drule bpspec)
  apply assumption
  apply simp
  apply (simp add: split_paired_all)
  done

theorem wf_dec: "\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T"
  apply (induct \<Delta> arbitrary: T)
  apply simp
  apply simp
  apply (drule wf_subst(1) [of "[]", simplified])
  apply (rule wf_Top)
  apply simp
  done

theorem wfE_subst: "\<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> \<Delta>[0 \<mapsto>\<^sub>\<tau> U]\<^sub>e @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  apply (induct \<Delta>)
  apply simp
  apply (erule well_formedE_cases)
  apply assumption
  apply simp
  apply (case_tac a)
  apply (erule well_formedE_cases)
  apply (rule wf_Cons)
  apply simp
  apply (rule wf_subst)
  apply assumption+
  apply simp
  apply (erule well_formedE_cases)
  apply (rule wf_Cons)
  apply simp
  apply (rule wf_subst)
  apply assumption+
  done

subsection \<open>Subtyping\<close>

text \<open>
The definition of the subtyping judgement is extended with a rule \<open>SA_Rcd\<close> stating
that a record type @{term "RcdT fs"} is a subtype of @{term "RcdT fs'"}, if
for all fields \mbox{@{term "(l, T)"}} contained in @{term fs'}, there exists a
corresponding field @{term "(l, S)"} such that @{term S} is a subtype of @{term T}.
If the list @{term fs'} is empty, \<open>SA_Rcd\<close> can appear as a leaf in
the derivation tree of the subtyping judgement. Therefore, the introduction
rule needs an additional premise @{term "\<Gamma> \<turnstile>\<^sub>w\<^sub>f"} to make sure that only
subtyping judgements with well-formed contexts are derivable. Moreover,
since @{term fs} can contain additional fields not present in @{term fs'},
we also have to require that the type @{term "RcdT fs"} is well-formed.
In order to ensure that the type @{term "RcdT fs'"} is well-formed, too,
we only have to require that labels in @{term fs'} are unique, since,
by induction on the subtyping derivation, all types contained in @{term fs'}
are already well-formed.
\<close>

inductive
  subtyping :: "env \<Rightarrow> type \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile> _ <: _" [50, 50, 50] 50)
where
  SA_Top: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f S \<Longrightarrow> \<Gamma> \<turnstile> S <: Top"
| SA_refl_TVar: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f TVar i \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: TVar i"
| SA_trans_TVar: "\<Gamma>\<langle>i\<rangle> = \<lfloor>TVarB U\<rfloor> \<Longrightarrow>
    \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc i) 0 U <: T \<Longrightarrow> \<Gamma> \<turnstile> TVar i <: T"
| SA_arrow: "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1 \<rightarrow> T\<^sub>2"
| SA_all: "\<Gamma> \<turnstile> T\<^sub>1 <: S\<^sub>1 \<Longrightarrow> TVarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2 \<Longrightarrow>
    \<Gamma> \<turnstile> (\<forall><:S\<^sub>1. S\<^sub>2) <: (\<forall><:T\<^sub>1. T\<^sub>2)"
| SA_Rcd: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs \<Longrightarrow> unique fs' \<Longrightarrow>
    \<forall>(l, T)\<in>set fs'. \<exists>S. (l, S)\<in>set fs \<and> \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<turnstile> RcdT fs <: RcdT fs'"

lemma wf_subtype_env:
  assumes PQ: "\<Gamma> \<turnstile> P <: Q"
  shows "\<Gamma> \<turnstile>\<^sub>w\<^sub>f" using PQ
  by induct assumption+

lemma wf_subtype:
  assumes PQ: "\<Gamma> \<turnstile> P <: Q"
  shows "\<Gamma> \<turnstile>\<^sub>w\<^sub>f P \<and> \<Gamma> \<turnstile>\<^sub>w\<^sub>f Q" using PQ
  by induct (auto intro: well_formed.intros elim!: wf_equallength)

lemma wf_subtypeE:
  assumes H: "\<Gamma> \<turnstile> T <: U"
  and H': "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f U \<Longrightarrow> P"
  shows "P"
  apply (rule H')
  apply (rule wf_subtype_env)
  apply (rule H)
  apply (rule wf_subtype [OF H, THEN conjunct1])
  apply (rule wf_subtype [OF H, THEN conjunct2])
  done

lemma subtype_refl: \<comment> \<open>A.1\<close>
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<Longrightarrow> \<Gamma> \<turnstile> T <: T"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<forall>(l::name, T)\<in>set fTs. \<Gamma> \<turnstile>\<^sub>w\<^sub>f T \<longrightarrow> \<Gamma> \<turnstile> T <: T"
  "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f snd (fT::fldT) \<Longrightarrow> \<Gamma> \<turnstile> snd fT <: snd fT"
  by (induct T and fTs and fT arbitrary: \<Gamma> and \<Gamma> and \<Gamma>
    rule: liftT.induct liftrT.induct liftfT.induct,
    simp_all add: split_paired_all, simp_all)
    (blast intro: subtyping.intros wf_Nil wf_TVarB bexpI intro!: ballpI
       elim: well_formed_cases ballpE elim!: bexpE)+

lemma subtype_weaken:
  assumes H: "\<Delta> @ \<Gamma> \<turnstile> P <: Q"
  and wf: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B"
  shows "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> P <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> Q" using H
proof (induct "\<Delta> @ \<Gamma>" P Q arbitrary: \<Delta>)
  case SA_Top
  with wf show ?case
    by (auto intro: subtyping.SA_Top wfE_weaken wf_weaken)
next
  case SA_refl_TVar
  with wf show ?case
    by (auto intro!: subtyping.SA_refl_TVar wfE_weaken dest: wf_weaken)
next
  case (SA_trans_TVar i U T)
  thus ?case
  proof (cases "i < \<parallel>\<Delta>\<parallel>")
    case True
    with SA_trans_TVar
    have "(\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma>)\<langle>i\<rangle> = \<lfloor>TVarB (\<up>\<^sub>\<tau> 1 (\<parallel>\<Delta>\<parallel> - Suc i) U)\<rfloor>"
      by simp
    moreover from True SA_trans_TVar
    have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>
      \<up>\<^sub>\<tau> (Suc i) 0 (\<up>\<^sub>\<tau> 1 (\<parallel>\<Delta>\<parallel> - Suc i) U) <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by simp
    ultimately have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> TVar i <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by (rule subtyping.SA_trans_TVar)
    with True show ?thesis by simp
  next
    case False
    then have "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)" by arith
    with False SA_trans_TVar have "(\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma>)\<langle>Suc i\<rangle> = \<lfloor>TVarB U\<rfloor>"
      by simp
    moreover from False SA_trans_TVar
    have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc (Suc i)) 0 U <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by simp
    ultimately have "\<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> TVar (Suc i) <: \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
      by (rule subtyping.SA_trans_TVar)
    with False show ?thesis by simp
  qed
next
  case SA_arrow
  thus ?case by simp (iprover intro: subtyping.SA_arrow)
next
  case (SA_all T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
  with SA_all(4) [of "TVarB T\<^sub>1 \<Colon> \<Delta>"]
  show ?case by simp (iprover intro: subtyping.SA_all)
next
  case (SA_Rcd fs fs')
  with wf have "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f" by simp (rule wfE_weaken)
  moreover from \<open>\<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs\<close>
  have "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> (RcdT fs)"
    by (rule wf_weaken)
  hence "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs)" by simp
  moreover from SA_Rcd have "unique (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs')" by simp
  moreover have "\<forall>(l, T)\<in>set (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs').
    \<exists>S. (l, S)\<in>set (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs) \<and> \<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> S <: T"
  proof (rule ballpI)
    fix l T
    assume "(l, T) \<in> set (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs')"
    then obtain T' where "(l, T') \<in> set fs'" and T: "T = \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T'"
      by (blast dest: liftrT_setD)
    with SA_Rcd obtain S where
      lS: "(l, S) \<in> set fs"
      and ST: "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> S <: \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> (T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>)"
      by fastforce
    with T have "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> S <: \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T'"
      by simp
    moreover from lS have "(l, \<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> S) \<in> set (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs)"
      by (rule liftrT_set)
    moreover note T
    ultimately show "\<exists>S. (l, S)\<in>set (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs) \<and> \<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> S <: T"
      by auto
  qed
  ultimately have "\<up>\<^sub>e (Suc 0) 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> RcdT (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs) <: RcdT (\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fs')"
    by (rule subtyping.SA_Rcd)
  thus ?case by simp
qed

lemma subtype_weaken': \<comment> \<open>A.2\<close>
  "\<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 P <: \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 Q"
  apply (induct \<Delta>)
  apply simp_all
  apply (erule well_formedE_cases)
  apply simp
  apply (drule_tac B="a" and \<Gamma>="\<Delta> @ \<Gamma>" in subtype_weaken [of "[]", simplified])
  apply simp_all
  done

lemma fieldT_size [simp]:
  "(a, T) \<in> set fs \<Longrightarrow> size T < Suc (size_list (size_prod (\<lambda>x. 0) size) fs)"
  by (induct fs arbitrary: a T rule: list.induct) fastforce+

lemma subtype_trans: \<comment> \<open>A.3\<close>
  "\<Gamma> \<turnstile> S <: Q \<Longrightarrow> \<Gamma> \<turnstile> Q <: T \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> M <: N \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
     \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> M <: N"
  using wf_measure_size
proof (induct Q arbitrary: \<Gamma> S T \<Delta> P M N rule: wf_induct_rule)
  case (less Q)
  {
    fix \<Gamma> S T Q'
    assume "\<Gamma> \<turnstile> S <: Q'"
    then have "\<Gamma> \<turnstile> Q' <: T \<Longrightarrow> size Q = size Q' \<Longrightarrow> \<Gamma> \<turnstile> S <: T"
    proof (induct arbitrary: T)
      case SA_Top
      from SA_Top(3) show ?case
        by cases (auto intro: subtyping.SA_Top SA_Top)
    next
      case SA_refl_TVar show ?case by fact
    next
      case SA_trans_TVar
      thus ?case by (auto intro: subtyping.SA_trans_TVar)
    next
      case (SA_arrow \<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
      note SA_arrow' = SA_arrow
      from SA_arrow(5) show ?case
      proof cases
        case SA_Top
        with SA_arrow show ?thesis
          by (auto intro: subtyping.SA_Top wf_arrow elim: wf_subtypeE)
      next
        case (SA_arrow T\<^sub>1' T\<^sub>2')
        from SA_arrow SA_arrow' have "\<Gamma> \<turnstile> S\<^sub>1 \<rightarrow> S\<^sub>2 <: T\<^sub>1' \<rightarrow> T\<^sub>2'"
          by (auto intro!: subtyping.SA_arrow intro: less(1) [of "T\<^sub>1"] less(1) [of "T\<^sub>2"])
        with SA_arrow show ?thesis by simp
      qed
    next
      case (SA_all \<Gamma> T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
      note SA_all' = SA_all
      from SA_all(5) show ?case
      proof cases
        case SA_Top
        with SA_all show ?thesis by (auto intro!:
          subtyping.SA_Top wf_all intro: wf_equallength elim: wf_subtypeE)
      next
        case (SA_all T\<^sub>1' T\<^sub>2')
        from SA_all SA_all' have "\<Gamma> \<turnstile> T\<^sub>1' <: S\<^sub>1"
          by - (rule less(1), simp_all)
        moreover from SA_all SA_all' have "TVarB T\<^sub>1' \<Colon> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2"
          by - (rule less(2) [of _ "[]", simplified], simp_all)
        with SA_all SA_all' have "TVarB T\<^sub>1' \<Colon> \<Gamma> \<turnstile> S\<^sub>2 <: T\<^sub>2'"
          by - (rule less(1), simp_all)
        ultimately have "\<Gamma> \<turnstile> (\<forall><:S\<^sub>1. S\<^sub>2) <: (\<forall><:T\<^sub>1'. T\<^sub>2')"
          by (rule subtyping.SA_all)
        with SA_all show ?thesis by simp
      qed
    next
      case (SA_Rcd \<Gamma> fs\<^sub>1 fs\<^sub>2)
      note SA_Rcd' = SA_Rcd
      from SA_Rcd(5) show ?case
      proof cases
        case SA_Top
        with SA_Rcd show ?thesis by (auto intro!: subtyping.SA_Top)
      next
        case (SA_Rcd fs\<^sub>2')
        note \<open>\<Gamma> \<turnstile>\<^sub>w\<^sub>f\<close>
        moreover note \<open>\<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs\<^sub>1\<close>
        moreover note \<open>unique fs\<^sub>2'\<close>
        moreover have "\<forall>(l, T)\<in>set fs\<^sub>2'. \<exists>S. (l, S)\<in>set fs\<^sub>1 \<and> \<Gamma> \<turnstile> S <: T"
        proof (rule ballpI)
          fix l T
          assume lT: "(l, T) \<in> set fs\<^sub>2'"
          with SA_Rcd obtain U where
            fs2: "(l, U) \<in> set fs\<^sub>2" and UT: "\<Gamma> \<turnstile> U <: T" by blast
          with SA_Rcd SA_Rcd' obtain S where
            fs1: "(l, S) \<in> set fs\<^sub>1" and SU: "\<Gamma> \<turnstile> S <: U" by blast
          from SA_Rcd SA_Rcd' fs2 have "(U, Q) \<in> measure size" by simp
          hence "\<Gamma> \<turnstile> S <: T" using SU UT by (rule less(1))
          with fs1 show "\<exists>S. (l, S)\<in>set fs\<^sub>1 \<and> \<Gamma> \<turnstile> S <: T" by blast
        qed
        ultimately have "\<Gamma> \<turnstile> RcdT fs\<^sub>1 <: RcdT fs\<^sub>2'" by (rule subtyping.SA_Rcd)
        with SA_Rcd show ?thesis by simp
      qed
    qed
  }
  note tr = this
  {
    case 1
    thus ?case using refl by (rule tr)
  next
    case 2
    from 2(1) show "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> M <: N"
    proof (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" M N arbitrary: \<Delta>)
      case SA_Top
      with 2 show ?case by (auto intro!: subtyping.SA_Top
        intro: wf_equallength wfE_replace elim!: wf_subtypeE)
    next
      case SA_refl_TVar
      with 2 show ?case by (auto intro!: subtyping.SA_refl_TVar
        intro: wf_equallength wfE_replace elim!: wf_subtypeE)
    next
      case (SA_trans_TVar i U T)
      show ?case
      proof (cases "i < \<parallel>\<Delta>\<parallel>")
        case True
        with SA_trans_TVar show ?thesis
          by (auto intro!: subtyping.SA_trans_TVar)
      next
        case False
        note False' = False
        show ?thesis
        proof (cases "i = \<parallel>\<Delta>\<parallel>")
          case True
          from SA_trans_TVar have "(\<Delta> @ [TVarB P]) @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
            by (auto intro: wfE_replace elim!: wf_subtypeE)
          with \<open>\<Gamma> \<turnstile> P <: Q\<close>
          have "(\<Delta> @ [TVarB P]) @ \<Gamma> \<turnstile> \<up>\<^sub>\<tau> \<parallel>\<Delta> @ [TVarB P]\<parallel> 0 P <: \<up>\<^sub>\<tau> \<parallel>\<Delta> @ [TVarB P]\<parallel> 0 Q"
            by (rule subtype_weaken')
          with SA_trans_TVar True False have "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>\<tau> (Suc \<parallel>\<Delta>\<parallel>) 0 P <: T"
            by - (rule tr, simp+)
          with True and False and SA_trans_TVar show ?thesis
            by (auto intro!: subtyping.SA_trans_TVar)
        next
          case False
          with False' have "i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel> - 1)" by arith
          with False False' SA_trans_TVar show ?thesis
            by - (rule subtyping.SA_trans_TVar, simp+)
        qed
      qed
    next
      case SA_arrow
      thus ?case by (auto intro!: subtyping.SA_arrow)
    next
      case (SA_all T\<^sub>1 S\<^sub>1 S\<^sub>2 T\<^sub>2)
      thus ?case by (auto intro: subtyping.SA_all
        SA_all(4) [of "TVarB T\<^sub>1 \<Colon> \<Delta>", simplified])
    next
      case (SA_Rcd fs fs')
      from \<open>\<Gamma> \<turnstile> P <: Q\<close> have "\<Gamma> \<turnstile>\<^sub>w\<^sub>f P" by (rule wf_subtypeE)
      with SA_Rcd have "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
        by - (rule wfE_replace, simp+)
      moreover from SA_Rcd have "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs" by simp
      hence "\<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile>\<^sub>w\<^sub>f RcdT fs" by (rule wf_equallength) simp_all
      moreover note \<open>unique fs'\<close>
      moreover from SA_Rcd
      have "\<forall>(l, T)\<in>set fs'. \<exists>S. (l, S)\<in>set fs \<and> \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> S <: T"
        by blast
      ultimately show ?case by (rule subtyping.SA_Rcd)
    qed
  }
qed

lemma substT_subtype: \<comment> \<open>A.10\<close>
  assumes H: "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> S <: T"
  shows "\<Gamma> \<turnstile> P <: Q \<Longrightarrow>
    \<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> S[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau> <: T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
  using H
  apply (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" S T arbitrary: \<Delta>)
  apply simp_all
  apply (rule SA_Top)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (rule wf_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (rule impI conjI)+
  apply (rule subtype_refl)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply (drule_tac T=P and \<Delta>="\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e" in wf_weaken')
  apply simp
  apply (rule conjI impI)+
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply (drule wf_subst)
  apply assumption
  apply simp
  apply (rule impI)
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply (drule wf_subst)
  apply assumption
  apply simp
  apply (rule conjI impI)+
  apply simp
  apply (drule_tac \<Gamma>=\<Gamma> and \<Delta>="\<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e" in subtype_weaken')
  apply (erule wf_subtypeE)+
  apply assumption
  apply simp
  apply (rule subtype_trans(1))
  apply assumption+
  apply (rule conjI impI)+
  apply (rule SA_trans_TVar)
  apply (simp split: nat.split_asm)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (rename_tac nat)
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply simp
  apply (rule impI)
  apply (rule SA_trans_TVar)
  apply (simp split: nat.split_asm)
  apply (subgoal_tac "Suc (\<parallel>\<Delta>\<parallel> - Suc 0) = \<parallel>\<Delta>\<parallel>")
  apply (simp (no_asm_simp))
  apply arith
  apply (rule SA_arrow)
  apply simp+
  apply (rule SA_all)
  apply simp
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (erule wf_subtypeE)
  apply (rule SA_Rcd)
  apply (erule wfE_subst)
  apply assumption
  apply (drule wf_subst)
  apply assumption
  apply simp
  apply simp
  apply (rule ballpI)
  apply (drule substrT_setD)
  apply (erule exE conjE)+
  apply (drule bpspec)
  apply assumption
  apply simp
  apply (erule exE)
  apply (erule conjE)+
  apply (rule exI)
  apply (rule conjI)
  apply (erule substrT_set)
  apply assumption
  done

lemma subst_subtype:
  assumes H: "\<Delta> @ VarB V \<Colon> \<Gamma> \<turnstile> T <: U"
  shows "\<down>\<^sub>e 1 0 \<Delta> @ \<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T <: \<down>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> U"
  using H
  apply (induct "\<Delta> @ VarB V \<Colon> \<Gamma>" T U arbitrary: \<Delta>)
  apply simp_all
  apply (rule SA_Top)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply (rule wf_subst)
  apply assumption
  apply (rule wf_Top)
  apply (rule impI conjI)+
  apply (rule SA_Top)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)+
  apply (rule conjI impI)+
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply (drule wf_subst)
  apply (rule wf_Top)
  apply simp
  apply (rule impI)
  apply (rule SA_refl_TVar)
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply (drule wf_subst)
  apply (rule wf_Top)
  apply simp
  apply (rule conjI impI)+
  apply simp
  apply (rule conjI impI)+
  apply (simp split: nat.split_asm)
  apply (rule SA_trans_TVar)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (rename_tac nat)
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply simp
  apply (rule impI)
  apply (rule SA_trans_TVar)
  apply simp
  apply (subgoal_tac "0 < \<parallel>\<Delta>\<parallel>")
  apply simp
  apply arith
  apply (rule SA_arrow)
  apply simp+
  apply (rule SA_all)
  apply simp
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (rule SA_Rcd)
  apply (erule wfE_subst)
  apply (rule wf_Top)
  apply (drule wf_subst)
  apply (rule wf_Top)
  apply simp
  apply simp
  apply (rule ballpI)
  apply (drule substrT_setD)
  apply (erule exE conjE)+
  apply (drule bpspec)
  apply assumption
  apply simp
  apply (erule exE)
  apply (erule conjE)+
  apply (rule exI)
  apply (rule conjI)
  apply (erule substrT_set)
  apply assumption
  done


subsection \<open>Typing\<close>

text \<open>
In the formalization of the type checking rule for the \<open>LET\<close> binder,
we use an additional judgement \<open>\<turnstile> p : T \<Rightarrow> \<Delta>\<close> for checking whether a
given pattern @{term p} is compatible with the type @{term T} of an object that
is to be matched against this pattern. The judgement will be defined simultaneously
with a judgement \mbox{\<open>\<turnstile> ps [:] Ts \<Rightarrow> \<Delta>\<close>} for type checking field patterns.
Apart from checking the type, the judgement also returns a list of bindings @{term \<Delta>},
which can be thought of as a ``flattened'' list of types of the variables occurring
in the pattern. Since typing environments are extended ``to the left'', the bindings
in @{term \<Delta>} appear in reverse order.
\<close>

inductive
  ptyping :: "pat \<Rightarrow> type \<Rightarrow> env \<Rightarrow> bool"  ("\<turnstile> _ : _ \<Rightarrow> _" [50, 50, 50] 50)
  and ptypings :: "rpat \<Rightarrow> rcdT \<Rightarrow> env \<Rightarrow> bool"  ("\<turnstile> _ [:] _ \<Rightarrow> _" [50, 50, 50] 50)
where
  P_Var: "\<turnstile> PVar T : T \<Rightarrow> [VarB T]"
| P_Rcd: "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<turnstile> PRcd fps : RcdT fTs \<Rightarrow> \<Delta>"
| P_Nil: "\<turnstile> [] [:] [] \<Rightarrow> []"
| P_Cons: "\<turnstile> p : T \<Rightarrow> \<Delta>\<^sub>1 \<Longrightarrow> \<turnstile> fps [:] fTs \<Rightarrow> \<Delta>\<^sub>2 \<Longrightarrow> fps\<langle>l\<rangle>\<^sub>? = \<bottom> \<Longrightarrow>
    \<turnstile> ((l, p) \<Colon> fps) [:] ((l, T) \<Colon> fTs) \<Rightarrow> \<up>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 \<Delta>\<^sub>2 @ \<Delta>\<^sub>1"

text \<open>
The definition of the typing judgement for terms is extended with the rules \<open>T_Let\<close>,
@{term "T_Rcd"}, and @{term "T_Proj"} for pattern matching, record construction and
field selection, respectively. The above typing judgement for patterns is used in
the rule \<open>T_Let\<close>. The typing judgement for terms is defined simultaneously
with a typing judgement \<open>\<Gamma> \<turnstile> fs [:] fTs\<close> for record fields.
\<close>

inductive
  typing :: "env \<Rightarrow> trm \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile> _ : _" [50, 50, 50] 50)
  and typings :: "env \<Rightarrow> rcd \<Rightarrow> rcdT \<Rightarrow> bool"  ("_ \<turnstile> _ [:] _" [50, 50, 50] 50)
where
  T_Var: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma>\<langle>i\<rangle> = \<lfloor>VarB U\<rfloor> \<Longrightarrow> T = \<up>\<^sub>\<tau> (Suc i) 0 U \<Longrightarrow> \<Gamma> \<turnstile> Var i : T"
| T_Abs: "VarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda>:T\<^sub>1. t\<^sub>2) : T\<^sub>1 \<rightarrow> \<down>\<^sub>\<tau> 1 0 T\<^sub>2"
| T_App: "\<Gamma> \<turnstile> t\<^sub>1 : T\<^sub>1\<^sub>1 \<rightarrow> T\<^sub>1\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile> t\<^sub>1 \<bullet> t\<^sub>2 : T\<^sub>1\<^sub>2"
| T_TAbs: "TVarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile> (\<lambda><:T\<^sub>1. t\<^sub>2) : (\<forall><:T\<^sub>1. T\<^sub>2)"
| T_TApp: "\<Gamma> \<turnstile> t\<^sub>1 : (\<forall><:T\<^sub>1\<^sub>1. T\<^sub>1\<^sub>2) \<Longrightarrow> \<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>1\<^sub>1 \<Longrightarrow>
    \<Gamma> \<turnstile> t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 : T\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]\<^sub>\<tau>"
| T_Sub: "\<Gamma> \<turnstile> t : S \<Longrightarrow> \<Gamma> \<turnstile> S <: T \<Longrightarrow> \<Gamma> \<turnstile> t : T"
| T_Let: "\<Gamma> \<turnstile> t\<^sub>1 : T\<^sub>1 \<Longrightarrow> \<turnstile> p : T\<^sub>1 \<Rightarrow> \<Delta> \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow>
    \<Gamma> \<turnstile> (LET p = t\<^sub>1 IN t\<^sub>2) : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T\<^sub>2"
| T_Rcd: "\<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> \<Gamma> \<turnstile> Rcd fs : RcdT fTs"
| T_Proj: "\<Gamma> \<turnstile> t : RcdT fTs \<Longrightarrow> fTs\<langle>l\<rangle>\<^sub>? = \<lfloor>T\<rfloor> \<Longrightarrow> \<Gamma> \<turnstile> t..l : T"
| T_Nil: "\<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Gamma> \<turnstile> [] [:] []"
| T_Cons: "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> fs\<langle>l\<rangle>\<^sub>? = \<bottom> \<Longrightarrow>
    \<Gamma> \<turnstile> (l, t) \<Colon> fs [:] (l, T) \<Colon> fTs"

theorem wf_typeE1:
  "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  "\<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f"
  by (induct set: typing typings) (blast elim: well_formedE_cases)+

theorem wf_typeE2:
  "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f T"
  "\<Gamma>' \<turnstile> fs [:] fTs \<Longrightarrow> (\<forall>(l, T) \<in> set fTs. \<Gamma>' \<turnstile>\<^sub>w\<^sub>f T) \<and>
     unique fTs \<and> (\<forall>l. (fs\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fTs\<langle>l\<rangle>\<^sub>? = \<bottom>))"
  apply (induct set: typing typings)
  apply simp
  apply (rule wf_liftB)
  apply assumption+
  apply (drule wf_typeE1)+
  apply (erule well_formedE_cases)+
  apply (rule wf_arrow)
  apply simp
  apply simp
  apply (rule wf_subst [of "[]", simplified])
  apply assumption
  apply (rule wf_Top)
  apply (erule well_formed_cases)
  apply assumption
  apply (rule wf_all)
  apply (drule wf_typeE1)
  apply (erule well_formedE_cases)
  apply simp  
  apply assumption
  apply (erule well_formed_cases)
  apply (rule wf_subst [of "[]", simplified])
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  apply (erule wf_subtypeE)
  apply assumption
  \<comment> \<open>records\<close>
  apply (erule wf_dec)
  apply (erule conjE)+
  apply (rule wf_RcdT)
  apply assumption+
  apply (erule well_formed_cases)
  apply (blast dest: assoc_set)
  apply simp
  apply simp
  done

lemmas ptyping_induct = ptyping_ptypings.inducts(1)
  [of _ _ _ _ "\<lambda>x y z. True", simplified True_simps, consumes 1,
   case_names P_Var P_Rcd]

lemmas ptypings_induct = ptyping_ptypings.inducts(2)
  [of _ _ _ "\<lambda>x y z. True", simplified True_simps, consumes 1,
   case_names P_Nil P_Cons]

lemmas typing_induct = typing_typings.inducts(1)
  [of _ _ _ _ "\<lambda>x y z. True", simplified True_simps, consumes 1,
   case_names T_Var T_Abs T_App T_TAbs T_TApp T_Sub T_Let T_Rcd T_Proj]

lemmas typings_induct = typing_typings.inducts(2)
  [of _ _ _ "\<lambda>x y z. True", simplified True_simps, consumes 1,
   case_names T_Nil T_Cons]

lemma narrow_type: \<comment> \<open>A.7\<close>
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> t : T \<Longrightarrow>
     \<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> t : T"
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> ts [:] Ts \<Longrightarrow>
     \<Gamma> \<turnstile> P <: Q \<Longrightarrow> \<Delta> @ TVarB P \<Colon> \<Gamma> \<turnstile> ts [:] Ts"
  apply (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" t T and "\<Delta> @ TVarB Q \<Colon> \<Gamma>" ts Ts
    arbitrary: \<Delta> and \<Delta> set: typing typings)
  apply simp_all
  apply (rule T_Var)
  apply (erule wfE_replace)
  apply (erule wf_subtypeE)
  apply simp+
  apply (case_tac "i < \<parallel>\<Delta>\<parallel>")
  apply simp
  apply (case_tac "i = \<parallel>\<Delta>\<parallel>")
  apply simp
  apply (simp split: nat.split nat.split_asm)+
  apply (rule T_Abs [simplified])
  apply (drule_tac x="VarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (rule_tac T\<^sub>1\<^sub>1=T\<^sub>1\<^sub>1 in T_App)
  apply simp+
  apply (rule T_TAbs)
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (rule_tac T\<^sub>1\<^sub>1=T\<^sub>1\<^sub>1 in T_TApp)
  apply simp
  apply (rule subtype_trans(2))
  apply assumption+
  apply (rule_tac S=S in T_Sub)
  apply simp
  apply (rule subtype_trans(2))
  apply assumption+
  \<comment> \<open>records\<close>
  apply (rule T_Let)
  apply blast
  apply assumption
  apply (drule_tac x="\<Delta> @ \<Delta>'" in meta_spec, drule meta_mp, rule refl)
  apply simp
  apply (rule T_Rcd)
  apply simp
  apply (rule T_Proj)
  apply blast
  apply assumption
  apply (rule T_Nil)
  apply (erule wfE_replace)
  apply (erule wf_subtypeE)
  apply simp+
  apply (rule T_Cons)
  apply simp+
  done

lemma typings_setD:
  assumes H: "\<Gamma> \<turnstile> fs [:] fTs"
  shows "(l, T) \<in> set fTs \<Longrightarrow> \<exists>t. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>t\<rfloor> \<and> \<Gamma> \<turnstile> t : T"
  using H
  by (induct arbitrary: l T rule: typings_induct) fastforce+

lemma subtype_refl':
  assumes t: "\<Gamma> \<turnstile> t : T"
  shows "\<Gamma> \<turnstile> T <: T"
proof (rule subtype_refl)
  from t show "\<Gamma> \<turnstile>\<^sub>w\<^sub>f" by (rule wf_typeE1)
  from t show "\<Gamma> \<turnstile>\<^sub>w\<^sub>f T" by (rule wf_typeE2)
qed

lemma Abs_type: \<comment> \<open>A.13(1)\<close>
  assumes H: "\<Gamma> \<turnstile> (\<lambda>:S. s) : T"
  shows "\<Gamma> \<turnstile> T <: U \<rightarrow> U' \<Longrightarrow>
    (\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> VarB S \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
      \<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 0 S' <: U' \<Longrightarrow> P) \<Longrightarrow> P"
  using H
proof (induct \<Gamma> "\<lambda>:S. s" T arbitrary: U U' S s P)
  case (T_Abs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  from \<open>\<Gamma> \<turnstile> T\<^sub>1 \<rightarrow> \<down>\<^sub>\<tau> 1 0 T\<^sub>2 <: U \<rightarrow> U'\<close>
  obtain ty1: "\<Gamma> \<turnstile> U <: T\<^sub>1" and ty2: "\<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 0 T\<^sub>2 <: U'"
    by cases simp_all
  from ty1 \<open>VarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2\<close> ty2
  show ?case by (rule T_Abs)
next
  case (T_Sub \<Gamma> S' T)
  from \<open>\<Gamma> \<turnstile> S' <: T\<close> and \<open>\<Gamma> \<turnstile> T <: U \<rightarrow> U'\<close>
  have "\<Gamma> \<turnstile> S' <: U \<rightarrow> U'" by (rule subtype_trans(1))
  then show ?case
    by (rule T_Sub) (rule T_Sub(5))
qed

lemma Abs_type':
  assumes H: "\<Gamma> \<turnstile> (\<lambda>:S. s) : U \<rightarrow> U'"
  and R: "\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> VarB S \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
    \<Gamma> \<turnstile> \<down>\<^sub>\<tau> 1 0 S' <: U' \<Longrightarrow> P"
  shows "P" using H subtype_refl' [OF H]
  by (rule Abs_type) (rule R)

lemma TAbs_type: \<comment> \<open>A.13(2)\<close>
  assumes H: "\<Gamma> \<turnstile> (\<lambda><:S. s) : T"
  shows "\<Gamma> \<turnstile> T <: (\<forall><:U. U') \<Longrightarrow>
    (\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> TVarB U \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
      TVarB U \<Colon> \<Gamma> \<turnstile> S' <: U' \<Longrightarrow> P) \<Longrightarrow> P"
  using H
proof (induct \<Gamma> "\<lambda><:S. s" T arbitrary: U U' S s P)
  case (T_TAbs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2)
  from \<open>\<Gamma> \<turnstile> (\<forall><:T\<^sub>1. T\<^sub>2) <: (\<forall><:U. U')\<close>
  obtain ty1: "\<Gamma> \<turnstile> U <: T\<^sub>1" and ty2: "TVarB U \<Colon> \<Gamma> \<turnstile> T\<^sub>2 <: U'"
    by cases simp_all
  from \<open>TVarB T\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2\<close>
  have "TVarB U \<Colon> \<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>2" using ty1
    by (rule narrow_type [of "[]", simplified])
  with ty1 show ?case using ty2 by (rule T_TAbs)
next
  case (T_Sub \<Gamma> S' T)
  from \<open>\<Gamma> \<turnstile> S' <: T\<close> and \<open>\<Gamma> \<turnstile> T <: (\<forall><:U. U')\<close>
  have "\<Gamma> \<turnstile> S' <: (\<forall><:U. U')" by (rule subtype_trans(1))
  then show ?case
    by (rule T_Sub) (rule T_Sub(5))
qed

lemma TAbs_type':
  assumes H: "\<Gamma> \<turnstile> (\<lambda><:S. s) : (\<forall><:U. U')"
  and R: "\<And>S'. \<Gamma> \<turnstile> U <: S \<Longrightarrow> TVarB U \<Colon> \<Gamma> \<turnstile> s : S' \<Longrightarrow>
    TVarB U \<Colon> \<Gamma> \<turnstile> S' <: U' \<Longrightarrow> P"
  shows "P" using H subtype_refl' [OF H]
  by (rule TAbs_type) (rule R)

text \<open>
In the proof of the preservation theorem, the following elimination rule
for typing judgements on record types will be useful:
\<close>

lemma Rcd_type1: \<comment> \<open>A.13(3)\<close>
  assumes H: "\<Gamma> \<turnstile> t : T"
  shows "t = Rcd fs \<Longrightarrow> \<Gamma> \<turnstile> T <: RcdT fTs \<Longrightarrow>
     \<forall>(l, U) \<in> set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<and> \<Gamma> \<turnstile> u : U"
  using H
  apply (induct arbitrary: fs fTs rule: typing_induct, simp_all)
  apply (drule meta_spec)+
  apply (drule meta_mp)
  apply (rule refl)
  apply (erule meta_mp)
  apply (rule subtype_trans(1))
  apply assumption+
  apply (erule subtyping.cases)
  apply simp_all
  apply (rule ballpI)
  apply (drule bpspec)
  apply assumption
  apply (erule exE conjE)+
  apply (drule typings_setD)
  apply assumption
  apply (erule exE conjE)+
  apply (rule exI conjI)+
  apply simp
  apply (erule T_Sub)
  apply assumption
  done

lemma Rcd_type1':
  assumes H: "\<Gamma> \<turnstile> Rcd fs : RcdT fTs"
  shows "\<forall>(l, U) \<in> set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<and> \<Gamma> \<turnstile> u : U"
  using H refl subtype_refl' [OF H]
  by (rule Rcd_type1)

text \<open>
Intuitively, this means that for a record @{term "Rcd fs"} of type @{term "RcdT fTs"},
each field with name @{term l} associated with a type @{term U} in @{term "fTs"}
must correspond to a field in @{term fs} with value @{term u}, where @{term u} has
type @{term U}. Thanks to the subsumption rule \<open>T_Sub\<close>, the typing judgement
for terms is not sensitive to the order of record fields. For example,
@{term [display] "\<Gamma> \<turnstile> Rcd [(l\<^sub>1, t\<^sub>1), (l\<^sub>2, t\<^sub>2), (l\<^sub>3, t\<^sub>3)] : RcdT [(l\<^sub>2, T\<^sub>2), (l\<^sub>1, T\<^sub>1)]"}
provided that \<open>\<Gamma> \<turnstile> t\<^sub>i : T\<^sub>i\<close>. Note however that this does not imply
@{term [display] "\<Gamma> \<turnstile> [(l\<^sub>1, t\<^sub>1), (l\<^sub>2, t\<^sub>2), (l\<^sub>3, t\<^sub>3)] [:] [(l\<^sub>2, T\<^sub>2), (l\<^sub>1, T\<^sub>1)]"}
In order for this statement to hold, we need to remove the field @{term "l\<^sub>3"}
and exchange the order of the fields @{term "l\<^sub>1"} and @{term "l\<^sub>2"}. This gives rise
to the following variant of the above elimination rule:
\<close>

lemma Rcd_type2:
  "\<Gamma> \<turnstile> Rcd fs : T \<Longrightarrow> \<Gamma> \<turnstile> T <: RcdT fTs \<Longrightarrow>
     \<Gamma> \<turnstile> map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs [:] fTs"
  apply (drule Rcd_type1)
  apply (rule refl)
  apply assumption
  apply (induct fTs rule: list.induct)
  apply simp
  apply (rule T_Nil)
  apply (erule wf_subtypeE)
  apply assumption
  apply (simp add: split_paired_all)
  apply (rule T_Cons)
  apply (drule_tac x=a and y=b in bpspec)
  apply simp
  apply (erule exE conjE)+
  apply simp
  apply (rename_tac list)
  apply (subgoal_tac "\<Gamma> \<turnstile> RcdT ((a, b) \<Colon> list) <: RcdT list")
  apply (erule meta_mp)
  apply (erule subtype_trans(1))
  apply assumption
  apply (erule wf_subtypeE)
  apply (rule SA_Rcd)
  apply assumption+
  apply (erule well_formed_cases)
  apply simp
  apply (rule ballpI)
  apply (rule exI)
  apply (rule conjI)
  apply (rule_tac [2] subtype_refl)
  apply simp
  apply assumption
  apply (erule well_formed_cases)
  apply (erule_tac x=l and y=Ta in bpspec)
  apply simp
  apply (erule wf_subtypeE)
  apply (erule well_formed_cases)
  apply simp
  done

lemma Rcd_type2':
  assumes H: "\<Gamma> \<turnstile> Rcd fs : RcdT fTs"
  shows "\<Gamma> \<turnstile> map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs [:] fTs"
  using H subtype_refl' [OF H]
  by (rule Rcd_type2)

lemma T_eq: "\<Gamma> \<turnstile> t : T \<Longrightarrow> T = T' \<Longrightarrow> \<Gamma> \<turnstile> t : T'" by simp

lemma ptyping_length [simp]:
  "\<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> \<parallel>p\<parallel>\<^sub>p = \<parallel>\<Delta>\<parallel>"
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<parallel>fps\<parallel>\<^sub>r = \<parallel>\<Delta>\<parallel>"
  by (induct set: ptyping ptypings) simp_all

lemma lift_ptyping:
  "\<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> \<turnstile> \<up>\<^sub>p n k p : \<up>\<^sub>\<tau> n k T \<Rightarrow> \<up>\<^sub>e n k \<Delta>"
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<turnstile> \<up>\<^sub>r\<^sub>p n k fps [:] \<up>\<^sub>r\<^sub>\<tau> n k fTs \<Rightarrow> \<up>\<^sub>e n k \<Delta>"
  apply (induct set: ptyping ptypings)
  apply simp_all
  apply (rule P_Var)
  apply (erule P_Rcd)
  apply (rule P_Nil)
  apply (drule_tac p="\<up>\<^sub>p n k p" and fps="\<up>\<^sub>r\<^sub>p n k fps" in P_Cons)
  apply simp_all
  done

lemma type_weaken:
  "\<Delta> @ \<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow>
     \<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up> 1 \<parallel>\<Delta>\<parallel> t : \<up>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
  "\<Delta> @ \<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>w\<^sub>f\<^sub>B B \<Longrightarrow>
     \<up>\<^sub>e 1 0 \<Delta> @ B \<Colon> \<Gamma> \<turnstile> \<up>\<^sub>r 1 \<parallel>\<Delta>\<parallel> fs [:] \<up>\<^sub>r\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> fTs"
  apply (induct "\<Delta> @ \<Gamma>" t T and "\<Delta> @ \<Gamma>" fs fTs
    arbitrary: \<Delta> and \<Delta> set: typing typings)
  apply simp_all
  apply (rule conjI)
  apply (rule impI)
  apply (rule T_Var)
  apply (erule wfE_weaken)
  apply simp+
  apply (rule impI)
  apply (rule T_Var)
  apply (erule wfE_weaken)
  apply assumption
  apply (subgoal_tac "Suc i - \<parallel>\<Delta>\<parallel> = Suc (i - \<parallel>\<Delta>\<parallel>)")
  apply simp
  apply arith
  apply (rule refl)
  apply (rule T_Abs [simplified])
  apply (drule_tac x="VarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (rule_tac T\<^sub>1\<^sub>1="\<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> T\<^sub>1\<^sub>1" in T_App)
  apply simp
  apply simp
  apply (rule T_TAbs)
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (erule_tac T_TApp [THEN T_eq])
  apply (drule subtype_weaken)
  apply simp+
  apply (case_tac \<Delta>)
  apply (simp add: liftT_substT_strange [of _ 0, simplified])+
  apply (rule_tac S="\<up>\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> S" in T_Sub)
  apply simp
  apply (drule subtype_weaken)
  apply simp+
  \<comment> \<open>records\<close>
  apply (drule_tac x="\<Delta> @ \<Delta>'" in meta_spec)
  apply (drule meta_mp)
  apply simp
  apply simp
  apply (drule_tac \<Gamma>="\<up>\<^sub>e (Suc 0) 0 \<Delta>' @ B \<Colon> \<Gamma>" in T_Let)
  apply (erule lift_ptyping)
  apply assumption
  apply (simp add: ac_simps)
  apply (rule T_Rcd)
  apply simp
  apply (rule_tac fTs="\<up>\<^sub>r\<^sub>\<tau> (Suc 0) \<parallel>\<Delta>\<parallel> fTs" in T_Proj)
  apply simp
  apply (erule_tac liftrT_assoc_Some)
  apply (rule T_Nil)
  apply (erule wfE_weaken)
  apply assumption
  apply (rule T_Cons)
  apply simp+
  done

lemma type_weaken': \<comment> \<open>A.5(6)\<close>
  "\<Gamma> \<turnstile> t : T \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile>\<^sub>w\<^sub>f \<Longrightarrow> \<Delta> @ \<Gamma> \<turnstile> \<up> \<parallel>\<Delta>\<parallel> 0 t : \<up>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T"
  apply (induct \<Delta>)
  apply simp
  apply simp
  apply (erule well_formedE_cases)
  apply simp
  apply (drule_tac B=a in type_weaken(1) [of "[]", simplified])
  apply simp+
  done

text \<open>
The substitution lemmas are now proved by mutual induction on the derivations of
the typing derivations for terms and lists of fields.
\<close>

lemma subst_ptyping:
  "\<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> \<turnstile> p[k \<mapsto>\<^sub>\<tau> U]\<^sub>p : T[k \<mapsto>\<^sub>\<tau> U]\<^sub>\<tau> \<Rightarrow> \<Delta>[k \<mapsto>\<^sub>\<tau> U]\<^sub>e"
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<turnstile> fps[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>p [:] fTs[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>\<tau> \<Rightarrow> \<Delta>[k \<mapsto>\<^sub>\<tau> U]\<^sub>e"
  apply (induct set: ptyping ptypings)
  apply simp_all
  apply (rule P_Var)
  apply (erule P_Rcd)
  apply (rule P_Nil)
  apply (drule_tac p="p[k \<mapsto>\<^sub>\<tau> U]\<^sub>p" and fps="fps[k \<mapsto>\<^sub>\<tau> U]\<^sub>r\<^sub>p" in P_Cons)
  apply simp+
  done

theorem subst_type: \<comment> \<open>A.8\<close>
  "\<Delta> @ VarB U \<Colon> \<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile> u : U \<Longrightarrow>
     \<down>\<^sub>e 1 0 \<Delta> @ \<Gamma> \<turnstile> t[\<parallel>\<Delta>\<parallel> \<mapsto> u] : \<down>\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> T"
  "\<Delta> @ VarB U \<Colon> \<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> \<Gamma> \<turnstile> u : U \<Longrightarrow>
     \<down>\<^sub>e 1 0 \<Delta> @ \<Gamma> \<turnstile> fs[\<parallel>\<Delta>\<parallel> \<mapsto> u]\<^sub>r [:] \<down>\<^sub>r\<^sub>\<tau> 1 \<parallel>\<Delta>\<parallel> fTs"
  apply (induct "\<Delta> @ VarB U \<Colon> \<Gamma>" t T and "\<Delta> @ VarB U \<Colon> \<Gamma>" fs fTs
    arbitrary: \<Delta> and \<Delta> set: typing typings)
  apply simp
  apply (rule conjI)
  apply (rule impI)
  apply simp
  apply (drule_tac \<Delta>="\<Delta>[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e" in type_weaken')
  apply (rule wfE_subst)
  apply assumption
  apply (rule wf_Top)
  apply simp
  apply (rule impI conjI)+
  apply (simp split: nat.split_asm)
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (rule wf_Top)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (rename_tac nat)
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply simp
  apply (rule impI)
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (rule wf_Top)
  apply simp
  apply (subgoal_tac "Suc (\<parallel>\<Delta>\<parallel> - Suc 0) = \<parallel>\<Delta>\<parallel>")
  apply (simp (no_asm_simp))
  apply arith
  apply simp
  apply (drule_tac x="VarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply (rule T_Abs [THEN T_eq])
  apply simp
  apply (simp add: substT_substT [symmetric])
  apply simp
  apply (rule_tac T\<^sub>1\<^sub>1="T\<^sub>1\<^sub>1[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>" in T_App)
  apply simp+
  apply (rule T_TAbs)
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply simp
  apply (rule T_TApp [THEN T_eq])
  apply simp
  apply (rule subst_subtype [simplified])
  apply assumption
  apply (simp add: substT_substT [symmetric])
  apply (rule_tac S="S[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>" in T_Sub)
  apply simp
  apply simp
  apply (rule subst_subtype [simplified])
  apply assumption
  \<comment> \<open>records\<close>
  apply simp
  apply (drule meta_spec)+
  apply (drule meta_mp, rule refl)+
  apply (drule_tac \<Gamma>="\<Delta>'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma>" in T_Let)
  apply (erule subst_ptyping)
  apply simp
  apply (simp add: ac_simps)
  apply simp
  apply (rule T_Rcd)
  apply simp
  apply simp
  apply (rule_tac fTs="fTs[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>r\<^sub>\<tau>" in T_Proj)
  apply simp
  apply (erule_tac substrTT_assoc_Some)
  apply simp
  apply (rule T_Nil)
  apply (erule wfE_subst)
  apply (rule wf_Top)
  apply simp
  apply (rule T_Cons)
  apply simp+
  done

theorem substT_type: \<comment> \<open>A.11\<close>
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> t : T \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
     \<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> t[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P] : T[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>"
  "\<Delta> @ TVarB Q \<Colon> \<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> \<Gamma> \<turnstile> P <: Q \<Longrightarrow>
     \<Delta>[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma> \<turnstile> fs[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>r [:] fTs[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>r\<^sub>\<tau>"
  apply (induct "\<Delta> @ TVarB Q \<Colon> \<Gamma>" t T and "\<Delta> @ TVarB Q \<Colon> \<Gamma>" fs fTs
    arbitrary: \<Delta> and \<Delta> set: typing typings)
  apply simp_all
  apply (rule impI conjI)+
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (erule wf_subtypeE)
  apply assumption
  apply (simp split: nat.split_asm)
  apply (subgoal_tac "\<parallel>\<Delta>\<parallel> \<le> i - Suc 0")
  apply (rename_tac nat)
  apply (subgoal_tac "i - Suc \<parallel>\<Delta>\<parallel> = nat")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply simp
  apply (rule impI)
  apply (case_tac "i = \<parallel>\<Delta>\<parallel>")
  apply simp
  apply (rule T_Var)
  apply (erule wfE_subst)
  apply (erule wf_subtypeE)
  apply assumption
  apply simp
  apply (subgoal_tac "i < \<parallel>\<Delta>\<parallel>")
  apply (subgoal_tac "Suc (\<parallel>\<Delta>\<parallel> - Suc 0) = \<parallel>\<Delta>\<parallel>")
  apply (simp (no_asm_simp))
  apply arith
  apply arith
  apply (rule T_Abs [THEN T_eq])
  apply (drule_tac x="VarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (simp add: substT_substT [symmetric])
  apply (rule_tac T\<^sub>1\<^sub>1="T\<^sub>1\<^sub>1[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>" in T_App)
  apply simp+
  apply (rule T_TAbs)
  apply (drule_tac x="TVarB T\<^sub>1 \<Colon> \<Delta>" in meta_spec)
  apply simp
  apply (rule T_TApp [THEN T_eq])
  apply simp
  apply (rule substT_subtype)
  apply assumption
  apply assumption
  apply (simp add: substT_substT [symmetric])
  apply (rule_tac S="S[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>\<tau>" in T_Sub)
  apply simp
  apply (rule substT_subtype)
  apply assumption
  apply assumption
  \<comment> \<open>records\<close>
  apply (drule meta_spec)+
  apply (drule meta_mp, rule refl)+
  apply (drule_tac \<Gamma>="\<Delta>'[0 \<mapsto>\<^sub>\<tau> P]\<^sub>e @ \<Gamma>" in T_Let)
  apply (erule subst_ptyping)
  apply simp
  apply (simp add: ac_simps)
  apply (rule T_Rcd)
  apply simp
  apply (rule_tac fTs="fTs[\<parallel>\<Delta>\<parallel> \<mapsto>\<^sub>\<tau> P]\<^sub>r\<^sub>\<tau>" in T_Proj)
  apply simp
  apply (erule_tac substrTT_assoc_Some)
  apply (rule T_Nil)
  apply (erule wfE_subst)
  apply (erule wf_subtypeE)
  apply assumption
  apply (rule T_Cons)
  apply simp+
  done


subsection \<open>Evaluation\<close>

text \<open>
\label{sec:evaluation-rcd}
The definition of canonical values is extended with a clause saying that
a record @{term "Rcd fs"} is a canonical value if all fields contain
canonical values:
\<close>

inductive_set
  "value" :: "trm set"
where
  Abs: "(\<lambda>:T. t) \<in> value"
| TAbs: "(\<lambda><:T. t) \<in> value"
| Rcd: "\<forall>(l, t) \<in> set fs. t \<in> value \<Longrightarrow> Rcd fs \<in> value"

text \<open>
In order to formalize the evaluation rule for \<open>LET\<close>, we introduce another
relation \<open>\<turnstile> p \<rhd> t \<Rightarrow> ts\<close> expressing that a pattern @{term p} matches a
term @{term t}. The relation also yields a list of terms @{term ts} corresponding
to the variables in the pattern. The relation is defined simultaneously with another
relation \<open>\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts\<close> for matching a list of field patterns @{term fps}
against a list of fields @{term fs}:
\<close>

inductive
  match :: "pat \<Rightarrow> trm \<Rightarrow> trm list \<Rightarrow> bool"  ("\<turnstile> _ \<rhd> _ \<Rightarrow> _" [50, 50, 50] 50)
  and matchs :: "rpat \<Rightarrow> rcd \<Rightarrow> trm list \<Rightarrow> bool"  ("\<turnstile> _ [\<rhd>] _ \<Rightarrow> _" [50, 50, 50] 50)
where
  M_PVar: "\<turnstile> PVar T \<rhd> t \<Rightarrow> [t]"
| M_Rcd: "\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts \<Longrightarrow> \<turnstile> PRcd fps \<rhd> Rcd fs \<Rightarrow> ts"
| M_Nil: "\<turnstile> [] [\<rhd>] fs \<Rightarrow> []"
| M_Cons: "fs\<langle>l\<rangle>\<^sub>? = \<lfloor>t\<rfloor> \<Longrightarrow> \<turnstile> p \<rhd> t \<Rightarrow> ts \<Longrightarrow> \<turnstile> fps [\<rhd>] fs \<Rightarrow> us \<Longrightarrow>
    \<turnstile> (l, p) \<Colon> fps [\<rhd>] fs \<Rightarrow> ts @ us"

text \<open>
The rules of the evaluation relation for the calculus with records are as follows:
\<close>

inductive
  eval :: "trm \<Rightarrow> trm \<Rightarrow> bool"  (infixl "\<longmapsto>" 50)
  and evals :: "rcd \<Rightarrow> rcd \<Rightarrow> bool"  (infixl "[\<longmapsto>]" 50)
where
  E_Abs: "v\<^sub>2 \<in> value \<Longrightarrow> (\<lambda>:T\<^sub>1\<^sub>1. t\<^sub>1\<^sub>2) \<bullet> v\<^sub>2 \<longmapsto> t\<^sub>1\<^sub>2[0 \<mapsto> v\<^sub>2]"
| E_TAbs: "(\<lambda><:T\<^sub>1\<^sub>1. t\<^sub>1\<^sub>2) \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]"
| E_App1: "t \<longmapsto> t' \<Longrightarrow> t \<bullet> u \<longmapsto> t' \<bullet> u"
| E_App2: "v \<in> value \<Longrightarrow> t \<longmapsto> t' \<Longrightarrow> v \<bullet> t \<longmapsto> v \<bullet> t'"
| E_TApp: "t \<longmapsto> t' \<Longrightarrow> t \<bullet>\<^sub>\<tau> T \<longmapsto> t' \<bullet>\<^sub>\<tau> T"
| E_LetV: "v \<in> value \<Longrightarrow> \<turnstile> p \<rhd> v \<Rightarrow> ts \<Longrightarrow> (LET p = v IN t) \<longmapsto> t[0 \<mapsto>\<^sub>s ts]"
| E_ProjRcd: "fs\<langle>l\<rangle>\<^sub>? = \<lfloor>v\<rfloor> \<Longrightarrow> v \<in> value \<Longrightarrow> Rcd fs..l \<longmapsto> v"
| E_Proj: "t \<longmapsto> t' \<Longrightarrow> t..l \<longmapsto> t'..l"
| E_Rcd: "fs [\<longmapsto>] fs' \<Longrightarrow> Rcd fs \<longmapsto> Rcd fs'"
| E_Let: "t \<longmapsto> t' \<Longrightarrow> (LET p = t IN u) \<longmapsto> (LET p = t' IN u)"
| E_hd: "t \<longmapsto> t' \<Longrightarrow> (l, t) \<Colon> fs [\<longmapsto>] (l, t') \<Colon> fs"
| E_tl: "v \<in> value \<Longrightarrow> fs [\<longmapsto>] fs' \<Longrightarrow> (l, v) \<Colon> fs [\<longmapsto>] (l, v) \<Colon> fs'"

text \<open>
The relation @{term "t \<longmapsto> t'"} is defined simultaneously with
a relation \mbox{@{term "fs [\<longmapsto>] fs'"}} for evaluating record fields.
The ``immediate'' reductions, namely pattern matching and projection,
are described by the rules \<open>E_LetV\<close> and \<open>E_ProjRcd\<close>, respectively,
whereas \<open>E_Proj\<close>, \<open>E_Rcd\<close>, \<open>E_Let\<close>, \<open>E_hd\<close> and
\<open>E_tl\<close> are congruence rules.
\<close>

lemmas matchs_induct = match_matchs.inducts(2)
  [of _ _ _ "\<lambda>x y z. True", simplified True_simps, consumes 1,
   case_names M_Nil M_Cons]

lemmas evals_induct = eval_evals.inducts(2)
  [of _ _ "\<lambda>x y. True", simplified True_simps, consumes 1,
   case_names E_hd E_tl]

lemma matchs_mono:
  assumes H: "\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts"
  shows "fps\<langle>l\<rangle>\<^sub>? = \<bottom> \<Longrightarrow> \<turnstile> fps [\<rhd>] (l, t) \<Colon> fs \<Rightarrow> ts"
  using H
  apply (induct rule: matchs_induct)
  apply (rule M_Nil)
  apply (simp split: if_split_asm)
  apply (rule M_Cons)
  apply simp_all
  done

lemma matchs_eq:
  assumes H: "\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts"
  shows "\<forall>(l, p) \<in> set fps. fs\<langle>l\<rangle>\<^sub>? = fs'\<langle>l\<rangle>\<^sub>? \<Longrightarrow> \<turnstile> fps [\<rhd>] fs' \<Rightarrow> ts"
  using H
  apply (induct rule: matchs_induct)
  apply (rule M_Nil)
  apply (rule M_Cons)
  apply auto
  done

lemma reorder_eq:
  assumes H: "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta>"
  shows "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<Longrightarrow>
    \<forall>(l, p) \<in> set fps. fs\<langle>l\<rangle>\<^sub>? = (map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs)\<langle>l\<rangle>\<^sub>?"
  using H
  by (induct rule: ptypings_induct) auto

lemma matchs_reorder:
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<Longrightarrow>
    \<turnstile> fps [\<rhd>] fs \<Rightarrow> ts \<Longrightarrow> \<turnstile> fps [\<rhd>] map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs \<Rightarrow> ts"
  by (rule matchs_eq [OF _ reorder_eq], assumption+)

lemma matchs_reorder':
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<Longrightarrow>
     \<turnstile> fps [\<rhd>] map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs \<Rightarrow> ts \<Longrightarrow> \<turnstile> fps [\<rhd>] fs \<Rightarrow> ts"
  by (rule matchs_eq [OF _ reorder_eq [THEN ball_eq_sym]], assumption+)

theorem matchs_tl:
  assumes H: "\<turnstile> fps [\<rhd>] (l, t) \<Colon> fs \<Rightarrow> ts"
  shows "fps\<langle>l\<rangle>\<^sub>? = \<bottom> \<Longrightarrow> \<turnstile> fps [\<rhd>] fs \<Rightarrow> ts"
  using H
  apply (induct fps "(l, t) \<Colon> fs" ts arbitrary: l t fs rule: matchs_induct)
  apply (simp_all split: if_split_asm)
  apply (rule M_Nil)
  apply (rule M_Cons)
  apply auto
  done

theorem match_length:
  "\<turnstile> p \<rhd> t \<Rightarrow> ts \<Longrightarrow> \<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> \<parallel>ts\<parallel> = \<parallel>\<Delta>\<parallel>"
  "\<turnstile> fps [\<rhd>] ft \<Rightarrow> ts \<Longrightarrow> \<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<parallel>ts\<parallel> = \<parallel>\<Delta>\<parallel>"
  by (induct arbitrary: T \<Delta> and fTs \<Delta> set: match matchs)
    (erule ptyping.cases ptypings.cases, simp+)+

text \<open>
In the proof of the preservation theorem
for the calculus with records, we need the following lemma relating
the matching and typing judgements for patterns,
which means that well-typed matching preserves typing. Although this property
will only be used for @{term "\<Gamma>\<^sub>1 = []"} later, the statement must be proved in
a more general form in order for the induction to go through.
\<close>

theorem match_type: \<comment> \<open>A.17\<close>
  "\<turnstile> p : T\<^sub>1 \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma>\<^sub>2 \<turnstile> t\<^sub>1 : T\<^sub>1 \<Longrightarrow>
     \<Gamma>\<^sub>1 @ \<Delta> @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<turnstile> p \<rhd> t\<^sub>1 \<Rightarrow> ts \<Longrightarrow>
       \<down>\<^sub>e \<parallel>\<Delta>\<parallel> 0 \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2[\<parallel>\<Gamma>\<^sub>1\<parallel> \<mapsto>\<^sub>s ts] : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> \<parallel>\<Gamma>\<^sub>1\<parallel> T\<^sub>2"
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> \<Gamma>\<^sub>2 \<turnstile> fs [:] fTs \<Longrightarrow>
     \<Gamma>\<^sub>1 @ \<Delta> @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2 : T\<^sub>2 \<Longrightarrow> \<turnstile> fps [\<rhd>] fs \<Rightarrow> ts \<Longrightarrow>
       \<down>\<^sub>e \<parallel>\<Delta>\<parallel> 0 \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2[\<parallel>\<Gamma>\<^sub>1\<parallel> \<mapsto>\<^sub>s ts] : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> \<parallel>\<Gamma>\<^sub>1\<parallel> T\<^sub>2"
proof (induct arbitrary: \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 t\<^sub>1 t\<^sub>2 T\<^sub>2 ts and \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 fs t\<^sub>2 T\<^sub>2 ts set: ptyping ptypings)
  case (P_Var T \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 t\<^sub>1 t\<^sub>2 T\<^sub>2 ts)
  from P_Var have "\<Gamma>\<^sub>1[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>e @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2[\<parallel>\<Gamma>\<^sub>1\<parallel> \<mapsto> t\<^sub>1] : T\<^sub>2[\<parallel>\<Gamma>\<^sub>1\<parallel> \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
    by - (rule subst_type [simplified], simp_all)
  moreover from P_Var(3) have "ts = [t\<^sub>1]" by cases simp_all
  ultimately show ?case by simp
next
  case (P_Rcd fps fTs \<Delta> \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 t\<^sub>1 t\<^sub>2 T\<^sub>2 ts)
  from P_Rcd(5) obtain fs where
    t\<^sub>1: "t\<^sub>1 = Rcd fs" and fps: "\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts" by cases simp_all
  with P_Rcd have fs: "\<Gamma>\<^sub>2 \<turnstile> Rcd fs : RcdT fTs" by simp
  hence "\<Gamma>\<^sub>2 \<turnstile> map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs [:] fTs"
    by (rule Rcd_type2')
  moreover note P_Rcd(4)
  moreover from fs have "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<and> \<Gamma>\<^sub>2 \<turnstile> u : U"
    by (rule Rcd_type1')
  hence "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor>" by blast
  with P_Rcd(1) have "\<turnstile> fps [\<rhd>] map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs \<Rightarrow> ts"
    using fps by (rule matchs_reorder)
  ultimately show ?case by (rule P_Rcd)
next
  case (P_Nil \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 fs t\<^sub>2 T\<^sub>2 ts)
  from P_Nil(3) have "ts = []" by cases simp_all
  with P_Nil show ?case by simp
next
  case (P_Cons p T \<Delta>\<^sub>1 fps fTs \<Delta>\<^sub>2 l \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 fs t\<^sub>2 T\<^sub>2 ts)
  from P_Cons(8) obtain t ts\<^sub>1 ts\<^sub>2 where
    t: "fs\<langle>l\<rangle>\<^sub>? = \<lfloor>t\<rfloor>" and p: "\<turnstile> p \<rhd> t \<Rightarrow> ts\<^sub>1" and fps: "\<turnstile> fps [\<rhd>] fs \<Rightarrow> ts\<^sub>2"
    and ts: "ts = ts\<^sub>1 @ ts\<^sub>2" by cases simp_all
  from P_Cons(6) t fps obtain fs' where
    fps': "\<turnstile> fps [\<rhd>] (l, t) \<Colon> fs' \<Rightarrow> ts\<^sub>2" and tT: "\<Gamma>\<^sub>2 \<turnstile> t : T" and fs': "\<Gamma>\<^sub>2 \<turnstile> fs' [:] fTs"
    and l: "fs'\<langle>l\<rangle>\<^sub>? = \<bottom>" by cases auto
  from P_Cons have "(\<Gamma>\<^sub>1 @ \<up>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 \<Delta>\<^sub>2) @ \<Delta>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2 : T\<^sub>2" by simp
  with tT have ts\<^sub>1: "\<down>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 (\<Gamma>\<^sub>1 @ \<up>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 \<Delta>\<^sub>2) @ \<Gamma>\<^sub>2 \<turnstile>
    t\<^sub>2[\<parallel>\<Gamma>\<^sub>1 @ \<up>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 \<Delta>\<^sub>2\<parallel> \<mapsto>\<^sub>s ts\<^sub>1] : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<^sub>1\<parallel> \<parallel>\<Gamma>\<^sub>1 @ \<up>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> 0 \<Delta>\<^sub>2\<parallel> T\<^sub>2"
    using p by (rule P_Cons)
  from fps' P_Cons(5) have "\<turnstile> fps [\<rhd>] fs' \<Rightarrow> ts\<^sub>2" by (rule matchs_tl)
  with fs' ts\<^sub>1 [simplified]
  have "\<down>\<^sub>e \<parallel>\<Delta>\<^sub>2\<parallel> 0 (\<down>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> \<parallel>\<Delta>\<^sub>2\<parallel> \<Gamma>\<^sub>1) @ \<Gamma>\<^sub>2 \<turnstile> t\<^sub>2[\<parallel>\<Gamma>\<^sub>1\<parallel> + \<parallel>\<Delta>\<^sub>2\<parallel> \<mapsto>\<^sub>s ts\<^sub>1][\<parallel>\<down>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> \<parallel>\<Delta>\<^sub>2\<parallel> \<Gamma>\<^sub>1\<parallel> \<mapsto>\<^sub>s ts\<^sub>2] :
    \<down>\<^sub>\<tau> \<parallel>\<Delta>\<^sub>2\<parallel> \<parallel>\<down>\<^sub>e \<parallel>\<Delta>\<^sub>1\<parallel> \<parallel>\<Delta>\<^sub>2\<parallel> \<Gamma>\<^sub>1\<parallel> (\<down>\<^sub>\<tau> \<parallel>\<Delta>\<^sub>1\<parallel> (\<parallel>\<Gamma>\<^sub>1\<parallel> + \<parallel>\<Delta>\<^sub>2\<parallel>) T\<^sub>2)"
    by (rule P_Cons(4))
  thus ?case by (simp add: decE_decE [of _ 0, simplified]
    match_length(2) [OF fps P_Cons(3)] ts)
qed

lemma evals_labels [simp]:
  assumes H: "fs [\<longmapsto>] fs'"
  shows "(fs\<langle>l\<rangle>\<^sub>? = \<bottom>) = (fs'\<langle>l\<rangle>\<^sub>? = \<bottom>)" using H
  by (induct rule: evals_induct) simp_all

theorem preservation: \<comment> \<open>A.20\<close>
  "\<Gamma> \<turnstile> t : T \<Longrightarrow> t \<longmapsto> t' \<Longrightarrow> \<Gamma> \<turnstile> t' : T"
  "\<Gamma> \<turnstile> fs [:] fTs \<Longrightarrow> fs [\<longmapsto>] fs' \<Longrightarrow> \<Gamma> \<turnstile> fs' [:] fTs"
proof (induct arbitrary: t' and fs' set: typing typings)
  case (T_Var \<Gamma> i U T t')
  from \<open>Var i \<longmapsto> t'\<close>
  show ?case by cases
next
  case (T_Abs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2 t')
  from \<open>(\<lambda>:T\<^sub>1. t\<^sub>2) \<longmapsto> t'\<close>
  show ?case by cases
next
  case (T_App \<Gamma> t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 t\<^sub>2 t')
  from \<open>t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t'\<close>
  show ?case
  proof cases
    case (E_Abs T\<^sub>1\<^sub>1' t\<^sub>1\<^sub>2)
    with T_App have "\<Gamma> \<turnstile> (\<lambda>:T\<^sub>1\<^sub>1'. t\<^sub>1\<^sub>2) : T\<^sub>1\<^sub>1 \<rightarrow> T\<^sub>1\<^sub>2" by simp
    then obtain S'
      where T\<^sub>1\<^sub>1: "\<Gamma> \<turnstile> T\<^sub>1\<^sub>1 <: T\<^sub>1\<^sub>1'"
      and t\<^sub>1\<^sub>2: "VarB T\<^sub>1\<^sub>1' \<Colon> \<Gamma> \<turnstile> t\<^sub>1\<^sub>2 : S'"
      and S': "\<Gamma> \<turnstile> S'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau> <: T\<^sub>1\<^sub>2" by (rule Abs_type' [simplified]) blast
    from \<open>\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1\<close>
    have "\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1'" using T\<^sub>1\<^sub>1 by (rule T_Sub)
    with t\<^sub>1\<^sub>2 have "\<Gamma> \<turnstile> t\<^sub>1\<^sub>2[0 \<mapsto> t\<^sub>2] : S'[0 \<mapsto>\<^sub>\<tau> Top]\<^sub>\<tau>"
      by (rule subst_type [where \<Delta>="[]", simplified])
    hence "\<Gamma> \<turnstile> t\<^sub>1\<^sub>2[0 \<mapsto> t\<^sub>2] : T\<^sub>1\<^sub>2" using S' by (rule T_Sub)
    with E_Abs show ?thesis by simp
  next
    case (E_App1 t'')
    from \<open>t\<^sub>1 \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : T\<^sub>1\<^sub>1 \<rightarrow> T\<^sub>1\<^sub>2" by (rule T_App)
    hence "\<Gamma> \<turnstile> t'' \<bullet> t\<^sub>2 : T\<^sub>1\<^sub>2" using \<open>\<Gamma> \<turnstile> t\<^sub>2 : T\<^sub>1\<^sub>1\<close>
      by (rule typing_typings.T_App)
    with E_App1 show ?thesis by simp
  next
    case (E_App2 t'')
    from \<open>t\<^sub>2 \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : T\<^sub>1\<^sub>1" by (rule T_App)
    with T_App(1) have "\<Gamma> \<turnstile> t\<^sub>1 \<bullet> t'' : T\<^sub>1\<^sub>2"
      by (rule typing_typings.T_App)
    with E_App2 show ?thesis by simp
  qed
next
  case (T_TAbs T\<^sub>1 \<Gamma> t\<^sub>2 T\<^sub>2 t')
  from \<open>(\<lambda><:T\<^sub>1. t\<^sub>2) \<longmapsto> t'\<close>
  show ?case by cases
next
  case (T_TApp \<Gamma> t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2 t')
  from \<open>t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t'\<close>
  show ?case
  proof cases
    case (E_TAbs T\<^sub>1\<^sub>1' t\<^sub>1\<^sub>2)
    with T_TApp have "\<Gamma> \<turnstile> (\<lambda><:T\<^sub>1\<^sub>1'. t\<^sub>1\<^sub>2) : (\<forall><:T\<^sub>1\<^sub>1. T\<^sub>1\<^sub>2)" by simp
    then obtain S'
      where "TVarB T\<^sub>1\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>1\<^sub>2 : S'"
      and "TVarB T\<^sub>1\<^sub>1 \<Colon> \<Gamma> \<turnstile> S' <: T\<^sub>1\<^sub>2" by (rule TAbs_type') blast
    hence "TVarB T\<^sub>1\<^sub>1 \<Colon> \<Gamma> \<turnstile> t\<^sub>1\<^sub>2 : T\<^sub>1\<^sub>2" by (rule T_Sub)
    hence "\<Gamma> \<turnstile> t\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2] : T\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]\<^sub>\<tau>" using T_TApp(3)
      by (rule substT_type [where \<Delta>="[]", simplified])
    with E_TAbs show ?thesis by simp
  next
    case (E_TApp t'')
    from \<open>t\<^sub>1 \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : (\<forall><:T\<^sub>1\<^sub>1. T\<^sub>1\<^sub>2)" by (rule T_TApp)
    hence "\<Gamma> \<turnstile> t'' \<bullet>\<^sub>\<tau> T\<^sub>2 : T\<^sub>1\<^sub>2[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]\<^sub>\<tau>" using \<open>\<Gamma> \<turnstile> T\<^sub>2 <: T\<^sub>1\<^sub>1\<close>
      by (rule typing_typings.T_TApp)
    with E_TApp show ?thesis by simp
  qed
next
  case (T_Sub \<Gamma> t S T t')
  from \<open>t \<longmapsto> t'\<close>
  have "\<Gamma> \<turnstile> t' : S" by (rule T_Sub)
  then show ?case using \<open>\<Gamma> \<turnstile> S <: T\<close>
    by (rule typing_typings.T_Sub)
next
  case (T_Let \<Gamma> t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2 t')
  from \<open>(LET p = t\<^sub>1 IN t\<^sub>2) \<longmapsto> t'\<close>
  show ?case
  proof cases
    case (E_LetV ts)
    from T_Let (3,1,4) \<open>\<turnstile> p \<rhd> t\<^sub>1 \<Rightarrow> ts\<close>
    have "\<Gamma> \<turnstile> t\<^sub>2[0 \<mapsto>\<^sub>s ts] : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T\<^sub>2"
      by (rule match_type(1) [of _ _ _ _ _ "[]", simplified])
    with E_LetV show ?thesis by simp
  next
    case (E_Let t'')
    from \<open>t\<^sub>1 \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : T\<^sub>1" by (rule T_Let)
    hence "\<Gamma> \<turnstile> (LET p = t'' IN t\<^sub>2) : \<down>\<^sub>\<tau> \<parallel>\<Delta>\<parallel> 0 T\<^sub>2" using T_Let(3,4)
      by (rule typing_typings.T_Let)
    with E_Let show ?thesis by simp
  qed
next
  case (T_Rcd \<Gamma> fs fTs t')
  from \<open>Rcd fs \<longmapsto> t'\<close>
  obtain fs' where t': "t' = Rcd fs'" and fs: "fs [\<longmapsto>] fs'"
    by cases simp_all
  from fs have "\<Gamma> \<turnstile> fs' [:] fTs" by (rule T_Rcd)
  hence "\<Gamma> \<turnstile> Rcd fs' : RcdT fTs" by (rule typing_typings.T_Rcd)
  with t' show ?case by simp
next
  case (T_Proj \<Gamma> t fTs l T t')
  from \<open>t..l \<longmapsto> t'\<close>
  show ?case
  proof cases
    case (E_ProjRcd fs)
    with T_Proj have "\<Gamma> \<turnstile> Rcd fs : RcdT fTs" by simp
    hence "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<and> \<Gamma> \<turnstile> u : U"
      by (rule Rcd_type1')
    with E_ProjRcd T_Proj show ?thesis by (fastforce dest: assoc_set)
  next
    case (E_Proj t'')
    from \<open>t \<longmapsto> t''\<close>
    have "\<Gamma> \<turnstile> t'' : RcdT fTs" by (rule T_Proj)
    hence "\<Gamma> \<turnstile> t''..l : T" using T_Proj(3)
      by (rule typing_typings.T_Proj)
    with E_Proj show ?thesis by simp
  qed
next
  case (T_Nil \<Gamma> fs')
  from \<open>[] [\<longmapsto>] fs'\<close>
  show ?case by cases
next
  case (T_Cons \<Gamma> t T fs fTs l fs')
  from \<open>(l, t) \<Colon> fs [\<longmapsto>] fs'\<close>
  show ?case
  proof cases
    case (E_hd t')
    from \<open>t \<longmapsto> t'\<close>
    have "\<Gamma> \<turnstile> t' : T" by (rule T_Cons)
    hence "\<Gamma> \<turnstile> (l, t') \<Colon> fs [:] (l, T) \<Colon> fTs" using T_Cons(3,5)
      by (rule typing_typings.T_Cons)
    with E_hd show ?thesis by simp
  next
    case (E_tl fs'')
    note fs = \<open>fs [\<longmapsto>] fs''\<close>
    note T_Cons(1)
    moreover from fs have "\<Gamma> \<turnstile> fs'' [:] fTs" by (rule T_Cons)
    moreover from fs T_Cons have "fs''\<langle>l\<rangle>\<^sub>? = \<bottom>" by simp
    ultimately have "\<Gamma> \<turnstile> (l, t) \<Colon> fs'' [:] (l, T) \<Colon> fTs"
      by (rule typing_typings.T_Cons)
    with E_tl show ?thesis by simp
  qed
qed

lemma Fun_canonical: \<comment> \<open>A.14(1)\<close>
  assumes ty: "[] \<turnstile> v : T\<^sub>1 \<rightarrow> T\<^sub>2"
  shows "v \<in> value \<Longrightarrow> \<exists>t S. v = (\<lambda>:S. t)" using ty
proof (induct "[]::env" v "T\<^sub>1 \<rightarrow> T\<^sub>2" arbitrary: T\<^sub>1 T\<^sub>2 rule: typing_induct)
  case T_Abs
  show ?case by iprover
next
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 t\<^sub>2 T\<^sub>1 T\<^sub>2)
  from \<open>t\<^sub>1 \<bullet> t\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2 T\<^sub>1 T\<^sub>2')
  from \<open>t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_Sub t S T\<^sub>1 T\<^sub>2)
  from \<open>[] \<turnstile> S <: T\<^sub>1 \<rightarrow> T\<^sub>2\<close>
  obtain S\<^sub>1 S\<^sub>2 where S: "S = S\<^sub>1 \<rightarrow> S\<^sub>2"
    by cases (auto simp add: T_Sub)
  show ?case by (rule T_Sub S)+
next
  case (T_Let t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2 T\<^sub>1' T\<^sub>2')
  from \<open>(LET p = t\<^sub>1 IN t\<^sub>2) \<in> value\<close>
  show ?case by cases
next
  case (T_Proj t fTs l T\<^sub>1 T\<^sub>2)
  from \<open>t..l \<in> value\<close>
  show ?case by cases
qed simp_all

lemma TyAll_canonical: \<comment> \<open>A.14(3)\<close>
  assumes ty: "[] \<turnstile> v : (\<forall><:T\<^sub>1. T\<^sub>2)"
  shows "v \<in> value \<Longrightarrow> \<exists>t S. v = (\<lambda><:S. t)" using ty
proof (induct "[]::env" v "\<forall><:T\<^sub>1. T\<^sub>2" arbitrary: T\<^sub>1 T\<^sub>2 rule: typing_induct)
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 t\<^sub>2 T\<^sub>1 T\<^sub>2)
  from \<open>t\<^sub>1 \<bullet> t\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case T_TAbs
  show ?case by iprover
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2 T\<^sub>1 T\<^sub>2')
  from \<open>t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_Sub t S T\<^sub>1 T\<^sub>2)
  from \<open>[] \<turnstile> S <: (\<forall><:T\<^sub>1. T\<^sub>2)\<close>
  obtain S\<^sub>1 S\<^sub>2 where S: "S = (\<forall><:S\<^sub>1. S\<^sub>2)"
    by cases (auto simp add: T_Sub)
  show ?case by (rule T_Sub S)+
next
  case (T_Let t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2 T\<^sub>1' T\<^sub>2')
  from \<open>(LET p = t\<^sub>1 IN t\<^sub>2) \<in> value\<close>
  show ?case by cases
next
  case (T_Proj t fTs l T\<^sub>1 T\<^sub>2)
  from \<open>t..l \<in> value\<close>
  show ?case by cases
qed simp_all

text \<open>
Like in the case of the simple calculus,
we also need a canonical values theorem for record types:
\<close>

lemma RcdT_canonical: \<comment> \<open>A.14(2)\<close>
  assumes ty: "[] \<turnstile> v : RcdT fTs"
  shows "v \<in> value \<Longrightarrow>
    \<exists>fs. v = Rcd fs \<and> (\<forall>(l, t) \<in> set fs. t \<in> value)" using ty
proof (induct "[]::env" v "RcdT fTs" arbitrary: fTs rule: typing_induct)
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 t\<^sub>2 fTs)
  from \<open>t\<^sub>1 \<bullet> t\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2 fTs)
  from \<open>t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<in> value\<close>
  show ?case by cases
next
  case (T_Sub t S fTs)
  from \<open>[] \<turnstile> S <: RcdT fTs\<close>
  obtain fTs' where S: "S = RcdT fTs'"
    by cases (auto simp add: T_Sub)
  show ?case by (rule T_Sub S)+
next
  case (T_Let t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2 fTs)
  from \<open>(LET p = t\<^sub>1 IN t\<^sub>2) \<in> value\<close>
  show ?case by cases
next
  case (T_Rcd fs fTs)
  from \<open>Rcd fs \<in> value\<close>
  show ?case using T_Rcd by cases simp_all
next
  case (T_Proj t fTs l fTs')
  from \<open>t..l \<in> value\<close>
  show ?case by cases
qed simp_all

theorem reorder_prop:
  "\<forall>(l, t) \<in> set fs. P t \<Longrightarrow> \<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<Longrightarrow>
     \<forall>(l, t) \<in> set (map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs). P t"
  apply (induct fs)
  apply simp
  apply (simp add: split_paired_all)
  apply simp
  apply (rule ballI)
  apply (simp add: split_paired_all)
  apply (drule bpspec)
  apply assumption
  apply (erule exE)
  apply (simp split: if_split_asm)
  apply (auto dest: assoc_set)
  done

text \<open>
Another central property needed in the proof of the progress theorem is
that well-typed matching is defined.
This means that if the pattern @{term p} is compatible with the type @{term T} of
the closed term @{term t} that it has to match, then it is always possible to extract a
list of terms @{term ts} corresponding to the variables in @{term p}.
Interestingly, this important property is missing in the description of the
{\sc PoplMark} Challenge \cite{PoplMark}.
\<close>

theorem ptyping_match:
  "\<turnstile> p : T \<Rightarrow> \<Delta> \<Longrightarrow> [] \<turnstile> t : T \<Longrightarrow> t \<in> value \<Longrightarrow>
    \<exists>ts. \<turnstile> p \<rhd> t \<Rightarrow> ts"
  "\<turnstile> fps [:] fTs \<Rightarrow> \<Delta> \<Longrightarrow> [] \<turnstile> fs [:] fTs \<Longrightarrow>
    \<forall>(l, t) \<in> set fs. t \<in> value \<Longrightarrow> \<exists>us. \<turnstile> fps [\<rhd>] fs \<Rightarrow> us"
proof (induct arbitrary: t and fs set: ptyping ptypings)
  case (P_Var T t)
  show ?case by (iprover intro: M_PVar)
next
  case (P_Rcd fps fTs \<Delta> t)
  then obtain fs where
    t: "t = Rcd fs" and fs: "\<forall>(l, t) \<in> set fs. t \<in> value"
    by (blast dest: RcdT_canonical)
  with P_Rcd have fs': "[] \<turnstile> Rcd fs : RcdT fTs" by simp
  hence "[] \<turnstile> map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs [:] fTs"
    by (rule Rcd_type2')
  moreover from Rcd_type1' [OF fs']
  have assoc: "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor>" by blast
  with fs have "\<forall>(l, t) \<in> set (map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs). t \<in> value"
    by (rule reorder_prop)
  ultimately have "\<exists>us. \<turnstile> fps [\<rhd>] map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs \<Rightarrow> us"
    by (rule P_Rcd)
  then obtain us where "\<turnstile> fps [\<rhd>] map (\<lambda>(l, T). (l, the (fs\<langle>l\<rangle>\<^sub>?))) fTs \<Rightarrow> us" ..
  with P_Rcd(1) assoc have "\<turnstile> fps [\<rhd>] fs \<Rightarrow> us" by (rule matchs_reorder')
  hence "\<turnstile> PRcd fps \<rhd> Rcd fs \<Rightarrow> us" by (rule M_Rcd)
  with t show ?case by fastforce
next
  case (P_Nil fs)
  show ?case by (iprover intro: M_Nil)
next
  case (P_Cons p T \<Delta>\<^sub>1 fps fTs \<Delta>\<^sub>2 l fs)
  from \<open>[] \<turnstile> fs [:] (l, T) \<Colon> fTs\<close>
  obtain t fs' where fs: "fs = (l, t) \<Colon> fs'" and t: "[] \<turnstile> t : T"
    and fs': "[] \<turnstile> fs' [:] fTs" by cases auto
  have "((l, t) \<Colon> fs')\<langle>l\<rangle>\<^sub>? = \<lfloor>t\<rfloor>" by simp
  moreover from fs P_Cons have "t \<in> value" by simp
  with t have "\<exists>ts. \<turnstile> p \<rhd> t \<Rightarrow> ts" by (rule P_Cons)
  then obtain ts where "\<turnstile> p \<rhd> t \<Rightarrow> ts" ..
  moreover from P_Cons fs have "\<forall>(l, t)\<in>set fs'. t \<in> value" by auto
  with fs' have "\<exists>us. \<turnstile> fps [\<rhd>] fs' \<Rightarrow> us" by (rule P_Cons)
  then obtain us where "\<turnstile> fps [\<rhd>] fs' \<Rightarrow> us" ..
  hence "\<turnstile> fps [\<rhd>] (l, t) \<Colon> fs' \<Rightarrow> us" using P_Cons(5) by (rule matchs_mono)
  ultimately have "\<turnstile> (l, p) \<Colon> fps [\<rhd>] (l, t) \<Colon> fs' \<Rightarrow> ts @ us"
    by (rule M_Cons)
  with fs show ?case by iprover
qed

theorem progress: \<comment> \<open>A.16\<close>
  "[] \<turnstile> t : T \<Longrightarrow> t \<in> value \<or> (\<exists>t'. t \<longmapsto> t')"
  "[] \<turnstile> fs [:] fTs \<Longrightarrow> (\<forall>(l, t) \<in> set fs. t \<in> value) \<or> (\<exists>fs'. fs [\<longmapsto>] fs')"
proof (induct "[]::env" t T and "[]::env" fs fTs set: typing typings)
  case T_Var
  thus ?case by simp
next
  case T_Abs
  from value.Abs show ?case ..
next
  case (T_App t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 t\<^sub>2)
  hence "t\<^sub>1 \<in> value \<or> (\<exists>t'. t\<^sub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume t\<^sub>1_val: "t\<^sub>1 \<in> value"
    with T_App obtain t S where t\<^sub>1: "t\<^sub>1 = (\<lambda>:S. t)"
      by (auto dest!: Fun_canonical)
    from T_App have "t\<^sub>2 \<in> value \<or> (\<exists>t'. t\<^sub>2 \<longmapsto> t')" by simp
    thus ?thesis
    proof
      assume "t\<^sub>2 \<in> value"
      with t\<^sub>1 have "t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t[0 \<mapsto> t\<^sub>2]"
        by simp (rule eval_evals.intros)
      thus ?thesis by iprover
    next
      assume "\<exists>t'. t\<^sub>2 \<longmapsto> t'"
      then obtain t' where "t\<^sub>2 \<longmapsto> t'" by iprover
      with t\<^sub>1_val have "t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t\<^sub>1 \<bullet> t'" by (rule eval_evals.intros)
      thus ?thesis by iprover
    qed
  next
    assume "\<exists>t'. t\<^sub>1 \<longmapsto> t'"
    then obtain t' where "t\<^sub>1 \<longmapsto> t'" ..
    hence "t\<^sub>1 \<bullet> t\<^sub>2 \<longmapsto> t' \<bullet> t\<^sub>2" by (rule eval_evals.intros)
    thus ?thesis by iprover
  qed
next
  case T_TAbs
  from value.TAbs show ?case ..
next
  case (T_TApp t\<^sub>1 T\<^sub>1\<^sub>1 T\<^sub>1\<^sub>2 T\<^sub>2)
  hence "t\<^sub>1 \<in> value \<or> (\<exists>t'. t\<^sub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume "t\<^sub>1 \<in> value"
    with T_TApp obtain t S where "t\<^sub>1 = (\<lambda><:S. t)"
      by (auto dest!: TyAll_canonical)
    hence "t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t[0 \<mapsto>\<^sub>\<tau> T\<^sub>2]" by simp (rule eval_evals.intros)
    thus ?thesis by iprover
  next
    assume "\<exists>t'. t\<^sub>1 \<longmapsto> t'"
    then obtain t' where "t\<^sub>1 \<longmapsto> t'" ..
    hence "t\<^sub>1 \<bullet>\<^sub>\<tau> T\<^sub>2 \<longmapsto> t' \<bullet>\<^sub>\<tau> T\<^sub>2" by (rule eval_evals.intros)
    thus ?thesis by iprover
  qed
next
  case (T_Sub t S T)
  show ?case by (rule T_Sub)
next
  case (T_Let t\<^sub>1 T\<^sub>1 p \<Delta> t\<^sub>2 T\<^sub>2)
  hence "t\<^sub>1 \<in> value \<or> (\<exists>t'. t\<^sub>1 \<longmapsto> t')" by simp
  thus ?case
  proof
    assume t\<^sub>1: "t\<^sub>1 \<in> value"
    with T_Let have "\<exists>ts. \<turnstile> p \<rhd> t\<^sub>1 \<Rightarrow> ts"
      by (auto intro: ptyping_match)
    with t\<^sub>1 show ?thesis by (blast intro: eval_evals.intros)
  next
    assume "\<exists>t'. t\<^sub>1 \<longmapsto> t'"
    thus ?thesis by (blast intro: eval_evals.intros)
  qed
next
  case (T_Rcd fs fTs)
  thus ?case by (blast intro: value.intros eval_evals.intros)
next
  case (T_Proj t fTs l T)
  hence "t \<in> value \<or> (\<exists>t'. t \<longmapsto> t')" by simp
  thus ?case
  proof
    assume tv: "t \<in> value"
    with T_Proj obtain fs where
      t: "t = Rcd fs" and fs: "\<forall>(l, t) \<in> set fs. t \<in> value"
      by (auto dest: RcdT_canonical)
    with T_Proj have "[] \<turnstile> Rcd fs : RcdT fTs" by simp
    hence "\<forall>(l, U)\<in>set fTs. \<exists>u. fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor> \<and> [] \<turnstile> u : U"
      by (rule Rcd_type1')
    with T_Proj obtain u where u: "fs\<langle>l\<rangle>\<^sub>? = \<lfloor>u\<rfloor>" by (blast dest: assoc_set)
    with fs have "u \<in> value" by (blast dest: assoc_set)
    with u t show ?case by (blast intro: eval_evals.intros)
  next
    assume "\<exists>t'. t \<longmapsto> t'"
    thus ?case by (blast intro: eval_evals.intros)
  qed
next
  case T_Nil
  show ?case by simp
next
  case (T_Cons t T fs fTs l)
  thus ?case by (auto intro: eval_evals.intros)
qed

end
