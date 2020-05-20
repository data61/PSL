section \<open>Syntax of KPL\<close>

theory KPL_syntax imports 
  Misc
begin

text\<open>Locations of local variables\<close>
typedecl V 

text \<open>C strings\<close>
typedecl name

text \<open>Procedure names\<close>
typedecl proc_name

text \<open>Local-id, group-id\<close>
type_synonym lid = nat
type_synonym gid = nat

text \<open>Fully-qualified thread-id\<close>
type_synonym tid = "gid \<times> lid"

text \<open>Let @{term "(G,T)"} range over threadsets\<close>
type_synonym threadset = "gid set \<times> (gid \<rightharpoonup> lid set)"

text \<open>Returns the set of tids in a threadset\<close>
fun tids :: "threadset \<Rightarrow> tid set"
where
  "tids (G,T) = {(i,j) | i j. i \<in> G \<and> j \<in> the (T i)}"

type_synonym word = nat  (* should really be machine words *)

datatype loc =
  Name name
| Var V

text \<open>Local expressions\<close>
datatype local_expr =
  Loc loc
| Gid
| Lid
| eTrue
| eConj local_expr local_expr  (infixl "\<and>*" 50)
| eNot local_expr              ("\<not>*")

text \<open>Basic statements\<close>
datatype basic_stmt =
  Assign loc local_expr
| Read loc local_expr
| Write local_expr local_expr

text \<open>Statements\<close>
datatype stmt =
  Basic basic_stmt
| Seq stmt stmt (infixl ";;" 50)
| Local name stmt
| If local_expr stmt stmt
| While local_expr stmt
| WhileDyn local_expr stmt
| Call proc_name local_expr
| Barrier
| Break
| Continue
| Return

text \<open>Procedures comprise a procedure name, parameter name, and a body statement\<close>
record proc = 
  proc_name :: proc_name
  param :: name
  body :: stmt

text \<open>Kernels\<close>
record kernel = 
  groups :: nat
  threads :: nat
  procs :: "proc list"
  main :: stmt

end
