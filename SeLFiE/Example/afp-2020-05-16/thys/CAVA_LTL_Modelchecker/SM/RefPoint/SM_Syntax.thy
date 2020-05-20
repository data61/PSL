section \<open>Syntax of SM\<close>
theory SM_Syntax
imports Main
begin
  text \<open>
    In this theory, we define the syntax of SM, the Simple Modeling language.
\<close>

  text \<open>Literals\<close>
  type_synonym ident = String.literal     \<comment> \<open> Identifier \<close>
  type_synonym numeric = int              \<comment> \<open> Numeric value \<close>

  datatype bin_op =                               \<comment> \<open> Binary operators \<close>
    bo_plus | bo_minus | bo_mul | bo_div | bo_mod \<comment> \<open>Standard arith\<close>
  | bo_less | bo_less_eq | bo_eq                  \<comment> \<open>Comparison\<close>
  | bo_and | bo_or | bo_xor                       \<comment> \<open>Bit-Wise\<close>

  datatype un_op =                    \<comment> \<open> Unary operators \<close>
    uo_minus | uo_not 

  (* Expressions *)
  datatype exp =
      e_var ident                       \<comment> \<open> Variable (local/global based on scope) \<close>
    | e_localvar ident                  \<comment> \<open> Local variable \<close>
    | e_globalvar ident                 \<comment> \<open> Global variable \<close>
    | e_const numeric                   \<comment> \<open> Numeric constant \<close>
    | e_bin bin_op exp exp              \<comment> \<open> Binary operators \<close> 
    | e_un un_op exp                    \<comment> \<open> Unary operators \<close>   
  
  (* Commands *)
  datatype cmd =
    Assign exp ident exp | Assign_local exp ident exp | Assign_global exp ident exp
  | Test exp 
  | Skip      
  | Seq cmd cmd | Or cmd cmd                  \<comment> \<open>Control flow\<close>
  | Break | Continue                          \<comment> \<open>More control flow\<close> 
  | Iterate cmd cmd                           \<comment> \<open>Iterate command\<close> 
  | Invalid                                   \<comment> \<open>Internal: Invalid command\<close>  

  definition "Loop cmd \<equiv> Iterate cmd cmd"    \<comment> \<open>Syntactic sugar\<close>

  text \<open>A variable declaration just contains a name\<close>
  type_synonym var_decl = ident

  text \<open>A process contains a body and local variable declarations\<close>
  record proc_decl =
    name :: "ident"
    body :: "cmd"
    local_vars :: "var_decl list"

  text \<open>A program contains process declarations and global variable 
    declarations\<close>
  record program =
    processes :: "proc_decl list"
    global_vars :: "var_decl list"

end
