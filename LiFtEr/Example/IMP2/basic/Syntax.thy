section \<open>Abstract Syntax of IMP2\<close>
theory Syntax
imports Main
begin

  text \<open>We define the abstract syntax of the IMP2 language, 
    and a minimal concrete syntax for direct use in terms.\<close>


  subsection \<open>Primitives\<close>  
  text \<open>Variable and procedure names are strings.\<close>
  type_synonym vname = string
  type_synonym pname = string

  text \<open>The variable names are partitioned into local and global variables.\<close>
  fun is_global :: "vname \<Rightarrow> bool" where
    "is_global [] \<longleftrightarrow> True"
  | "is_global (CHR ''G''#_) \<longleftrightarrow> True"
  | "is_global _ \<longleftrightarrow> False"

  abbreviation "is_local a \<equiv> \<not>is_global a"
  
  
    
  text \<open>
    Primitive values are integers,
    and values are arrays modeled as functions from integers to primitive values.
    
    Note that values and primitive values are usually part of the semantics, however, 
    as they occur as literals in the abstract syntax, we already define them here.
  \<close>
  
  type_synonym pval = "int"
  type_synonym val = "int \<Rightarrow> pval"

  (*
    TODO: Cf. SortedAlgebra, used in CeTa. Akihisa Yamada
      Should give aexp, bexp with type-checking, term ops, etc.
  
  *)

  subsection \<open>Arithmetic Expressions\<close>
  text \<open>Arithmetic expressions consist of constants, indexed array variables, 
    and unary and binary operations. The operations are modeled by reflecting 
    arbitrary functions into the abstract syntax.\<close>
  
  datatype aexp = 
      N int 
    | Vidx vname aexp
    | Unop "int \<Rightarrow> int" aexp 
    | Binop "int \<Rightarrow> int \<Rightarrow> int" aexp aexp
    
  subsection \<open>Boolean Expressions\<close>
  text \<open>Boolean expressions consist of constants, the not operation, binary connectives, 
    and comparison operations. Binary connectives and comparison operations are modeled by
    reflecting arbitrary functions into the abstract syntax. The not operation is the only 
    meaningful unary Boolean operation, so we chose to model it explicitly instead of 
    reflecting and unary Boolean function.\<close>
    
  datatype bexp = 
      Bc bool 
    | Not bexp 
    | BBinop "bool \<Rightarrow> bool \<Rightarrow> bool" bexp bexp 
    | Cmpop "int \<Rightarrow> int \<Rightarrow> bool" aexp aexp

    
  subsection \<open>Commands\<close>
  text \<open>
    The commands can roughly be put into five categories:
    \<^descr>[Skip] The no-op command
    \<^descr>[Assignment commands] Commands to assign the value of an arithmetic expression, copy or clear arrays,
      and a command to simultaneously assign all local variables, which is only used internally 
      to simplify the definition of a small-step semantics.
    \<^descr>[Block commands] The standard sequential composition, if-then-else, and while commands,
      and a scope command which executes a command with a fresh set of local variables.
    \<^descr>[Procedure commands] Procedure call, and a procedure scope command, which executes
      a command in a specified procedure environment. Similar to the scope command, 
      which introduces new local variables, and thus limits the effect of variable manipulations
      to the content of the command, the procedure scope command introduces new procedures,
      and limits the validity of their names to the content of the command. This greatly 
      simplifies modular definition of programs, as procedure names can be used locally.
      
  \<close>
  
  
  datatype
    com = 
        SKIP                              \<comment> \<open>No-op\<close>
        
        \<comment> \<open>Assignment\<close> 
        | AssignIdx vname aexp aexp       \<comment> \<open>Assign to index in array\<close>
        | ArrayCpy vname vname            \<comment> \<open>Copy whole array\<close>
        | ArrayClear vname                \<comment> \<open>Clear array\<close>
        | Assign_Locals "vname \<Rightarrow> val"    \<comment> \<open>Internal: Assign all local variables simultaneously\<close>
        
        \<comment> \<open>Block\<close>
        | Seq    com  com                 \<comment> \<open>Sequential composition\<close>
        | If     bexp com com             \<comment> \<open>Conditional\<close>
        | While  bexp com                 \<comment> \<open>While-loop\<close>
        | Scope com                       \<comment> \<open>Local variable scope\<close>
        
        \<comment> \<open>Procedure\<close>
        | PCall pname                     \<comment> \<open>Procedure call\<close>
        | PScope "pname \<rightharpoonup> com" com       \<comment> \<open>Procedure scope\<close>

  subsubsection \<open>Minimal Concrete Syntax\<close>
  text \<open>The commands come with a minimal concrete syntax, which is compatible 
    to the syntax of \<open>IMP\<close>.\<close>
  
  notation AssignIdx      ("_[_] ::= _" [1000, 0, 61] 61)
  notation ArrayCpy       ("_[] ::= _" [1000, 1000] 61)
  notation ArrayClear     ("CLEAR _[]" [1000] 61)
  
  notation Seq            ("_;;/ _"  [61, 60] 60)
  notation If             ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
  notation While          ("(WHILE _/ DO _)"  [0, 61] 61)
  notation Scope          ("SCOPE _" [61] 61)
        
        
  subsection \<open>Program\<close>                
  type_synonym program = "pname \<rightharpoonup> com"
        

  subsection \<open>Default Array Index\<close>
  text \<open>We define abbreviations to make arrays look like plain integer variables:
    Without explicitly specifying an array index, the index \<open>0\<close> will be used automatically.
  \<close>
  
  abbreviation "V x \<equiv> Vidx x (N 0)"  
  abbreviation Assign ("_ ::= _" [1000, 61] 61) 
    where "x ::= a \<equiv> (x[N 0] ::= a)"
        
   
end
