(*  Title:      JinjaThreads/JVM/JVMInstructions.thy
    Author:     Gerwin Klein, Andreas Lochbihler
*)

section \<open>Instructions of the JVM\<close>

theory JVMInstructions
imports
  JVMState
  "../Common/BinOp"
begin

datatype 'addr instr 
  = Load nat                  \<comment> \<open>load from local variable\<close>
  | Store nat                 \<comment> \<open>store into local variable\<close>
  | Push "'addr val"          \<comment> \<open>push a value (constant)\<close>
  | New cname                 \<comment> \<open>create object\<close>
  | NewArray ty               \<comment> \<open>create array for elements of given type\<close>
  | ALoad                     \<comment> \<open>Load array element from heap to stack\<close>
  | AStore                    \<comment> \<open>Set element in array\<close>
  | ALength                   \<comment> \<open>Return the length of the array\<close>
  | Getfield vname cname      \<comment> \<open>Fetch field from object\<close>
  | Putfield vname cname      \<comment> \<open>Set field in object\<close>
  | CAS vname cname           \<comment> \<open>Compare-and-swap instruction\<close>
  | Checkcast ty              \<comment> \<open>Check whether object is of given type\<close>
  | Instanceof ty             \<comment> \<open>instanceof test\<close>
  | Invoke mname nat          \<comment> \<open>inv. instance meth of an object\<close>
  | Return                    \<comment> \<open>return from method\<close>
  | Pop                       \<comment> \<open>pop top element from opstack\<close>
  | Dup                       \<comment> \<open>duplicate top stack element\<close>
  | Swap                      \<comment> \<open>swap top stack elements\<close>
  | BinOpInstr bop            \<comment> \<open>binary operator instruction\<close>
  | Goto int                  \<comment> \<open>goto relative address\<close>
  | IfFalse int               \<comment> \<open>branch if top of stack false\<close>
  | ThrowExc                  \<comment> \<open>throw top of stack as exception\<close>
  | MEnter                    \<comment> \<open>enter the monitor of object on top of the stack\<close>
  | MExit                     \<comment> \<open>exit the monitor of object on top of the stack\<close>

abbreviation CmpEq :: "'addr instr"
where "CmpEq \<equiv> BinOpInstr Eq"

abbreviation CmpLeq :: "'addr instr"
where "CmpLeq \<equiv> BinOpInstr LessOrEqual"

abbreviation CmpGeq :: "'addr instr"
where "CmpGeq \<equiv> BinOpInstr GreaterOrEqual"

abbreviation CmpLt :: "'addr instr"
where "CmpLt \<equiv> BinOpInstr LessThan"

abbreviation CmpGt :: "'addr instr"
where "CmpGt \<equiv> BinOpInstr GreaterThan"

abbreviation IAdd :: "'addr instr"
where "IAdd \<equiv> BinOpInstr Add"

abbreviation ISub :: "'addr instr"
where "ISub \<equiv> BinOpInstr Subtract"

abbreviation IMult :: "'addr instr"
where "IMult \<equiv> BinOpInstr Mult"

abbreviation IDiv :: "'addr instr"
where "IDiv \<equiv> BinOpInstr Div"

abbreviation IMod :: "'addr instr"
where "IMod \<equiv> BinOpInstr Mod"

abbreviation IShl :: "'addr instr"
where "IShl \<equiv> BinOpInstr ShiftLeft"

abbreviation IShr :: "'addr instr"
where "IShr \<equiv> BinOpInstr ShiftRightSigned"

abbreviation IUShr :: "'addr instr"
where "IUShr \<equiv> BinOpInstr ShiftRightZeros"

abbreviation IAnd :: "'addr instr"
where "IAnd \<equiv> BinOpInstr BinAnd"

abbreviation IOr :: "'addr instr"
where "IOr \<equiv> BinOpInstr BinOr"

abbreviation IXor :: "'addr instr"
where "IXor \<equiv> BinOpInstr BinXor"

type_synonym
  'addr bytecode = "'addr instr list"

type_synonym
  ex_entry = "pc \<times> pc \<times> cname option \<times> pc \<times> nat" 
  \<comment> \<open>start-pc, end-pc, exception type (None = Any), handler-pc, remaining stack depth\<close>

type_synonym
  ex_table = "ex_entry list"

type_synonym
  'addr jvm_method = "nat \<times> nat \<times> 'addr bytecode \<times> ex_table"
   \<comment> \<open>max stacksize\<close>
   \<comment> \<open>number of local variables. Add 1 + no. of parameters to get no. of registers\<close>
   \<comment> \<open>instruction sequence\<close>
   \<comment> \<open>exception handler table\<close>

type_synonym
  'addr jvm_prog = "'addr jvm_method prog" 

end
