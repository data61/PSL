section \<open>WebAssembly Core AST\<close>

theory Wasm_Ast imports Main "Native_Word.Uint8" begin

type_synonym \<comment> \<open>immediate\<close>
  i = nat
type_synonym \<comment> \<open>static offset\<close>
  off = nat
type_synonym \<comment> \<open>alignment exponent\<close>
  a = nat

\<comment> \<open>primitive types\<close>
typedecl i32
typedecl i64
typedecl f32
typedecl f64

\<comment> \<open>memory\<close>
type_synonym byte = uint8

typedef bytes = "UNIV :: (byte list) set" ..
setup_lifting type_definition_bytes
declare Quotient_bytes[transfer_rule]

lift_definition bytes_takefill :: "byte \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> bytes" is "(\<lambda>a n as. takefill (Abs_uint8 a) n as)" .
lift_definition bytes_replicate :: "nat \<Rightarrow> byte \<Rightarrow> bytes" is "(\<lambda>n b. replicate n (Abs_uint8 b))" .
definition msbyte :: "bytes \<Rightarrow> byte" where
  "msbyte bs = last (Rep_bytes bs)"

typedef mem = "UNIV :: (byte list) set" ..
setup_lifting type_definition_mem
declare Quotient_mem[transfer_rule]

lift_definition read_bytes :: "mem \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bytes" is "(\<lambda>m n l. take l (drop n m))" .
lift_definition write_bytes :: "mem \<Rightarrow> nat \<Rightarrow> bytes \<Rightarrow> mem" is "(\<lambda>m n bs. (take n m) @ bs @ (drop (n + length bs) m))" .
lift_definition mem_append :: "mem \<Rightarrow> bytes \<Rightarrow> mem" is append .

\<comment> \<open>host\<close>
typedecl host
typedecl host_state

datatype \<comment> \<open>value types\<close>
  t = T_i32 | T_i64 | T_f32 | T_f64

datatype \<comment> \<open>packed types\<close>
  tp = Tp_i8 | Tp_i16 | Tp_i32

datatype \<comment> \<open>mutability\<close>
  mut = T_immut | T_mut

record tg = \<comment> \<open>global types\<close>
  tg_mut :: mut
  tg_t :: t

datatype \<comment> \<open>function types\<close>
  tf = Tf "t list" "t list" ("_ '_> _" 60)

(* TYPING *)
record t_context =
  types_t :: "tf list"
  func_t :: "tf list"
  global :: "tg list"
  table :: "nat option"
  memory :: "nat option"
  local :: "t list"
  label :: "(t list) list"
  return :: "(t list) option"

record s_context =
  s_inst :: "t_context list"
  s_funcs :: "tf list"
  s_tab  :: "nat list"
  s_mem  :: "nat list"
  s_globs :: "tg list"

datatype
  sx = S | U

datatype
  unop_i = Clz | Ctz | Popcnt

datatype
  unop_f = Neg | Abs | Ceil | Floor | Trunc | Nearest | Sqrt

datatype
  binop_i = Add | Sub | Mul | Div sx | Rem sx | And | Or | Xor | Shl | Shr sx | Rotl | Rotr

datatype
  binop_f = Addf | Subf | Mulf | Divf | Min | Max | Copysign
  
datatype
  testop = Eqz
  
datatype
  relop_i = Eq | Ne | Lt sx | Gt sx | Le sx | Ge sx
  
datatype
  relop_f = Eqf | Nef | Ltf | Gtf | Lef | Gef
  
datatype
  cvtop = Convert | Reinterpret

datatype \<comment> \<open>values\<close>
  v =
    ConstInt32 i32
    | ConstInt64 i64
    | ConstFloat32 f32
    | ConstFloat64 f64

datatype \<comment> \<open>basic instructions\<close>
  b_e =
    Unreachable
    | Nop
    | Drop
    | Select
    | Block tf "b_e list"
    | Loop tf "b_e list"
    | If tf "b_e list" "b_e list"
    | Br i
    | Br_if i
    | Br_table "i list" i
    | Return
    | Call i
    | Call_indirect i
    | Get_local i
    | Set_local i
    | Tee_local i
    | Get_global i
    | Set_global i
    | Load t "(tp \<times> sx) option" a off
    | Store t "tp option" a off
    | Current_memory
    | Grow_memory
    | EConst v ("C _" 60)
    | Unop_i t unop_i
    | Unop_f t unop_f
    | Binop_i t binop_i
    | Binop_f t binop_f
    | Testop t testop
    | Relop_i t relop_i
    | Relop_f t relop_f
    | Cvtop t cvtop t "sx option"

datatype cl = \<comment> \<open>function closures\<close>
  Func_native i tf "t list" "b_e list"
| Func_host tf host

record inst = \<comment> \<open>instances\<close>
  types :: "tf list"
  funcs :: "i list"
  tab :: "i option"
  mem :: "i option"
  globs :: "i list"

type_synonym tabinst = "(cl option) list"

record global =
  g_mut :: mut
  g_val :: v

record s = \<comment> \<open>store\<close>
  inst :: "inst list"
  funcs :: "cl list"
  tab :: "tabinst list"
  mem :: "mem list"
  globs :: "global list"

datatype e = \<comment> \<open>administrative instruction\<close>
  Basic b_e ("$_" 60)
  | Trap
  | Callcl cl
  | Label nat "e list" "e list"
  | Local nat i "v list" "e list"

datatype Lholed =
    \<comment> \<open>L0 = v* [<hole>] e*\<close>
    LBase "e list" "e list"
    \<comment> \<open>L(i+1) = v* (label n {e* } Li) e*\<close>
  | LRec "e list" nat "e list" Lholed "e list"
end
