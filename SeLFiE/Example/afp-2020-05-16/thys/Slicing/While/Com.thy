chapter \<open>Instantiating the Framework with a simple While-Language\<close>

section \<open>Commands\<close>

theory Com imports Main begin

subsection \<open>Variables and Values\<close>

type_synonym vname = string \<comment> \<open>names for variables\<close>

datatype val
  = Bool bool      \<comment> \<open>Boolean value\<close>
  | Intg int       \<comment> \<open>integer value\<close> 

abbreviation "true == Bool True"
abbreviation "false == Bool False"

subsection \<open>Expressions and Commands\<close>

datatype bop = Eq | And | Less | Add | Sub     \<comment> \<open>names of binary operations\<close>

datatype expr
  = Val val                                          \<comment> \<open>value\<close>
  | Var vname                                        \<comment> \<open>local variable\<close>
  | BinOp expr bop expr    ("_ \<guillemotleft>_\<guillemotright> _" [80,0,81] 80)  \<comment> \<open>binary operation\<close>


fun binop :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val option"
where "binop Eq v\<^sub>1 v\<^sub>2               = Some(Bool(v\<^sub>1 = v\<^sub>2))"
  | "binop And (Bool b\<^sub>1) (Bool b\<^sub>2)  = Some(Bool(b\<^sub>1 \<and> b\<^sub>2))"
  | "binop Less (Intg i\<^sub>1) (Intg i\<^sub>2) = Some(Bool(i\<^sub>1 < i\<^sub>2))"
  | "binop Add (Intg i\<^sub>1) (Intg i\<^sub>2)  = Some(Intg(i\<^sub>1 + i\<^sub>2))"
  | "binop Sub (Intg i\<^sub>1) (Intg i\<^sub>2)  = Some(Intg(i\<^sub>1 - i\<^sub>2))"
  | "binop bop v\<^sub>1 v\<^sub>2                = None"


datatype cmd
  = Skip
  | LAss vname expr        ("_:=_" [70,70] 70)  \<comment> \<open>local assignment\<close>
  | Seq cmd cmd            ("_;;/ _" [61,60] 60)
  | Cond expr cmd cmd      ("if '(_') _/ else _" [80,79,79] 70)
  | While expr cmd         ("while '(_') _" [80,79] 70)


fun num_inner_nodes :: "cmd \<Rightarrow> nat" ("#:_")
where "#:Skip              = 1"
  | "#:(V:=e)              = 2"       (* zusätzlicher Skip-Knoten *)
  | "#:(c\<^sub>1;;c\<^sub>2)            = #:c\<^sub>1 + #:c\<^sub>2"
  | "#:(if (b) c\<^sub>1 else c\<^sub>2) = #:c\<^sub>1 + #:c\<^sub>2 + 1"
  | "#:(while (b) c)       = #:c + 2" (* zusätzlicher Skip-Knoten *)
  


lemma num_inner_nodes_gr_0:"#:c > 0"
by(induct c) auto

lemma [dest]:"#:c = 0 \<Longrightarrow> False"
by(induct c) auto

subsection \<open>The state\<close>

type_synonym state = "vname \<rightharpoonup> val"

fun "interpret" :: "expr \<Rightarrow> state \<Rightarrow> val option"
where Val: "interpret (Val v) s = Some v"
  | Var: "interpret (Var V) s = s V"
  | BinOp: "interpret (e\<^sub>1\<guillemotleft>bop\<guillemotright>e\<^sub>2) s = 
    (case interpret e\<^sub>1 s of None \<Rightarrow> None
                         | Some v\<^sub>1 \<Rightarrow> (case interpret e\<^sub>2 s of None \<Rightarrow> None
                                                           | Some v\<^sub>2 \<Rightarrow> (
      case binop bop v\<^sub>1 v\<^sub>2 of None \<Rightarrow> None | Some v \<Rightarrow> Some v)))"

end
