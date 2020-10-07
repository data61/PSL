section \<open>The state\<close>

theory ProcState imports Com begin

fun "interpret" :: "expr \<Rightarrow> (vname \<rightharpoonup> val) \<Rightarrow> val option"
where Val: "interpret (Val v) cf = Some v"
  | Var: "interpret (Var V) cf = cf V"
  | BinOp: "interpret (e\<^sub>1\<guillemotleft>bop\<guillemotright>e\<^sub>2) cf = 
    (case interpret e\<^sub>1 cf of None \<Rightarrow> None
                         | Some v\<^sub>1 \<Rightarrow> (case interpret e\<^sub>2 cf of None \<Rightarrow> None
                                                           | Some v\<^sub>2 \<Rightarrow> (
      case binop bop v\<^sub>1 v\<^sub>2 of None \<Rightarrow> None | Some v \<Rightarrow> Some v)))"


abbreviation update :: "(vname \<rightharpoonup> val) \<Rightarrow> vname \<Rightarrow> expr \<Rightarrow> (vname \<rightharpoonup> val)"
  where "update cf V e \<equiv> cf(V:=(interpret e cf))"

abbreviation state_check :: "(vname \<rightharpoonup> val) \<Rightarrow> expr \<Rightarrow> val option \<Rightarrow> bool"
where "state_check cf b v \<equiv> (interpret b cf = v)"

end
