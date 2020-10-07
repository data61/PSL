theory Refine_String
imports
  Autoref_Misc
begin

subsection \<open>Setup for characters\<close>
context includes autoref_syntax begin
lemma [autoref_itype]: "Char b0 b1 b2 b3 b4 b5 b6 b7 ::\<^sub>i I"
  and [autoref_op_pat_def]: "Char b0 b1 b2 b3 b4 b5 b6 b7 \<equiv> OP (Char b0 b1 b2 b3 b4 b5 b6 b7) :::\<^sub>i I"
  and [autoref_rules]: "(Char b0 b1 b2 b3 b4 b5 b6 b7, OP (Char b0 b1 b2 b3 b4 b5 b6 b7) ::: Id) \<in> Id"
  by simp_all
end

subsection \<open>setup for strings\<close>

consts i_string :: interface
consts i_char :: interface

abbreviation "char_rel \<equiv> Id::(char\<times>_) set"
definition "string_rel \<equiv> \<langle>char_rel\<rangle>list_rel::(string\<times>_) set"
lemmas [autoref_rel_intf] = REL_INTFI[of string_rel i_string]
lemmas [autoref_rel_intf] = REL_INTFI[of char_rel i_char]

definition op_str_Nil::"string" where [simp]: "op_str_Nil = Nil"
definition op_str_Cons::"char \<Rightarrow> string \<Rightarrow> string" where [simp]: "op_str_Cons = Cons"
definition op_str_append::"string \<Rightarrow> string \<Rightarrow> string" where [simp]: "op_str_append = (@)"

context includes autoref_syntax begin
lemma
  shows [autoref_itype]:
    "op_str_Nil ::\<^sub>i i_string"
    "op_str_Cons ::\<^sub>i i_char \<rightarrow>\<^sub>i i_string \<rightarrow>\<^sub>i i_string"
    "op_str_append ::\<^sub>i i_string \<rightarrow>\<^sub>i i_string \<rightarrow>\<^sub>i i_string"
  and [autoref_rules]:
    "(Nil, op_str_Nil::string) \<in> string_rel"
    "(Cons, op_str_Cons) \<in> char_rel \<rightarrow> string_rel \<rightarrow> string_rel"
    "((@), op_str_append) \<in> string_rel \<rightarrow> string_rel \<rightarrow> string_rel"
  and [autoref_op_pat_def]:
    "Nil \<equiv> op_str_Nil"
    "Cons \<equiv> op_str_Cons"
    "(@) \<equiv> op_str_append"
  by (simp_all add: string_rel_def)
end

subsection \<open>Setup for literals\<close>
context includes autoref_syntax begin
lemma [autoref_itype]: "String.empty_literal ::\<^sub>i I"
  and [autoref_op_pat_def]: "String.empty_literal \<equiv> OP String.empty_literal :::\<^sub>i I"
  and [autoref_rules]: "(String.empty_literal, OP String.empty_literal ::: Id) \<in> Id"
  by simp_all

lemma [autoref_itype]: "String.Literal b0 b1 b2 b3 b4 b5 b6 s ::\<^sub>i I"
  and [autoref_op_pat_def]: "String.Literal b0 b1 b2 b3 b4 b5 b6 s \<equiv>
    OP (String.Literal b0 b1 b2 b3 b4 b5 b6 s) :::\<^sub>i I"
  and [autoref_rules]: "(String.Literal b0 b1 b2 b3 b4 b5 b6 s,
    OP (String.Literal b0 b1 b2 b3 b4 b5 b6 s) ::: Id) \<in> Id"
  by simp_all

definition [simp]: "ST (x::char list) = x"
lemma [autoref_op_pat_def]: "ST xs \<equiv> OP (ST xs)" by simp
lemma [autoref_rules]: "(x, ST x) \<in> string_rel"
  by (auto simp: string_rel_def)

end

text \<open>A little check\<close>

schematic_goal "(?c::?'c, RETURN (STR '''', STR ''Hello''))\<in>?R"
  by autoref

end
