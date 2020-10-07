theory Refine_Phantom
imports
  Autoref_Misc
  Refine_Unions
begin
consts i_phantom :: "interface \<Rightarrow> interface"

context includes autoref_syntax begin


definition pphantom_rel_internal:
  "phantom_rel A = {(Some x, y)|x y. (x, y) \<in> A} \<union> {(None, y)|x y. (x, y) \<in> A}"
lemma phantom_rel_def: "\<langle>A\<rangle>phantom_rel = {(Some x, y)|x y. (x, y) \<in> A} \<union> {(None, y)|x y. (x, y) \<in> A}"
  by (auto simp: relAPP_def pphantom_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of phantom_rel i_phantom]

definition [simp]: "mk_phantom x = x"

lemma phantom_rel_const[autoref_rules(overloaded)]:
  shows "(Some, mk_phantom) \<in> A \<rightarrow> \<langle>A\<rangle>phantom_rel"
  by (auto simp: phantom_rel_def)

definition [simp]: "op_union_phantom = (\<union>)"
lemma [autoref_op_pat]: "(\<union>) \<equiv> OP op_union_phantom"
  by simp
lemma phantom_rel_union[autoref_rules]:
  assumes [THEN GEN_OP_D, autoref_rules(overloaded)]: "GEN_OP un (\<union>) (A \<rightarrow> A \<rightarrow> A)"
  shows "(\<lambda>a b. do {a \<leftarrow> a; b \<leftarrow> b; Some (un a b)}, op_union_phantom) \<in> \<langle>A\<rangle>phantom_rel \<rightarrow> \<langle>A\<rangle>phantom_rel \<rightarrow> \<langle>A\<rangle>phantom_rel"
  using assms
  by (fastforce simp: phantom_rel_def dest: fun_relD)

definition [simp]: "op_empty_phantom b = {}"

lemma phantom_rel_empty_coll[autoref_rules]:
  shows "(\<lambda>b. (if b then None else Some []), op_empty_phantom) \<in> bool_rel \<rightarrow> \<langle>clw_rel A\<rangle>phantom_rel"
  apply (auto simp: phantom_rel_def br_def lw_rel_def Union_rel_def)
    apply (rule relcompI)
     apply force
    apply (rule relcompI)
     defer
  by (force dest!: spec[where x="[]"])+


lemma mem_phantom_rel_Some[simp]:
  "(Some x, y) \<in> \<langle>A\<rangle>phantom_rel \<longleftrightarrow> (x, y) \<in> A"
  by (auto simp: phantom_rel_def)

lemma RETURN_None_ph_relI: "(RETURN y, x) \<in> \<langle>B\<rangle>nres_rel \<Longrightarrow> (RETURN None, x) \<in> \<langle>\<langle>B\<rangle>phantom_rel\<rangle>nres_rel"
  by (auto simp: phantom_rel_def nres_rel_def pw_le_iff refine_pw_simps)
lemma RETURN_Some_ph_relI: "(RETURN y, x) \<in> \<langle>B\<rangle>nres_rel \<Longrightarrow> (RETURN (Some y), x) \<in> \<langle>\<langle>B\<rangle>phantom_rel\<rangle>nres_rel"
  by (auto simp: phantom_rel_def nres_rel_def pw_le_iff refine_pw_simps)

lemma None_ph_relI: "(x, X) \<in> B \<Longrightarrow> (None, X) \<in> \<langle>B\<rangle>phantom_rel"
  by (auto simp: phantom_rel_def)

definition "phantom_rel_unop fid x = (case x of None \<Rightarrow> None | Some x \<Rightarrow> (Some (fid x)))"
lemma phantom_rel_unop:
  assumes f[THEN GEN_OP_D]: "GEN_OP fi f (A \<rightarrow> \<langle>B\<rangle>nres_rel)"
  assumes fi[unfolded autoref_tag_defs]: "\<And>x. TRANSFER (RETURN (fid x) \<le> fi x)"
  shows "(\<lambda>x. RETURN (phantom_rel_unop fid x), f) \<in> \<langle>A\<rangle>phantom_rel \<rightarrow> \<langle>\<langle>B\<rangle>phantom_rel\<rangle>nres_rel"
proof (rule fun_relI)
  fix x a assume x: "(x, a) \<in> \<langle>A\<rangle>phantom_rel"
  with assms obtain b where "(b, a) \<in> A" by (auto simp: phantom_rel_def)
  show "(RETURN (phantom_rel_unop fid x), f a) \<in> \<langle>\<langle>B\<rangle>phantom_rel\<rangle>nres_rel"
    using x
    by (auto split: option.splits intro!: x \<open>(b, a) \<in> A\<close> f[param_fo]
        RETURN_Some_ph_relI RETURN_None_ph_relI nres_rel_trans1[OF fi]
        simp: phantom_rel_unop_def)
qed

lemma phantom_rel_union_coll[autoref_rules]:
  assumes [THEN GEN_OP_D, autoref_rules(overloaded)]: "GEN_OP un op_union_coll (clw_rel A \<rightarrow> clw_rel A \<rightarrow> clw_rel A)"
  shows "(\<lambda>a b. do {a \<leftarrow> a; b \<leftarrow> b; Some (un a b)}, op_union_phantom) \<in> \<langle>clw_rel A\<rangle>phantom_rel \<rightarrow> \<langle>clw_rel A\<rangle>phantom_rel \<rightarrow> \<langle>clw_rel A\<rangle>phantom_rel"
  using assms
  by (fastforce simp: phantom_rel_def dest: fun_relD)

definition [refine_vcg_def]: "get_phantom X = SPEC (\<lambda>R. R = X)"

lemma get_phantom_impl[autoref_rules]:
  "(\<lambda>x. nres_of (case x of None \<Rightarrow> dSUCCEED | Some y \<Rightarrow> dRETURN y), get_phantom) \<in> \<langle>A\<rangle>phantom_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
  by (auto simp: get_phantom_def phantom_rel_def nres_rel_def RETURN_RES_refine_iff)

end

end