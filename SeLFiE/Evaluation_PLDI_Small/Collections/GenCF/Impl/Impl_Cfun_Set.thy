section \<open>Set by Characteristic Function\<close>
theory Impl_Cfun_Set
imports "../Intf/Intf_Set"
begin

definition fun_set_rel where
  fun_set_rel_internal_def: 
  "fun_set_rel R \<equiv> (R\<rightarrow>bool_rel) O br Collect (\<lambda>_. True)"

lemma fun_set_rel_def: "\<langle>R\<rangle>fun_set_rel = (R\<rightarrow>bool_rel) O br Collect (\<lambda>_. True)"
  by (simp add: relAPP_def fun_set_rel_internal_def)

lemma fun_set_rel_sv[relator_props]: 
  "\<lbrakk>single_valued R; Range R = UNIV\<rbrakk> \<Longrightarrow> single_valued (\<langle>R\<rangle>fun_set_rel)"
  unfolding fun_set_rel_def
  by (tagged_solver (keep))

lemma fun_set_rel_RUNIV[relator_props]:
  assumes SV: "single_valued R" 
  shows "Range (\<langle>R\<rangle>fun_set_rel) = UNIV"
proof -
  {
    fix b
    have "\<exists>a. (a,b)\<in>\<langle>R\<rangle>fun_set_rel" unfolding fun_set_rel_def
      apply (rule exI)
      apply (rule relcompI)
    proof -
      show "((\<lambda>x. x\<in>b),b)\<in>br Collect (\<lambda>_. True)" by (auto simp: br_def)
      show "(\<lambda>x'. \<exists>x. (x',x)\<in>R \<and> x\<in>b,\<lambda>x. x \<in> b)\<in>R \<rightarrow> bool_rel"
        by (auto dest: single_valuedD[OF SV])
    qed
  } thus ?thesis by blast
qed

lemmas [autoref_rel_intf] = REL_INTFI[of fun_set_rel i_set]

lemma fs_mem_refine[autoref_rules]: "(\<lambda>x f. f x,(\<in>)) \<in> R \<rightarrow> \<langle>R\<rangle>fun_set_rel \<rightarrow> bool_rel"
  apply (intro fun_relI)
  apply (auto simp add: fun_set_rel_def br_def dest: fun_relD)
  done

lemma fun_set_Collect_refine[autoref_rules]: 
  "(\<lambda>x. x, Collect)\<in>(R\<rightarrow>bool_rel) \<rightarrow> \<langle>R\<rangle>fun_set_rel"
  unfolding fun_set_rel_def
  by (auto simp: br_def)

lemma fun_set_empty_refine[autoref_rules]: 
  "(\<lambda>_. False,{})\<in>\<langle>R\<rangle>fun_set_rel"
  by (force simp add: fun_set_rel_def br_def)

lemma fun_set_UNIV_refine[autoref_rules]: 
  "(\<lambda>_. True,UNIV)\<in>\<langle>R\<rangle>fun_set_rel"
  by (force simp add: fun_set_rel_def br_def)

lemma fun_set_union_refine[autoref_rules]: 
  "(\<lambda>a b x. a x \<or> b x,(\<union>))\<in>\<langle>R\<rangle>fun_set_rel \<rightarrow> \<langle>R\<rangle>fun_set_rel \<rightarrow> \<langle>R\<rangle>fun_set_rel"
proof -
  have A: "\<And>a b. (\<lambda>x. x\<in>a \<or> x\<in>b, a \<union> b) \<in> br Collect (\<lambda>_. True)"
    by (auto simp: br_def)

  show ?thesis
    apply (simp add: fun_set_rel_def)
    apply (intro fun_relI)
    apply clarsimp
    apply rule
    defer
    apply (rule A)
    apply (auto simp: br_def dest: fun_relD)
    done
qed

lemma fun_set_inter_refine[autoref_rules]: 
  "(\<lambda>a b x. a x \<and> b x,(\<inter>))\<in>\<langle>R\<rangle>fun_set_rel \<rightarrow> \<langle>R\<rangle>fun_set_rel \<rightarrow> \<langle>R\<rangle>fun_set_rel"
proof -
  have A: "\<And>a b. (\<lambda>x. x\<in>a \<and> x\<in>b, a \<inter> b) \<in> br Collect (\<lambda>_. True)"
    by (auto simp: br_def)

  show ?thesis
    apply (simp add: fun_set_rel_def)
    apply (intro fun_relI)
    apply clarsimp
    apply rule
    defer
    apply (rule A)
    apply (auto simp: br_def dest: fun_relD)
    done
qed


lemma fun_set_diff_refine[autoref_rules]: 
  "(\<lambda>a b x. a x \<and> \<not>b x,(-))\<in>\<langle>R\<rangle>fun_set_rel \<rightarrow> \<langle>R\<rangle>fun_set_rel \<rightarrow> \<langle>R\<rangle>fun_set_rel"
proof -
  have A: "\<And>a b. (\<lambda>x. x\<in>a \<and> \<not>x\<in>b, a - b) \<in> br Collect (\<lambda>_. True)"
    by (auto simp: br_def)

  show ?thesis
    apply (simp add: fun_set_rel_def)
    apply (intro fun_relI)
    apply clarsimp
    apply rule
    defer
    apply (rule A)
    apply (auto simp: br_def dest: fun_relD)
    done
qed



end
