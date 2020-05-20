section \<open>Commutativity of IMAP Commands\<close>

text\<open>In this section we prove the commutativity of operations and identify the edge cases.\<close>

theory
  "IMAP-proof-commute"
  imports
    "IMAP-def"  
begin

lemma (in imap) create_create_commute:
  shows "\<langle>Create i1 e1\<rangle> \<rhd> \<langle>Create i2 e2\<rangle> = \<langle>Create i2 e2\<rangle> \<rhd> \<langle>Create i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in imap) create_delete_commute:
  assumes "i \<notin> is"
  shows "\<langle>Create i e1\<rangle> \<rhd> \<langle>Delete is e2\<rangle> = \<langle>Delete is e2\<rangle> \<rhd> \<langle>Create i e1\<rangle>"
  using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def, fastforce)

lemma (in imap) create_append_commute:
  shows "\<langle>Create i1 e1\<rangle> \<rhd> \<langle>Append i2 e2\<rangle> = \<langle>Append i2 e2\<rangle> \<rhd> \<langle>Create i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in imap) create_expunge_commute:
  shows "\<langle>Create i1 e1\<rangle> \<rhd> \<langle>Expunge e2 mo i2\<rangle> = \<langle>Expunge e2 mo i2\<rangle> \<rhd> \<langle>Create i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in imap) create_store_commute:
  shows "\<langle>Create i1 e1\<rangle> \<rhd> \<langle>Store e2 mo i2\<rangle> = \<langle>Store e2 mo i2\<rangle> \<rhd> \<langle>Create i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in imap) delete_delete_commute:
  shows "\<langle>Delete i1 e1\<rangle> \<rhd> \<langle>Delete i2 e2\<rangle> = \<langle>Delete i2 e2\<rangle> \<rhd> \<langle>Delete i1 e1\<rangle>"
  by(unfold interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in imap) delete_append_commute:
  assumes "i \<notin> is"
  shows "\<langle>Delete is e1\<rangle> \<rhd> \<langle>Append i e2\<rangle> = \<langle>Append i e2\<rangle> \<rhd> \<langle>Delete is e1\<rangle>"
  using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def, fastforce)

lemma (in imap) delete_expunge_commute:
  assumes "i \<notin> is"
  shows "\<langle>Delete is e1\<rangle> \<rhd> \<langle>Expunge e2 mo i\<rangle> = \<langle>Expunge e2 mo i\<rangle> \<rhd> \<langle>Delete is e1\<rangle>"
  using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def, fastforce)

lemma (in imap) delete_store_commute:
  assumes "i \<notin> is"
  shows "\<langle>Delete is e1\<rangle> \<rhd> \<langle>Store e2 mo i\<rangle> = \<langle>Store e2 mo i\<rangle> \<rhd> \<langle>Delete is e1\<rangle>"
  using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def, fastforce)

lemma (in imap) append_append_commute:
  shows "\<langle>Append i1 e1\<rangle> \<rhd> \<langle>Append i2 e2\<rangle> = \<langle>Append i2 e2\<rangle> \<rhd> \<langle>Append i1 e1\<rangle>"
  by(auto simp add: interpret_op_def op_elem_def kleisli_def, fastforce)

lemma (in imap) append_expunge_commute:
  assumes "i1 \<noteq> mo"
  shows "(\<langle>Append i1 e1\<rangle> \<rhd> \<langle>Expunge e2 mo i2\<rangle>) = (\<langle>Expunge e2 mo i2\<rangle> \<rhd> \<langle>Append i1 e1\<rangle>)"
proof
  fix x
  show "(\<langle>Append i1 e1\<rangle> \<rhd> \<langle>Expunge e2 mo i2\<rangle>) x = (\<langle>Expunge e2 mo i2\<rangle> \<rhd> \<langle>Append i1 e1\<rangle>) x"
    using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def)
qed

lemma (in imap) append_store_commute:
  assumes "i1 \<noteq> mo"
  shows "(\<langle>Append i1 e1\<rangle> \<rhd> \<langle>Store e2 mo i2\<rangle>) = (\<langle>Store e2 mo i2\<rangle> \<rhd> \<langle>Append i1 e1\<rangle>)"
proof
  fix x
  show "(\<langle>Append i1 e1\<rangle> \<rhd> \<langle>Store e2 mo i2\<rangle>) x = (\<langle>Store e2 mo i2\<rangle> \<rhd> \<langle>Append i1 e1\<rangle>) x"
    using assms by(auto simp add: interpret_op_def kleisli_def op_elem_def)
qed

lemma (in imap) expunge_expunge_commute:
  shows "(\<langle>Expunge e1 mo1 i1\<rangle> \<rhd> \<langle>Expunge e2 mo2 i2\<rangle>) = (\<langle>Expunge e2 mo2 i2\<rangle> \<rhd> \<langle>Expunge e1 mo1 i1\<rangle>)"
proof
  fix x
  show "(\<langle>Expunge e1 mo1 i1\<rangle> \<rhd> \<langle>Expunge e2 mo2 i2\<rangle>) x 
       = (\<langle>Expunge e2 mo2 i2\<rangle> \<rhd> \<langle>Expunge e1 mo1 i1\<rangle>) x"
    by(auto simp add: interpret_op_def kleisli_def op_elem_def) qed

lemma (in imap) expunge_store_commute:
  assumes "i1 \<noteq> mo2" and "i2 \<noteq> mo1"
  shows "(\<langle>Expunge e1 mo1 i1\<rangle> \<rhd> \<langle>Store e2 mo2 i2\<rangle>) = (\<langle>Store e2 mo2 i2\<rangle> \<rhd> \<langle>Expunge e1 mo1 i1\<rangle>)"
proof
  fix x
  show "(\<langle>Expunge e1 mo1 i1\<rangle> \<rhd> \<langle>Store e2 mo2 i2\<rangle>) x = (\<langle>Store e2 mo2 i2\<rangle> \<rhd> \<langle>Expunge e1 mo1 i1\<rangle>) x"
    unfolding  interpret_op_def kleisli_def op_elem_def using assms(2) by (simp, fastforce)
qed

lemma (in imap) store_store_commute:
  assumes "i1 \<noteq> mo2" and "i2 \<noteq> mo1"
  shows "(\<langle>Store e1 mo1 i1\<rangle> \<rhd> \<langle>Store e2 mo2 i2\<rangle>) = (\<langle>Store e2 mo2 i2\<rangle> \<rhd> \<langle>Store e1 mo1 i1\<rangle>)"
proof
  fix x
  show "(\<langle>Store e1 mo1 i1\<rangle> \<rhd> \<langle>Store e2 mo2 i2\<rangle>) x = (\<langle>Store e2 mo2 i2\<rangle> \<rhd> \<langle>Store e1 mo1 i1\<rangle>) x"
    unfolding  interpret_op_def kleisli_def op_elem_def using assms by (simp, fastforce)
qed

end
