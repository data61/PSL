subsection \<open>The view-partitioning equivalence relation\<close>

theory Step_vpeq
  imports Step Step_invariants
begin

text \<open>The view consists of
 \begin{enumerate}
 \item View of object values.
 \item View of subject-subject dynamic policy. The threads can discover the policy
       at runtime, e.g. by calling ipc() and observing success or failure.
 \item View of subject-object dynamic policy. The threads can discover the policy
       at runtime, e.g. by calling open() and observing success or failure.
 \end{enumerate}
\<close>

definition vpeq_obj :: "partition_id_t \<Rightarrow> state_t \<Rightarrow> state_t \<Rightarrow> bool" where
  "vpeq_obj u s t \<equiv> \<forall> obj_id . Policy.sp_spec_subj_obj u obj_id READ \<longrightarrow> (obj s) obj_id = (obj t) obj_id"

definition vpeq_subj_subj :: "partition_id_t \<Rightarrow> state_t \<Rightarrow> state_t \<Rightarrow> bool" where
  "vpeq_subj_subj u s t \<equiv>
    \<forall> v . ((Policy.sp_spec_subj_subj u v \<longrightarrow> sp_impl_subj_subj s u v = sp_impl_subj_subj t u v)
           \<and> (Policy.sp_spec_subj_subj v u \<longrightarrow> sp_impl_subj_subj s v u = sp_impl_subj_subj t v u))"

definition vpeq_subj_obj :: "partition_id_t \<Rightarrow> state_t \<Rightarrow> state_t \<Rightarrow> bool" where
  "vpeq_subj_obj u s t \<equiv>    
   \<forall> ob m p1 .
     (Policy.sp_spec_subj_obj u ob m \<longrightarrow> sp_impl_subj_obj s u ob m = sp_impl_subj_obj t u ob m) 
   \<and> (Policy.sp_spec_subj_obj p1 ob PROVIDE \<and> (Policy.sp_spec_subj_obj u ob READ \<or> Policy.sp_spec_subj_obj u ob WRITE) \<longrightarrow>
         sp_impl_subj_obj s p1 ob PROVIDE = sp_impl_subj_obj t p1 ob PROVIDE)"
   

definition vpeq_local :: "partition_id_t \<Rightarrow> state_t \<Rightarrow> state_t \<Rightarrow> bool" where
 "vpeq_local u s t \<equiv>
    \<forall> tid . (partition tid) = u \<longrightarrow> (thread s tid) = (thread t tid)"

definition "vpeq u s t \<equiv>
   vpeq_obj u s t \<and> vpeq_subj_subj u s t \<and> vpeq_subj_obj u s t \<and> vpeq_local u s t"

subsubsection \<open>Elementary properties\<close>

lemma vpeq_rel:
  shows vpeq_refl: "vpeq u s s"
    and vpeq_sym [sym]: "vpeq u s t \<Longrightarrow> vpeq u t s"
    and vpeq_trans [trans]: "\<lbrakk> vpeq u s1 s2 ; vpeq u s2 s3 \<rbrakk> \<Longrightarrow> vpeq u s1 s3"
  unfolding vpeq_def vpeq_obj_def vpeq_subj_subj_def vpeq_subj_obj_def vpeq_local_def
    by auto

text \<open>Auxiliary equivalence relation.\<close>


lemma set_object_value_ign:
  assumes eq_obs: "~ Policy.sp_spec_subj_obj u x READ"
    shows "vpeq u s (set_object_value x y s)"
proof -
  from assms show ?thesis
    unfolding vpeq_def vpeq_obj_def vpeq_subj_subj_def vpeq_subj_obj_def set_object_value_def 
              vpeq_local_def
    by auto
qed

text \<open>Context-switch and fetch operations are also consistent with vpeq
        and locally respect everything.\<close>

theorem cswitch_consistency_and_respect:
  fixes u :: partition_id_t 
    and s :: state_t
    and new_current :: thread_id_t
  assumes "atomic_step_invariant s"
  shows "vpeq u s (s \<lparr> current := new_current \<rparr>)"
proof -
  show ?thesis
    unfolding vpeq_def vpeq_obj_def vpeq_subj_subj_def vpeq_subj_obj_def vpeq_local_def
    by auto
qed



end

