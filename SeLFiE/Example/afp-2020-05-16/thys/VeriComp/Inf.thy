section \<open>Infinitely Transitive Closure\<close>

theory Inf
  imports Well_founded
begin

coinductive inf :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" for r where
  inf_step: "r x y \<Longrightarrow> inf r y \<Longrightarrow> inf r x"

coinductive inf_wf :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> bool" for r order where
  inf_wf: "order n m \<Longrightarrow> inf_wf r order n x \<Longrightarrow> inf_wf r order m x" |
  inf_wf_step: "r\<^sup>+\<^sup>+ x y \<Longrightarrow> inf_wf r order n y \<Longrightarrow> inf_wf r order m x"

lemma inf_wf_to_step_inf_wf:
  assumes "well_founded order"
  shows "inf_wf r order n x \<Longrightarrow> \<exists>y m. r x y \<and> inf_wf r order m y"
proof (induction n arbitrary: x rule: well_founded.induct[OF assms(1)])
  case (1 n)
  from "1.prems"(1) show ?case
  proof (induction rule: inf_wf.cases)
    case (inf_wf m n' x')
    then show ?case using "1.IH" by simp
  next
    case (inf_wf_step x' y m n')
    then show ?case
      by (metis converse_tranclpE inf_wf.inf_wf_step)
  qed
qed

lemma inf_wf_to_inf:
  assumes "well_founded order"
  shows "inf_wf r order n x \<Longrightarrow> inf r x"
proof (coinduction arbitrary: x n rule: inf.coinduct)
  case (inf x n)
  then obtain y m where "r x y" and "inf_wf r order m y"
    using inf_wf_to_step_inf_wf[OF assms(1) inf(1)] by metis
  thus ?case by auto
qed

lemma step_inf:
  assumes
    deterministic: "\<And>x y z. r x y \<Longrightarrow> r x z \<Longrightarrow> y = z"
  shows "r x y \<Longrightarrow> inf r x \<Longrightarrow> inf r y"
  by (metis deterministic inf.cases)

lemma star_inf:
  assumes
    deterministic: "\<And>x y z. r x y \<Longrightarrow> r x z \<Longrightarrow> y = z"
  shows "r\<^sup>*\<^sup>* x y \<Longrightarrow> inf r x \<Longrightarrow> inf r y"
proof (induction y rule: rtranclp_induct)
  case base
  then show ?case .
next
  case (step y z)
  then show ?case
    using step_inf deterministic by metis
qed

end