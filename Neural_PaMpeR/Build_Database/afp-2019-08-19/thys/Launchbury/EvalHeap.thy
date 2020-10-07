theory "EvalHeap"
  imports "AList-Utils" Env Nominal2.Nominal2 "HOLCF-Utils"
begin

subsubsection \<open>Conversion from heaps to environments\<close> 

fun
  evalHeap :: "('var \<times> 'exp) list \<Rightarrow> ('exp \<Rightarrow> 'value::{pure,pcpo}) \<Rightarrow> 'var \<Rightarrow> 'value"
where
  "evalHeap [] _ = \<bottom>"
| "evalHeap ((x,e)#h) eval = (evalHeap h eval) (x := eval e)"

lemma cont2cont_evalHeap[simp, cont2cont]:
  "(\<And> e . e \<in> snd ` set h \<Longrightarrow> cont (\<lambda>\<rho>. eval \<rho> e)) \<Longrightarrow> cont (\<lambda> \<rho>. evalHeap h (eval \<rho>))"
  by(induct h, auto)

lemma evalHeap_eqvt[eqvt]:
  "\<pi> \<bullet> evalHeap h eval = evalHeap (\<pi> \<bullet> h) (\<pi> \<bullet> eval)"
  by (induct h) (auto simp add:fun_upd_eqvt  simp del: fun_upd_apply)

lemma edom_evalHeap_subset:"edom (evalHeap h eval) \<subseteq> domA h"
  by (induct h eval rule:evalHeap.induct) (auto dest:subsetD[OF edom_fun_upd_subset] simp del: fun_upd_apply)

lemma evalHeap_cong[fundef_cong]:
  "\<lbrakk> heap1 = heap2 ;  (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> eval1 e = eval2 e) \<rbrakk>
    \<Longrightarrow>  evalHeap heap1 eval1 = evalHeap heap2 eval2"
 by (induct heap2 eval2 arbitrary:heap1 rule:evalHeap.induct, auto)

lemma lookupEvalHeap:
  assumes "v \<in> domA h"
  shows "(evalHeap h f) v = f (the (map_of h v))"
  using assms
  by (induct h f rule: evalHeap.induct) auto

lemma lookupEvalHeap':
  assumes "map_of \<Gamma> v = Some e"
  shows "(evalHeap \<Gamma> f) v = f e"
  using assms
  by (induct \<Gamma> f rule: evalHeap.induct) auto

lemma lookupEvalHeap_other[simp]:
  assumes "v \<notin> domA \<Gamma>"
  shows "(evalHeap \<Gamma> f) v = \<bottom>"
  using assms
  by (induct \<Gamma> f rule: evalHeap.induct) auto

lemma env_restr_evalHeap_noop:
  "domA h \<subseteq> S \<Longrightarrow> env_restr S (evalHeap h eval) = evalHeap h eval"
  apply (rule ext)
  apply (case_tac "x \<in> S")
  apply (auto simp add: lookupEvalHeap intro: lookupEvalHeap_other)
  done

lemma env_restr_evalHeap_same[simp]:
  "env_restr (domA h) (evalHeap h eval) = evalHeap h eval"
  by (simp add: env_restr_evalHeap_noop)

lemma evalHeap_cong':
  "\<lbrakk> (\<And> x. x \<in> domA heap \<Longrightarrow> eval1 (the (map_of heap x)) = eval2 (the (map_of heap x))) \<rbrakk>
    \<Longrightarrow>  evalHeap heap eval1 = evalHeap heap eval2"
 apply (rule ext)
 apply (case_tac "x \<in> domA heap")
 apply (auto simp add: lookupEvalHeap)
 done

lemma lookupEvalHeapNotAppend[simp]:
  assumes "x \<notin> domA \<Gamma>"
  shows "(evalHeap (\<Gamma>@h) f) x = evalHeap h f x"
  using assms by (induct \<Gamma>, auto)

lemma evalHeap_delete[simp]: "evalHeap (delete x \<Gamma>) eval = env_delete x (evalHeap \<Gamma> eval)"
  by (induct \<Gamma>) auto

lemma evalHeap_mono:
  "x \<notin> domA \<Gamma> \<Longrightarrow>
  evalHeap \<Gamma> eval \<sqsubseteq> evalHeap ((x, e) # \<Gamma>) eval"
   apply simp
   apply (rule fun_belowI)
   apply (case_tac "xa \<in> domA \<Gamma>")
   apply (case_tac "xa = x")
   apply auto
   done

subsubsection \<open>Reordering lemmas\<close>

lemma evalHeap_reorder:
  assumes "map_of \<Gamma> = map_of \<Delta>"
  shows "evalHeap \<Gamma> h = evalHeap \<Delta> h"
proof (rule ext)
  from assms
  have *: "domA \<Gamma> = domA \<Delta>" by (metis dom_map_of_conv_domA)

  fix x
  show "evalHeap \<Gamma> h x = evalHeap \<Delta> h x" 
    using assms(1) *
    apply (cases "x \<in> domA \<Gamma>")
    apply (auto simp add: lookupEvalHeap)
    done
qed

lemma evalHeap_reorder_head:
  assumes "x \<noteq> y"
  shows "evalHeap ((x,e1)#(y,e2)#\<Gamma>) eval = evalHeap ((y,e2)#(x,e1)#\<Gamma>) eval"
  by (rule evalHeap_reorder) (simp add: fun_upd_twist[OF assms])

lemma evalHeap_reorder_head_append:
  assumes "x \<notin> domA \<Gamma>"
  shows "evalHeap ((x,e)#\<Gamma>@\<Delta>) eval = evalHeap (\<Gamma> @ ((x,e)#\<Delta>)) eval"
  by (rule evalHeap_reorder) (simp, metis assms dom_map_of_conv_domA map_add_upd_left)

lemma evalHeap_subst_exp:
  assumes "eval e = eval e'"
  shows "evalHeap ((x,e)#\<Gamma>) eval = evalHeap ((x,e')#\<Gamma>) eval"
  by (simp add: assms)

end
