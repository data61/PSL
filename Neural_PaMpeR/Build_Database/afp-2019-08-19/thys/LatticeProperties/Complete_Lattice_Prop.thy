section \<open>Fixpoints and Complete Lattices\<close>

(*
    Author: Viorel Preoteasa
*)

theory Complete_Lattice_Prop
imports WellFoundedTransitive
begin

text\<open>
This theory introduces some results about fixpoints of functions on 
complete lattices. The main result is that a monotonic function 
mapping momotonic functions to monotonic functions has the least 
fixpoint monotonic.
\<close>

context complete_lattice begin

lemma inf_Inf: assumes nonempty: "A \<noteq> {}"
   shows "inf x (Inf A) = Inf ((inf x) ` A)"
  apply (rule antisym, simp_all)
  apply (rule INF_greatest)
  apply (safe, simp)
  apply (rule_tac y = "Inf A" in order_trans, simp_all)
  apply (rule Inf_lower, simp)
  apply (cut_tac nonempty)
  apply safe
  apply (erule notE)
  apply (rule_tac y = "inf x xa" in order_trans)
  apply (rule INF_lower, blast)
  apply simp
  apply (rule Inf_greatest)
  apply (rule_tac y = "inf x xa" in order_trans)
  apply (rule INF_lower)
  apply (simp add: image_def)
  by auto

end


(*
Monotonic applications which map monotonic to monotonic have monotonic fixpoints
*)

definition
  "mono_mono F = (mono F \<and> (\<forall> f . mono f \<longrightarrow> mono (F f)))"

theorem lfp_mono [simp]:
  "mono_mono F \<Longrightarrow> mono (lfp F)"
  apply (simp add: mono_mono_def)
  apply (rule_tac f="F" and P = "mono" in lfp_ordinal_induct)
  apply (simp_all add: mono_def)
  apply (intro allI impI SUP_least)
  apply (rule_tac y = "f y" in order_trans)
  apply (auto intro: SUP_upper)
  done

lemma gfp_ordinal_induct:
  fixes f :: "'a::complete_lattice => 'a"
  assumes mono: "mono f"
  and P_f: "!!S. P S ==> P (f S)"
  and P_Union: "!!M. \<forall>S\<in>M. P S ==> P (Inf M)"
  shows "P (gfp f)"
proof -
  let ?M = "{S. gfp f \<le> S \<and> P S}"
  have "P (Inf ?M)" using P_Union by simp
  also have "Inf ?M = gfp f"
  proof (rule antisym)
    show "gfp f \<le> Inf ?M" by (blast intro: Inf_greatest)
    hence "f (gfp f) \<le> f (Inf ?M)" by (rule mono [THEN monoD])
    hence "gfp f \<le> f (Inf ?M)" using mono [THEN gfp_unfold] by simp
    hence "f (Inf ?M) \<in> ?M" using P_f P_Union by simp
    hence "Inf ?M \<le> f (Inf ?M)" by (rule Inf_lower)
    thus "Inf ?M \<le> gfp f" by (rule gfp_upperbound)
  qed
  finally show ?thesis .
qed 
theorem gfp_mono [simp]:
  "mono_mono F \<Longrightarrow> mono (gfp F)"
  apply (simp add: mono_mono_def)
  apply (rule_tac f="F" and P = "mono" in gfp_ordinal_induct)
  apply (simp_all, safe)
  apply (simp_all add: mono_def)
  apply (intro allI impI INF_greatest)
  apply (rule_tac y = "f x" in order_trans)
  apply (auto intro: INF_lower)
  done

context complete_lattice begin

definition
  "Sup_less x (w::'b::well_founded) = Sup {y ::'a . \<exists> v < w . y = x v}"

lemma Sup_less_upper:
  "v < w \<Longrightarrow> P v \<le> Sup_less P w"
  by (simp add: Sup_less_def, rule Sup_upper, blast)


lemma Sup_less_least:
  "(!! v . v < w \<Longrightarrow> P v \<le> Q) \<Longrightarrow> Sup_less P w \<le> Q"
  by (simp add: Sup_less_def, rule Sup_least, blast)

end

lemma Sup_less_fun_eq:
  "((Sup_less P w) i) = (Sup_less (\<lambda> v . P v i)) w"
  apply (simp add: Sup_less_def fun_eq_iff)
  apply (rule arg_cong [of _ _ Sup])
  apply auto
  done

theorem fp_wf_induction:
  "f x  = x \<Longrightarrow> mono f \<Longrightarrow> (\<forall> w . (y w) \<le> f (Sup_less y w)) \<Longrightarrow> Sup (range y) \<le> x"
  apply (rule Sup_least)
  apply (simp add: image_def, safe, simp)
  apply (rule less_induct1, simp_all)
  apply (rule_tac y = "f (Sup_less y xa)" in order_trans, simp)
  apply (drule_tac x = "Sup_less y xa" and y = "x" in monoD)
  by (simp add: Sup_less_least, auto)



end
