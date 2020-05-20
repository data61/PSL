section \<open>Order Pairs\<close>

text \<open>
  An order pair consists of two relations @{term S} and @{term NS}, where @{term S}
  is a strict order and @{term NS} a compatible non-strict order,
  such that the combination of @{term S} and @{term NS} always results in strict decrease.
\<close>

theory Order_Pair
  imports "Abstract-Rewriting.Relative_Rewriting"
begin

named_theorems order_simps
declare O_assoc[order_simps]

locale pre_order_pair = 
  fixes S :: "'a rel"
    and NS :: "'a rel"
  assumes refl_NS: "refl NS"
    and trans_S: "trans S"
    and trans_NS: "trans NS"
begin

lemma refl_NS_point: "(s, s) \<in> NS" using refl_NS unfolding refl_on_def by blast

lemma NS_O_NS[order_simps]: "NS O NS = NS" "NS O NS O T = NS O T"
proof -
  show "NS O NS = NS" by(fact trans_refl_imp_O_id[OF trans_NS refl_NS])
  then show "NS O NS O T = NS O T" by fast
qed

lemma trancl_NS[order_simps]: "NS\<^sup>+ = NS" using trans_NS by simp

lemma rtrancl_NS[order_simps]: "NS\<^sup>* = NS"
  by (rule trans_refl_imp_rtrancl_id[OF trans_NS refl_NS])

lemma trancl_S[order_simps]: "S\<^sup>+ = S" using trans_S by simp

lemma S_O_S: "S O S \<subseteq> S" "S O S O T \<subseteq> S O T"
proof -
  show "S O S \<subseteq> S" by (fact trans_O_subset[OF trans_S])
  then show "S O S O T \<subseteq> S O T" by blast
qed

lemma trans_S_point: "\<And> x y z. (x, y) \<in> S \<Longrightarrow> (y, z) \<in> S \<Longrightarrow> (x, z) \<in> S"
  using trans_S unfolding trans_def by blast

lemma trans_NS_point: "\<And> x y z. (x, y) \<in> NS \<Longrightarrow> (y, z) \<in> NS \<Longrightarrow> (x, z) \<in> NS"
  using trans_NS unfolding trans_def by blast
end

locale compat_pair = 
  fixes S NS :: "'a rel" 
  assumes compat_NS_S: "NS O S \<subseteq> S"
    and compat_S_NS: "S O NS \<subseteq> S"
begin
lemma compat_NS_S_point: "\<And> x y z. (x, y) \<in> NS \<Longrightarrow> (y, z) \<in> S \<Longrightarrow> (x, z) \<in> S"
  using compat_NS_S by blast

lemma compat_S_NS_point: "\<And> x y z. (x, y) \<in> S \<Longrightarrow> (y, z) \<in> NS \<Longrightarrow> (x, z) \<in> S"
  using compat_S_NS by blast

lemma S_O_rtrancl_NS[order_simps]: "S O NS\<^sup>* = S" "S O NS\<^sup>* O T = S O T"
proof -
  show "S O NS\<^sup>* = S"
  proof(intro equalityI subrelI)
    fix x y assume "(x, y) \<in> S O NS\<^sup>*"
    then obtain n where "(x, y) \<in> S O NS^^n" by blast
    then show "(x, y) \<in> S"
    proof(induct n arbitrary: y)
      case 0 then show ?case by auto
    next
      case IH: (Suc n)
      then obtain z where xz: "(x, z) \<in> S O NS^^n" and zy: "(z, y) \<in> NS" by auto
      from IH.hyps[OF xz] zy have "(x, y) \<in> S O NS" by auto
      with compat_S_NS show ?case by auto
    qed
  qed auto
  then show "S O NS\<^sup>* O T = S O T" by auto
qed

lemma rtrancl_NS_O_S[order_simps]: "NS\<^sup>* O S = S" "NS\<^sup>* O S O T = S O T"
proof -
  show "NS\<^sup>* O S = S"
  proof(intro equalityI subrelI)
    fix x y assume "(x, y) \<in> NS\<^sup>* O S"
    then obtain n where "(x, y) \<in> NS^^n O S" by blast
    then show "(x, y) \<in> S"
    proof(induct n arbitrary: x)
      case 0 then show ?case by auto
    next
      case IH: (Suc n)
      then obtain z where xz: "(x, z) \<in> NS" and zy: "(z, y) \<in> NS^^n O S" by (unfold relpow_Suc, auto)
      from xz IH.hyps[OF zy] have "(x, y) \<in> NS O S" by auto
      with compat_NS_S show ?case by auto
    qed
  qed auto
  then show "NS\<^sup>* O S O T = S O T" by auto
qed

end

locale order_pair = pre_order_pair S NS + compat_pair S NS 
  for S NS :: "'a rel"
begin

lemma S_O_NS[order_simps]: "S O NS = S" "S O NS O T = S O T" by (fact S_O_rtrancl_NS[unfolded rtrancl_NS])+
lemma NS_O_S[order_simps]: "NS O S = S" "NS O S O T = S O T" by (fact rtrancl_NS_O_S[unfolded rtrancl_NS])+

lemma compat_rtrancl:
  assumes ab: "(a, b) \<in> S"
    and bc: "(b, c) \<in> (NS \<union> S)\<^sup>*"
  shows "(a, c) \<in> S"
  using bc
proof (induct)
  case base
  show ?case by (rule ab)
next
  case (step c d)
  from step(2-3) show ?case using compat_S_NS_point trans_S unfolding trans_def by blast
qed

end

locale SN_ars =
  fixes S :: "'a rel"
  assumes SN: "SN S"

locale SN_pair = compat_pair S NS + SN_ars S for S NS :: "'a rel"

locale SN_order_pair = order_pair S NS + SN_ars S for S NS :: "'a rel"

sublocale SN_order_pair \<subseteq> SN_pair ..

end
