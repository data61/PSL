(* Author:     Tobias Nipkow
*)

section\<open>Tame Properties\<close>

theory TameProps
imports Tame RTranCl
begin

lemma length_disj_filter_le: "\<forall>x \<in> set xs. \<not>(P x \<and> Q x) \<Longrightarrow>
 length(filter P xs) + length(filter Q xs) \<le> length xs"
by(induct xs) auto

lemma tri_quad_le_degree: "tri g v + quad g v \<le> degree g v"
proof -
  let ?fins = "[f \<leftarrow> facesAt g v . final f]"
  have "tri g v + quad g v =
        |[f \<leftarrow> ?fins . triangle f]| + |[f \<leftarrow> ?fins. |vertices f| = 4]|"
    by(simp add:tri_def quad_def)
  also have "\<dots> \<le> |[f \<leftarrow> facesAt g v. final f]|"
    by(rule length_disj_filter_le) simp
  also have "\<dots> \<le> |facesAt g v|" by(rule length_filter_le)
  finally show ?thesis by(simp add:degree_def)
qed

lemma faceCountMax_bound:
 "\<lbrakk> tame g; v \<in> \<V> g \<rbrakk> \<Longrightarrow> tri g v + quad g v \<le> 7"
using tri_quad_le_degree[of g v]
by(auto simp:tame_def tame11b_def split:if_split_asm)


lemma filter_tame_succs:
assumes invP: "invariant P succs" and fin: "\<And>g. final g \<Longrightarrow> succs g = []"
and ok_untame: "\<And>g. P g \<Longrightarrow> \<not> ok g \<Longrightarrow> final g \<and> \<not> tame g"
and gg': "g [succs]\<rightarrow>* g'"
shows "P g \<Longrightarrow> final g' \<Longrightarrow> tame g' \<Longrightarrow> g [filter ok \<circ> succs]\<rightarrow>* g'"
using gg'
proof (induct rule:RTranCl.induct)
  case refl show ?case by(rule RTranCl.refl)
next
  case (succs h h' h'')
  hence "P h'"  using invP by(unfold invariant_def) blast
  show ?case
  proof cases
    assume "ok h'"
    thus ?thesis using succs \<open>P h'\<close> by(fastforce intro:RTranCl.succs)
  next
    assume "\<not> ok h'" note fin_tame = ok_untame[OF \<open>P h'\<close> \<open>\<not> ok h'\<close>]
    have "h'' = h'" using fin_tame
      by(rule_tac RTranCl.cases[OF succs(2)])(auto simp:fin)
    hence False using fin_tame succs by fast
    thus ?case ..
  qed
qed


definition untame :: "(graph \<Rightarrow> bool) \<Rightarrow> bool" where
"untame P \<equiv> \<forall>g. final g \<and> P g \<longrightarrow> \<not> tame g"


lemma filterout_untame_succs:
assumes invP: "invariant P f" and invPU: "invariant (\<lambda>g. P g \<and>  U g) f"
and untame: "untame(\<lambda>g. P g \<and> U g)"
and new_untame: "\<And>g g'. \<lbrakk> P g; g' \<in> set(f g); g' \<notin> set(f' g) \<rbrakk> \<Longrightarrow> U g'"
and gg': "g [f]\<rightarrow>* g'"
shows "P g \<Longrightarrow> final g' \<Longrightarrow> tame g' \<Longrightarrow> g [f']\<rightarrow>* g'"
using gg'
proof (induct rule:RTranCl.induct)
  case refl show ?case by(rule RTranCl.refl)
next
  case (succs h h' h'')
  hence Ph': "P h'"  using invP by(unfold invariant_def) blast
  show ?case
  proof cases
    assume "h' \<in> set(f' h)"
    thus ?thesis using succs Ph' by(blast intro:RTranCl.succs)
  next
    assume "h' \<notin> set(f' h)"
    with succs(4) succs(1) have "U h'" by (rule new_untame)
    hence False using Ph' RTranCl_inv[OF invPU] untame succs
      by (unfold untame_def) fast
    thus ?case ..
  qed
qed

end
