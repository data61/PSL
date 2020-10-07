theory Kuratowski_Combinatorial
imports
  Planar_Complete
  Planar_Subdivision
  Planar_Subgraph
begin

theorem comb_planar_compat:
  assumes "comb_planar G"
  shows "kuratowski_planar G"
proof (rule ccontr)
  assume "\<not>?thesis"
  then obtain G0 rev_G0 K rev_K where sub: "subgraph G0 G" "subdivision (K, rev_K) (G0, rev_G0)"
      and is_kur: "K\<^bsub>3,3\<^esub> K \<or> K\<^bsub>5\<^esub> K"
    unfolding kuratowski_planar_def by auto

  have "comb_planar K" using sub assms 
    by (metis subgraph_comb_planar subdivision_comb_planar subdivision_bidir)
  moreover
  have "\<not>comb_planar K" using is_kur by (metis K5_not_comb_planar K33_not_comb_planar)
  ultimately
  show False by contradiction
qed

end
