section \<open>Very Basic LTS Formalization\<close>
theory LTS
imports CAVA_Automata.Digraph
begin

  (* TODO: transition labeled automata, not supported by CAVA automata library *)

  locale LTS =
    fixes step :: "'s \<Rightarrow> 'l \<Rightarrow> 's \<Rightarrow> bool"
  begin
    primrec path :: "'s \<Rightarrow> 'l list \<Rightarrow> 's \<Rightarrow> bool" where
      "path s [] s' \<longleftrightarrow> s'=s"
    | "path s (l#ls) s' \<longleftrightarrow> (\<exists>sh. step s l sh \<and> path sh ls s')"

    lemma path_append[simp]: 
      "path s (p@p') s' \<longleftrightarrow> (\<exists>sh. path s p sh \<and> path sh p' s')"
      by (induction p arbitrary: s) auto

    lemma path_trans[trans]:
      "step s l sh \<Longrightarrow> step sh l' s' \<Longrightarrow> path s [l,l'] s'"
      "step s l sh \<Longrightarrow> path sh p s' \<Longrightarrow> path s (l#p) s'"
      "path s p sh \<Longrightarrow> step sh l s' \<Longrightarrow> path s (p@[l]) s'"
      "path s p sh \<Longrightarrow> path sh p' s' \<Longrightarrow> path s (p@p') s'"
      by auto

    lemma path_sngI: "step s a s' \<Longrightarrow> path s [a] s'" by auto
    lemma path_emptyI: "path s [] s" by auto

    definition "reachable s s' \<equiv> \<exists>p. path s p s'"
    lemma reachableI: "path s p s' \<Longrightarrow> reachable s s'"
      unfolding reachable_def by auto

    lemma reachable_trans[trans]:
      "reachable s sh \<Longrightarrow> step sh l s' \<Longrightarrow> reachable s s'"
      "reachable s sh \<Longrightarrow> path sh p s' \<Longrightarrow> reachable s s'"
      "path s p sh \<Longrightarrow> reachable sh s' \<Longrightarrow> reachable s s'"
      "step s l sh \<Longrightarrow> reachable sh s' \<Longrightarrow> reachable s s'"
      unfolding reachable_def
      by (auto dest: path_trans)
    
  end

  locale asystem =
    lts: LTS astep
    for init :: "'c \<Rightarrow> bool"
    and astep :: "'c \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> bool"
  begin

    definition step :: "'c digraph"
      where "step \<equiv> {(c, c'). \<exists> a. astep c a c'}"

    definition G :: "'c graph_rec"
      where "G \<equiv> \<lparr> g_V = UNIV, g_E = step, g_V0 = Collect init \<rparr>"

    lemma G_simps[simp]:
      "g_V G = UNIV"
      "g_E G = step"
      "g_V0 G = Collect init"
      unfolding G_def by simp+
  
    sublocale graph G by unfold_locales auto
  
    lemma path_is_step: "lts.path c p c' \<Longrightarrow> (c, c') \<in> step\<^sup>*"
      unfolding step_def
      apply (induction p arbitrary: c)
      apply auto
      by (metis (mono_tags, lifting) case_prod_conv converse_rtrancl_into_rtrancl mem_Collect_eq)

    lemma step_is_path: "(c, c') \<in> step\<^sup>* \<Longrightarrow> \<exists>p. lts.path c p c'"
    proof (induction rule: converse_rtrancl_induct, safe)
      fix c
      show "\<exists>p. lts.path c p c"
        apply (rule exI[where x="[]"])
        by auto 
    next
      fix c ch p
      assume "(c, ch) \<in> step" and 1: "lts.path ch p c'"
      then obtain a where "astep c a ch" by (auto simp: step_def)
      with 1 show "\<exists>p. lts.path c p c'" 
        apply (rule_tac exI[where x="a#p"]) by auto
    qed
  
    lemma step_path_conv: "(c, c') \<in> step\<^sup>* \<longleftrightarrow> (\<exists>p. lts.path c p c')"
      using path_is_step step_is_path by blast
  
  end

end

