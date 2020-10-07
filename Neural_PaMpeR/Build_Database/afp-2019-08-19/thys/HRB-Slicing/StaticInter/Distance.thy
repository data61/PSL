section \<open>Distance of Paths\<close>

theory Distance imports CFG begin

context CFG begin

inductive distance :: "'node \<Rightarrow> 'node \<Rightarrow> nat \<Rightarrow> bool"
where distanceI:
  "\<lbrakk>n -as\<rightarrow>\<^sub>\<iota>* n'; length as = x; \<forall>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> x \<le> length as'\<rbrakk>
  \<Longrightarrow> distance n n' x"


lemma every_path_distance:
  assumes "n -as\<rightarrow>\<^sub>\<iota>* n'"
  obtains x where "distance n n' x" and "x \<le> length as"
proof(atomize_elim)
  show "\<exists>x. distance n n' x \<and> x \<le> length as"
  proof(cases "\<exists>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<and> 
                     (\<forall>asx. n -asx\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> length as' \<le> length asx)")
    case True
    then obtain as' 
      where "n -as'\<rightarrow>\<^sub>\<iota>* n' \<and> (\<forall>asx. n -asx\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> length as' \<le> length asx)" 
      by blast
    hence "n -as'\<rightarrow>\<^sub>\<iota>* n'" and all:"\<forall>asx. n -asx\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> length as' \<le> length asx"
      by simp_all
    hence "distance n n' (length as')" by(fastforce intro:distanceI)
    from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> all have "length as' \<le> length as" by fastforce
    with \<open>distance n n' (length as')\<close> show ?thesis by blast
  next
    case False
    hence all:"\<forall>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> (\<exists>asx. n -asx\<rightarrow>\<^sub>\<iota>* n' \<and> length as' > length asx)"
      by fastforce
    have "wf (measure length)" by simp
    from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "as \<in> {as. n -as\<rightarrow>\<^sub>\<iota>* n'}" by simp
    with \<open>wf (measure length)\<close> obtain as' where "as' \<in> {as. n -as\<rightarrow>\<^sub>\<iota>* n'}" 
      and notin:"\<And>as''. (as'',as') \<in> (measure length) \<Longrightarrow> as'' \<notin> {as. n -as\<rightarrow>\<^sub>\<iota>* n'}"
      by(erule wfE_min)
    from \<open>as' \<in> {as. n -as\<rightarrow>\<^sub>\<iota>* n'}\<close> have "n -as'\<rightarrow>\<^sub>\<iota>* n'" by simp
    with all obtain asx where "n -asx\<rightarrow>\<^sub>\<iota>* n'"
      and "length as' > length asx"
      by blast
    with notin have  "asx \<notin> {as. n -as\<rightarrow>\<^sub>\<iota>* n'}" by simp
    hence "\<not> n -asx\<rightarrow>\<^sub>\<iota>* n'" by simp
    with \<open>n -asx\<rightarrow>\<^sub>\<iota>* n'\<close> have False by simp
    thus ?thesis by simp
  qed
qed


lemma distance_det:
  "\<lbrakk>distance n n' x; distance n n' x'\<rbrakk> \<Longrightarrow> x = x'"
apply(erule distance.cases)+ apply clarsimp
apply(erule_tac x="asa" in allE) apply(erule_tac x="as" in allE)
by simp


lemma only_one_SOME_dist_edge:
  assumes "valid_edge a" and "intra_kind(kind a)" and "distance (targetnode a) n' x"
  shows "\<exists>!a'. sourcenode a = sourcenode a' \<and> distance (targetnode a') n' x \<and>
               valid_edge a' \<and> intra_kind(kind a') \<and>
               targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                              distance (targetnode a') n' x \<and>
                                              valid_edge a' \<and> intra_kind(kind a') \<and> 
                                              targetnode a' = nx)"
proof(rule ex_ex1I)
  show "\<exists>a'. sourcenode a = sourcenode a' \<and> 
             distance (targetnode a') n' x \<and> valid_edge a' \<and> intra_kind(kind a') \<and>
             targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                            distance (targetnode a') n' x \<and>
                                            valid_edge a' \<and> intra_kind(kind a') \<and> 
                                            targetnode a' = nx)"
  proof -
    have "(\<exists>a'. sourcenode a = sourcenode a' \<and> 
                distance (targetnode a') n' x \<and> valid_edge a' \<and> intra_kind(kind a') \<and>
                targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                               distance (targetnode a') n' x \<and>
                                               valid_edge a' \<and> intra_kind(kind a') \<and> 
                                               targetnode a' = nx)) =
      (\<exists>nx. \<exists>a'. sourcenode a = sourcenode a' \<and> distance (targetnode a') n' x \<and> 
                 valid_edge a' \<and> intra_kind(kind a') \<and> targetnode a' = nx)"
      apply(unfold some_eq_ex[of "\<lambda>nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
        distance (targetnode a') n' x \<and> valid_edge a' \<and> intra_kind(kind a') \<and> 
        targetnode a' = nx"])
      by simp
    also have "\<dots>" 
      using \<open>valid_edge a\<close> \<open>intra_kind(kind a)\<close> \<open>distance (targetnode a) n' x\<close>
      by blast
    finally show ?thesis .
  qed
next
  fix a' ax
  assume "sourcenode a = sourcenode a' \<and> 
    distance (targetnode a') n' x \<and> valid_edge a' \<and> intra_kind(kind a') \<and> 
    targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                   distance (targetnode a') n' x \<and> 
                                   valid_edge a' \<and> intra_kind(kind a') \<and> 
                                   targetnode a' = nx)"
    and "sourcenode a = sourcenode ax \<and> 
    distance (targetnode ax) n' x \<and> valid_edge ax \<and> intra_kind(kind ax) \<and> 
    targetnode ax = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                   distance (targetnode a') n' x \<and> 
                                   valid_edge a' \<and> intra_kind(kind a') \<and> 
                                   targetnode a' = nx)"
  thus "a' = ax" by(fastforce intro!:edge_det)
qed


lemma distance_successor_distance:
  assumes "distance n n' x" and "x \<noteq> 0" 
  obtains a where "valid_edge a" and "n = sourcenode a" and "intra_kind(kind a)"
  and "distance (targetnode a) n' (x - 1)"
  and "targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                     distance (targetnode a') n' (x - 1) \<and>
                                     valid_edge a' \<and> intra_kind(kind a') \<and>
                                     targetnode a' = nx)"
proof(atomize_elim)
  show "\<exists>a. valid_edge a \<and> n = sourcenode a \<and> intra_kind(kind a) \<and>
    distance (targetnode a) n' (x - 1) \<and>
    targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                  distance (targetnode a') n' (x - 1) \<and>
                                  valid_edge a' \<and> intra_kind(kind a') \<and>
                                  targetnode a' = nx)"
  proof(rule ccontr)
    assume "\<not> (\<exists>a. valid_edge a \<and> n = sourcenode a \<and> intra_kind(kind a) \<and>
                   distance (targetnode a) n' (x - 1) \<and> 
                   targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 distance (targetnode a') n' (x - 1) \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = nx))"
    hence imp:"\<forall>a. valid_edge a \<and> n = sourcenode a \<and> intra_kind(kind a) \<and>
                   targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') n' (x - 1) \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = nx)
                 \<longrightarrow> \<not> distance (targetnode a) n' (x - 1)" by blast
    from \<open>distance n n' x\<close> obtain as where "n -as\<rightarrow>\<^sub>\<iota>* n'" and "x = length as"
      and all:"\<forall>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> x \<le> length as'"
      by(auto elim:distance.cases)
    from \<open>n -as\<rightarrow>\<^sub>\<iota>* n'\<close> have "n -as\<rightarrow>* n'" and "\<forall>a \<in> set as. intra_kind(kind a)"
      by(simp_all add:intra_path_def)
    from this \<open>x = length as\<close> all imp show False
    proof(induct rule:path.induct)
      case (empty_path n)
      from \<open>x = length []\<close> \<open>x \<noteq> 0\<close> show False by simp
    next
      case (Cons_path n'' as n' a n)
      note imp = \<open>\<forall>a. valid_edge a \<and> n = sourcenode a \<and> intra_kind (kind a) \<and>
                      targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') n' (x - 1) \<and>
                                                 valid_edge a' \<and> intra_kind(kind a') \<and>
                                                 targetnode a' = nx)
                    \<longrightarrow> \<not> distance (targetnode a) n' (x - 1)\<close>
      note all = \<open>\<forall>as'. n -as'\<rightarrow>\<^sub>\<iota>* n' \<longrightarrow> x \<le> length as'\<close>
      from \<open>\<forall>a\<in>set (a#as). intra_kind (kind a)\<close> 
      have "intra_kind (kind a)" and "\<forall>a\<in>set as. intra_kind (kind a)"
        by simp_all
      from \<open>n'' -as\<rightarrow>* n'\<close> \<open>\<forall>a\<in>set as. intra_kind (kind a)\<close>
      have "n'' -as\<rightarrow>\<^sub>\<iota>* n'" by(simp add:intra_path_def)
      then obtain y where "distance n'' n' y"
        and "y \<le> length as" by(erule every_path_distance)
      from \<open>distance n'' n' y\<close> obtain as' where "n'' -as'\<rightarrow>\<^sub>\<iota>* n'"
        and "y = length as'" by(auto elim:distance.cases)
      hence "n'' -as'\<rightarrow>* n'" and "\<forall>a\<in>set as'. intra_kind (kind a)"
        by(simp_all add:intra_path_def)
      show False
      proof(cases "y < length as")
        case True
        from \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>targetnode a = n''\<close> \<open>n'' -as'\<rightarrow>* n'\<close>
        have "n -a#as'\<rightarrow>* n'" by -(rule path.Cons_path)
        with \<open>\<forall>a\<in>set as'. intra_kind (kind a)\<close> \<open>intra_kind (kind a)\<close>
        have "n -a#as'\<rightarrow>\<^sub>\<iota>* n'" by(simp add:intra_path_def)
        with all have "x \<le> length (a#as')" by blast
        with \<open>x = length (a#as)\<close> True \<open>y = length as'\<close> show False by simp
      next
        case False
        with \<open>y \<le> length as\<close> \<open>x = length (a#as)\<close> have "y = x - 1" by simp
        from \<open>targetnode a = n''\<close> \<open>distance n'' n' y\<close>
        have "distance (targetnode a) n' y" by simp
        with \<open>valid_edge a\<close> \<open>intra_kind(kind a)\<close>
        obtain a' where "sourcenode a = sourcenode a'"
          and "distance (targetnode a') n' y" and "valid_edge a'"
          and "intra_kind(kind a')"
          and "targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                              distance (targetnode a') n' y \<and>
                                              valid_edge a' \<and> intra_kind(kind a') \<and>
                                              targetnode a' = nx)"
          by(auto dest:only_one_SOME_dist_edge)
        with imp \<open>sourcenode a = n\<close> \<open>y = x - 1\<close> show False by fastforce
      qed
    qed
  qed
qed

end

end
