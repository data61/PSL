section \<open>Static backward slice\<close>

theory Slice 
  imports Observable Distance DataDependence "../Basic/SemanticsCFG"  
begin

locale BackwardSlice = 
  CFG_wf sourcenode targetnode kind valid_edge Entry Def Use state_val
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val" +
  fixes backward_slice :: "'node set \<Rightarrow> 'node set"
  assumes valid_nodes:"n \<in> backward_slice S \<Longrightarrow> valid_node n"
  and refl:"\<lbrakk>valid_node n; n \<in> S\<rbrakk> \<Longrightarrow> n \<in> backward_slice S"
  and dd_closed:"\<lbrakk>n' \<in> backward_slice S; n influences V in n'\<rbrakk> 
  \<Longrightarrow> n \<in> backward_slice S"
  and obs_finite:"finite (obs n (backward_slice S))"
  and obs_singleton:"card (obs n (backward_slice S)) \<le> 1"

begin

lemma slice_n_in_obs:
  "n \<in> backward_slice S \<Longrightarrow> obs n (backward_slice S) = {n}"
by(fastforce intro!:n_in_obs dest:valid_nodes)

lemma obs_singleton_disj: 
  "(\<exists>m. obs n (backward_slice S) = {m}) \<or> obs n (backward_slice S) = {}"
proof -
  have "finite(obs n (backward_slice S))" by(rule obs_finite)
  show ?thesis
  proof(cases "card(obs n (backward_slice S)) = 0")
    case True
    with \<open>finite(obs n (backward_slice S))\<close> have "obs n (backward_slice S) = {}"
      by simp
    thus ?thesis by simp
  next
    case False
    have "card(obs n (backward_slice S)) \<le> 1" by(rule obs_singleton)
    with False have "card(obs n (backward_slice S)) = 1"
      by simp
    hence "\<exists>m. obs n (backward_slice S) = {m}" by(fastforce dest:card_eq_SucD)
    thus ?thesis by simp
  qed
qed


lemma obs_singleton_element:
  assumes "m \<in> obs n (backward_slice S)" shows "obs n (backward_slice S) = {m}"
proof -
  have "(\<exists>m. obs n (backward_slice S) = {m}) \<or> obs n (backward_slice S) = {}"
    by(rule obs_singleton_disj)
  with \<open>m \<in> obs n (backward_slice S)\<close> show ?thesis by fastforce
qed


lemma obs_the_element: 
  "m \<in> obs n (backward_slice S) \<Longrightarrow> (THE m. m \<in> obs n (backward_slice S)) = m"
by(fastforce dest:obs_singleton_element)


subsection \<open>Traversing the sliced graph\<close>

text \<open>\<open>slice_kind S a\<close> conforms to @{term "kind a"} in the
  sliced graph\<close>

definition slice_kind :: "'node set \<Rightarrow> 'edge \<Rightarrow> 'state edge_kind"
  where "slice_kind S a = (let S' = backward_slice S; n = sourcenode a in 
  (if sourcenode a \<in> S' then kind a
   else (case kind a of \<Up>f \<Rightarrow> \<Up>id | (Q)\<^sub>\<surd> \<Rightarrow> 
    (if obs (sourcenode a) S' = {} then 
      (let nx = (SOME n'. \<exists>a'. n = sourcenode a' \<and> valid_edge a' \<and> targetnode a' = n')
      in (if (targetnode a = nx) then (\<lambda>s. True)\<^sub>\<surd> else (\<lambda>s. False)\<^sub>\<surd>))
     else (let m = THE m. m \<in> obs n S' in 
       (if (\<exists>x. distance (targetnode a) m x \<and> distance n m (x + 1) \<and>
            (targetnode a = (SOME nx'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                     distance (targetnode a') m x \<and>
                                     valid_edge a' \<and> targetnode a' = nx'))) 
          then (\<lambda>s. True)\<^sub>\<surd> else (\<lambda>s. False)\<^sub>\<surd>
       ))
     ))
  ))"


definition
  slice_kinds :: "'node set \<Rightarrow> 'edge list \<Rightarrow> 'state edge_kind list"
  where "slice_kinds S as \<equiv> map (slice_kind S) as"


lemma slice_kind_in_slice:
  "sourcenode a \<in> backward_slice S \<Longrightarrow> slice_kind S a = kind a"
by(simp add:slice_kind_def)


lemma slice_kind_Upd:
  "\<lbrakk>sourcenode a \<notin> backward_slice S; kind a = \<Up>f\<rbrakk> \<Longrightarrow> slice_kind S a = \<Up>id"
by(simp add:slice_kind_def)


lemma slice_kind_Pred_empty_obs_SOME:
  "\<lbrakk>sourcenode a \<notin> backward_slice S; kind a = (Q)\<^sub>\<surd>; 
    obs (sourcenode a) (backward_slice S) = {}; 
    targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
                                  targetnode a' = n')\<rbrakk>
  \<Longrightarrow> slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
by(simp add:slice_kind_def)


lemma slice_kind_Pred_empty_obs_not_SOME:
  "\<lbrakk>sourcenode a \<notin> backward_slice S; kind a = (Q)\<^sub>\<surd>; 
    obs (sourcenode a) (backward_slice S) = {}; 
    targetnode a \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
                                  targetnode a' = n')\<rbrakk>
  \<Longrightarrow> slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
by(simp add:slice_kind_def)


lemma slice_kind_Pred_obs_nearer_SOME:
  assumes "sourcenode a \<notin> backward_slice S" and "kind a = (Q)\<^sub>\<surd>" 
  and "m \<in> obs (sourcenode a) (backward_slice S)"
  and "distance (targetnode a) m x" "distance (sourcenode a) m (x + 1)"
  and "targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                          distance (targetnode a') m x \<and>
                                          valid_edge a' \<and> targetnode a' = n')"
  shows "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
proof -
  from \<open>m \<in> obs (sourcenode a) (backward_slice S)\<close>
  have "m = (THE m. m \<in> obs (sourcenode a) (backward_slice S))"
    by(rule obs_the_element[THEN sym])
  with assms show ?thesis
    by(fastforce simp:slice_kind_def Let_def)
qed


lemma slice_kind_Pred_obs_nearer_not_SOME:
  assumes "sourcenode a \<notin> backward_slice S" and "kind a = (Q)\<^sub>\<surd>" 
  and "m \<in> obs (sourcenode a) (backward_slice S)"
  and "distance (targetnode a) m x" "distance (sourcenode a) m (x + 1)"
  and "targetnode a \<noteq> (SOME nx'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                          distance (targetnode a') m x \<and>
                                          valid_edge a' \<and> targetnode a' = nx')"
  shows "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
proof -
  from \<open>m \<in> obs (sourcenode a) (backward_slice S)\<close>
  have "m = (THE m. m \<in> obs (sourcenode a) (backward_slice S))"
    by(rule obs_the_element[THEN sym])
  with assms show ?thesis
    by(fastforce dest:distance_det simp:slice_kind_def Let_def)
qed


lemma slice_kind_Pred_obs_not_nearer:
  assumes "sourcenode a \<notin> backward_slice S" and "kind a = (Q)\<^sub>\<surd>" 
  and in_obs:"m \<in> obs (sourcenode a) (backward_slice S)"
  and dist:"distance (sourcenode a) m (x + 1)" 
           "\<not> distance (targetnode a) m x"
  shows "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
proof -
  from in_obs have the:"m = (THE m. m \<in> obs (sourcenode a) (backward_slice S))"
    by(rule obs_the_element[THEN sym])
  from dist have "\<not> (\<exists>x. distance (targetnode a) m x \<and> 
                            distance (sourcenode a) m (x + 1))"
    by(fastforce dest:distance_det)
  with \<open>sourcenode a \<notin> backward_slice S\<close> \<open>kind a = (Q)\<^sub>\<surd>\<close> in_obs the show ?thesis
    by(fastforce simp:slice_kind_def Let_def)
qed


lemma kind_Predicate_notin_slice_slice_kind_Predicate:
  assumes "kind a = (Q)\<^sub>\<surd>" and "sourcenode a \<notin> backward_slice S"
  obtains Q' where "slice_kind S a = (Q')\<^sub>\<surd>" and "Q' = (\<lambda>s. False) \<or> Q' = (\<lambda>s. True)"
proof(atomize_elim)
  show "\<exists>Q'. slice_kind S a = (Q')\<^sub>\<surd> \<and> (Q' = (\<lambda>s. False) \<or> Q' = (\<lambda>s. True))"
  proof(cases "obs (sourcenode a) (backward_slice S) = {}")
    case True
    show ?thesis
    proof(cases "targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               valid_edge a' \<and> targetnode a' = n')")
      case True
      with \<open>sourcenode a \<notin> backward_slice S\<close> \<open>kind a = (Q)\<^sub>\<surd>\<close>
        \<open>obs (sourcenode a) (backward_slice S) = {}\<close>
      have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>" by(rule slice_kind_Pred_empty_obs_SOME)
      thus ?thesis by simp
    next
      case False
      with \<open>sourcenode a \<notin> backward_slice S\<close> \<open>kind a = (Q)\<^sub>\<surd>\<close>
        \<open>obs (sourcenode a) (backward_slice S) = {}\<close>
      have "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
        by(rule slice_kind_Pred_empty_obs_not_SOME)
      thus ?thesis by simp
    qed
  next
    case False
    then obtain m where "m \<in> obs (sourcenode a) (backward_slice S)" by blast
    show ?thesis
    proof(cases "\<exists>x. distance (targetnode a) m x \<and> 
        distance (sourcenode a) m (x + 1)")
      case True
      then obtain x where "distance (targetnode a) m x" 
        and "distance (sourcenode a) m (x + 1)" by blast
      show ?thesis
      proof(cases "targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') m x \<and>
                                                 valid_edge a' \<and> targetnode a' = n')")
        case True
        with \<open>sourcenode a \<notin> backward_slice S\<close> \<open>kind a = (Q)\<^sub>\<surd>\<close>
          \<open>m \<in> obs (sourcenode a) (backward_slice S)\<close>
          \<open>distance (targetnode a) m x\<close> \<open>distance (sourcenode a) m (x + 1)\<close>
        have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
          by(rule slice_kind_Pred_obs_nearer_SOME)
        thus ?thesis by simp
      next
        case False
        with \<open>sourcenode a \<notin> backward_slice S\<close> \<open>kind a = (Q)\<^sub>\<surd>\<close>
          \<open>m \<in> obs (sourcenode a) (backward_slice S)\<close>
          \<open>distance (targetnode a) m x\<close> \<open>distance (sourcenode a) m (x + 1)\<close>
        have "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
          by(rule slice_kind_Pred_obs_nearer_not_SOME)
        thus ?thesis by simp
      qed
    next
      case False
      from \<open>m \<in> obs (sourcenode a) (backward_slice S)\<close>
      have "m = (THE m. m \<in> obs (sourcenode a) (backward_slice S))"
        by(rule obs_the_element[THEN sym])
      with \<open>sourcenode a \<notin> backward_slice S\<close> \<open>kind a = (Q)\<^sub>\<surd>\<close> False
        \<open>m \<in> obs (sourcenode a) (backward_slice S)\<close>
      have "slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
        by(fastforce simp:slice_kind_def Let_def)
      thus ?thesis by simp
    qed
  qed
qed


lemma only_one_SOME_edge:
  assumes "valid_edge a"
  shows "\<exists>!a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
               targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                              valid_edge a' \<and> targetnode a' = n')"
proof(rule ex_ex1I)
  show "\<exists>a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
             targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                            valid_edge a' \<and> targetnode a' = n')"
  proof -
    have "(\<exists>a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
                targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               valid_edge a' \<and> targetnode a' = n')) =
      (\<exists>n'. \<exists>a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and> targetnode a' = n')"
      apply(unfold some_eq_ex[of "\<lambda>n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                            valid_edge a' \<and> targetnode a' = n'"])
      by simp
    also have "\<dots>" using \<open>valid_edge a\<close> by blast
    finally show ?thesis .
  qed
next
  fix a' ax
  assume "sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
    targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                   valid_edge a' \<and> targetnode a' = n')"
    and "sourcenode a = sourcenode ax \<and> valid_edge ax \<and>
    targetnode ax = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                              valid_edge a' \<and> targetnode a' = n')"
  thus "a' = ax" by(fastforce intro!:edge_det)
qed


lemma slice_kind_only_one_True_edge:
  assumes "sourcenode a = sourcenode a'" and "targetnode a \<noteq> targetnode a'" 
  and "valid_edge a" and "valid_edge a'" and "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
  shows "slice_kind S a' = (\<lambda>s. False)\<^sub>\<surd>"
proof -
  from assms obtain Q Q' where "kind a = (Q)\<^sub>\<surd>"
    and "kind a' = (Q')\<^sub>\<surd>" and det:"\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
    by(auto dest:deterministic)
  from \<open>valid_edge a\<close> have ex1:"\<exists>!a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
               targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                              valid_edge a' \<and> targetnode a' = n')"
    by(rule only_one_SOME_edge)
  show ?thesis
  proof(cases "sourcenode a \<in> backward_slice S")
    case True
    with \<open>slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>kind a = (Q)\<^sub>\<surd>\<close> have "Q = (\<lambda>s. True)"
      by(simp add:slice_kind_def Let_def)
    with det have "Q' = (\<lambda>s. False)" by(simp add:fun_eq_iff)
    with True \<open>kind a' = (Q')\<^sub>\<surd>\<close> \<open>sourcenode a = sourcenode a'\<close> show ?thesis
      by(simp add:slice_kind_def Let_def)
  next
    case False
    hence "sourcenode a \<notin> backward_slice S" by simp
    thus ?thesis
    proof(cases "obs (sourcenode a) (backward_slice S) = {}")
      case True
      with \<open>sourcenode a \<notin> backward_slice S\<close> \<open>slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>\<close>
        \<open>kind a = (Q)\<^sub>\<surd>\<close>
      have target:"targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 valid_edge a' \<and> targetnode a' = n')"
        by(auto simp:slice_kind_def Let_def fun_eq_iff split:if_split_asm)
      have "targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                            valid_edge a' \<and> targetnode a' = n')"
      proof(rule ccontr)
        assume "\<not> targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 valid_edge a' \<and> targetnode a' = n')"
        hence "targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                              valid_edge a' \<and> targetnode a' = n')"
          by simp
        with ex1 target \<open>sourcenode a = sourcenode a'\<close> \<open>valid_edge a\<close>
          \<open>valid_edge a'\<close> have "a = a'" by blast
        with \<open>targetnode a \<noteq> targetnode a'\<close> show False by simp
      qed
      with \<open>sourcenode a \<notin> backward_slice S\<close> True \<open>kind a' = (Q')\<^sub>\<surd>\<close>
        \<open>sourcenode a = sourcenode a'\<close> show ?thesis 
        by(auto simp:slice_kind_def Let_def fun_eq_iff split:if_split_asm)
    next
      case False
      hence "obs (sourcenode a) (backward_slice S) \<noteq> {}" .
      then obtain m where "m \<in> obs (sourcenode a) (backward_slice S)" by auto
      hence "m = (THE m. m \<in> obs (sourcenode a) (backward_slice S))"
        by(auto dest:obs_the_element)
      with \<open>sourcenode a \<notin> backward_slice S\<close> 
        \<open>obs (sourcenode a) (backward_slice S) \<noteq> {}\<close> 
        \<open>slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>\<close> \<open>kind a = (Q)\<^sub>\<surd>\<close>
      obtain x x' where "distance (targetnode a) m x" 
        "distance (sourcenode a) m (x + 1)"
        and target:"targetnode a = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') m x \<and>
                                                 valid_edge a' \<and> targetnode a' = n')"
        by(auto simp:slice_kind_def Let_def fun_eq_iff split:if_split_asm)
      show ?thesis
      proof(cases "distance (targetnode a') m x")
        case False
        with \<open>sourcenode a \<notin> backward_slice S\<close> \<open>kind a' = (Q')\<^sub>\<surd>\<close>
          \<open>m \<in> obs (sourcenode a) (backward_slice S)\<close>
          \<open>distance (targetnode a) m x\<close> \<open>distance (sourcenode a) m (x + 1)\<close>
          \<open>sourcenode a = sourcenode a'\<close> show ?thesis
          by(fastforce intro:slice_kind_Pred_obs_not_nearer)
      next
        case True
        from \<open>valid_edge a\<close> \<open>distance (targetnode a) m x\<close>
          \<open>distance (sourcenode a) m (x + 1)\<close>
        have ex1:"\<exists>!a'. sourcenode a = sourcenode a' \<and> 
               distance (targetnode a') m x \<and> valid_edge a' \<and>
               targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                              distance (targetnode a') m x \<and>
                                              valid_edge a' \<and> targetnode a' = nx)"
          by(fastforce intro!:only_one_SOME_dist_edge)
        have "targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                               distance (targetnode a') m x \<and>
                                               valid_edge a' \<and> targetnode a' = n')"
        proof(rule ccontr)
          assume "\<not> targetnode a' \<noteq> (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 distance (targetnode a') m x \<and>
                                                 valid_edge a' \<and> targetnode a' = n')"
          hence "targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                distance (targetnode a') m x \<and>
                                                valid_edge a' \<and> targetnode a' = n')"
            by simp
          with ex1 target \<open>sourcenode a = sourcenode a'\<close> 
            \<open>valid_edge a\<close> \<open>valid_edge a'\<close> 
            \<open>distance (targetnode a) m x\<close> \<open>distance (sourcenode a) m (x + 1)\<close>
          have "a = a'" by auto
          with \<open>targetnode a \<noteq> targetnode a'\<close> show False by simp
        qed
        with \<open>sourcenode a \<notin> backward_slice S\<close> 
          \<open>kind a' = (Q')\<^sub>\<surd>\<close> \<open>m \<in> obs (sourcenode a) (backward_slice S)\<close>
          \<open>distance (targetnode a) m x\<close> \<open>distance (sourcenode a) m (x + 1)\<close>
          True \<open>sourcenode a = sourcenode a'\<close> show ?thesis
          by(fastforce intro:slice_kind_Pred_obs_nearer_not_SOME)
      qed
    qed
  qed
qed


lemma slice_deterministic:
  assumes "valid_edge a" and "valid_edge a'"
  and "sourcenode a = sourcenode a'" and "targetnode a \<noteq> targetnode a'"
  obtains Q Q' where "slice_kind S a = (Q)\<^sub>\<surd>" and "slice_kind S a' = (Q')\<^sub>\<surd>"
  and "\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
proof(atomize_elim)
  from assms obtain Q Q' 
    where "kind a = (Q)\<^sub>\<surd>" and "kind a' = (Q')\<^sub>\<surd>" 
    and det:"\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
    by(auto dest:deterministic)
  from \<open>valid_edge a\<close> have ex1:"\<exists>!a'. sourcenode a = sourcenode a' \<and> valid_edge a' \<and>
               targetnode a' = (SOME n'. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                              valid_edge a' \<and> targetnode a' = n')"
    by(rule only_one_SOME_edge)
  show "\<exists>Q Q'. slice_kind S a = (Q)\<^sub>\<surd> \<and> slice_kind S a' = (Q')\<^sub>\<surd> \<and> 
                (\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s))"
  proof(cases "sourcenode a \<in> backward_slice S")
    case True
    with \<open>kind a = (Q)\<^sub>\<surd>\<close> have "slice_kind S a = (Q)\<^sub>\<surd>"
      by(simp add:slice_kind_def Let_def)
    from True \<open>kind a' = (Q')\<^sub>\<surd>\<close> \<open>sourcenode a = sourcenode a'\<close>
    have "slice_kind S a' = (Q')\<^sub>\<surd>"
      by(simp add:slice_kind_def Let_def)
    with \<open>slice_kind S a = (Q)\<^sub>\<surd>\<close> det show ?thesis by blast
  next
    case False
    with \<open>kind a = (Q)\<^sub>\<surd>\<close> 
    have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd> \<or> slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
      by(simp add:slice_kind_def Let_def)
    thus ?thesis
    proof
      assume true:"slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
      with \<open>sourcenode a = sourcenode a'\<close> \<open>targetnode a \<noteq> targetnode a'\<close>
        \<open>valid_edge a\<close> \<open>valid_edge a'\<close>
      have "slice_kind S a' = (\<lambda>s. False)\<^sub>\<surd>"
        by(rule slice_kind_only_one_True_edge)
      with true show ?thesis by simp
    next
      assume false:"slice_kind S a = (\<lambda>s. False)\<^sub>\<surd>"
      from False \<open>kind a' = (Q')\<^sub>\<surd>\<close> \<open>sourcenode a = sourcenode a'\<close>
      have "slice_kind S a' = (\<lambda>s. True)\<^sub>\<surd> \<or> slice_kind S a' = (\<lambda>s. False)\<^sub>\<surd>"
        by(simp add:slice_kind_def Let_def)
      with false show ?thesis by auto
    qed
  qed
qed




subsection \<open>Observable and silent moves\<close>

inductive silent_move :: 
  "'node set \<Rightarrow> ('edge \<Rightarrow> 'state edge_kind) \<Rightarrow> 'node \<Rightarrow> 'state \<Rightarrow> 'edge \<Rightarrow> 
  'node \<Rightarrow> 'state \<Rightarrow> bool" ("_,_ \<turnstile> '(_,_') -_\<rightarrow>\<^sub>\<tau> '(_,_')" [51,50,0,0,50,0,0] 51) 
 
  where silent_moveI:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; sourcenode a \<notin> backward_slice S; 
    valid_edge a\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (sourcenode a,s) -a\<rightarrow>\<^sub>\<tau> (targetnode a,s')"


inductive silent_moves :: 
  "'node set \<Rightarrow> ('edge \<Rightarrow> 'state edge_kind) \<Rightarrow> 'node \<Rightarrow> 'state \<Rightarrow> 'edge list \<Rightarrow> 
  'node \<Rightarrow> 'state \<Rightarrow> bool" ("_,_ \<turnstile> '(_,_') =_\<Rightarrow>\<^sub>\<tau> '(_,_')" [51,50,0,0,50,0,0] 51)

  where silent_moves_Nil: "S,f \<turnstile> (n,s) =[]\<Rightarrow>\<^sub>\<tau> (n,s)"

  | silent_moves_Cons:
  "\<lbrakk>S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n',s'); S,f \<turnstile> (n',s') =as\<Rightarrow>\<^sub>\<tau> (n'',s'')\<rbrakk> 
  \<Longrightarrow> S,f \<turnstile> (n,s) =a#as\<Rightarrow>\<^sub>\<tau> (n'',s'')"


lemma silent_moves_obs_slice:
  "\<lbrakk>S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s'); nx \<in> obs n' (backward_slice S)\<rbrakk>
  \<Longrightarrow> nx \<in> obs n (backward_slice S)"
proof(induct rule:silent_moves.induct)
  case silent_moves_Nil thus ?case by simp
next
  case (silent_moves_Cons S f n s a n' s' as n'' s'')
  from \<open>nx \<in> obs n'' (backward_slice S)\<close>
    \<open>nx \<in> obs n'' (backward_slice S) \<Longrightarrow> nx \<in> obs n' (backward_slice S)\<close>
  have obs:"nx \<in> obs n' (backward_slice S)" by simp
  from \<open>S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n',s')\<close>
  have "n = sourcenode a" and "n' = targetnode a" and "valid_edge a" 
    and "n \<notin> (backward_slice S)"
    by(auto elim:silent_move.cases)
  hence "obs n' (backward_slice S) \<subseteq> obs n (backward_slice S)"
    by simp(rule edge_obs_subset,simp+)
  with obs show ?case by blast
qed


lemma silent_moves_preds_transfers_path:
  "\<lbrakk>S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s'); valid_node n\<rbrakk> 
  \<Longrightarrow> preds (map f as) s \<and> transfers (map f as) s = s' \<and> n -as\<rightarrow>* n'"
proof(induct rule:silent_moves.induct)
  case silent_moves_Nil thus ?case by(simp add:path.empty_path)
next
  case (silent_moves_Cons S f n s a n' s' as n'' s'')
  note IH = \<open>valid_node n' \<Longrightarrow>
    preds (map f as) s' \<and> transfers (map f as) s' = s'' \<and> n' -as\<rightarrow>* n''\<close>
  from \<open>S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n',s')\<close> have "pred (f a) s" and "transfer (f a) s = s'"
    and "n = sourcenode a" and "n' = targetnode a" and "valid_edge a"
    by(auto elim:silent_move.cases)
  from \<open>n' = targetnode a\<close> \<open>valid_edge a\<close> have "valid_node n'" by simp
  from IH[OF this] have "preds (map f as) s'" and "transfers (map f as) s' = s''"
    and "n' -as\<rightarrow>* n''" by simp_all
  from \<open>n = sourcenode a\<close> \<open>n' = targetnode a\<close> \<open>valid_edge a\<close> \<open>n' -as\<rightarrow>* n''\<close>
  have "n -a#as\<rightarrow>* n''" by(fastforce intro:Cons_path)
  with \<open>pred (f a) s\<close> \<open>preds (map f as) s'\<close> \<open>transfer (f a) s = s'\<close> 
    \<open>transfers (map f as) s' = s''\<close> show ?case by simp
qed


lemma obs_silent_moves:
  assumes "obs n (backward_slice S) = {n'}"
  obtains as where "S,slice_kind S \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s)"
proof(atomize_elim)
  from \<open>obs n (backward_slice S) = {n'}\<close> 
  have "n' \<in> obs n (backward_slice S)" by simp
  then obtain as where "n -as\<rightarrow>* n'" 
    and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> (backward_slice S)"
    and "n' \<in> (backward_slice S)" by(erule obsE)
  from \<open>n -as\<rightarrow>* n'\<close> obtain x where "distance n n' x" and "x \<le> length as"
    by(erule every_path_distance)
  from \<open>distance n n' x\<close> \<open>n' \<in> obs n (backward_slice S)\<close> 
  show "\<exists>as. S,slice_kind S \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s)"
  proof(induct x arbitrary:n s rule:nat.induct)
    fix n s assume "distance n n' 0"
    then obtain as' where "n -as'\<rightarrow>* n'" and "length as' = 0"
      by(auto elim:distance.cases)
    hence "n -[]\<rightarrow>* n'" by(cases as) auto
    hence "n = n'" by(fastforce elim:path.cases)
    hence "S,slice_kind S \<turnstile> (n,s) =[]\<Rightarrow>\<^sub>\<tau> (n',s)" by(fastforce intro:silent_moves_Nil)
    thus "\<exists>as. S,slice_kind S \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s)" by blast
  next
    fix x n s 
    assume "distance n n' (Suc x)" and "n' \<in> obs n (backward_slice S)"
      and IH:"\<And>n s. \<lbrakk>distance n n' x; n' \<in> obs n (backward_slice S)\<rbrakk> 
              \<Longrightarrow> \<exists>as. S,slice_kind S \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s)"
    from \<open>n' \<in> obs n (backward_slice S)\<close>
    have "valid_node n" by(rule in_obs_valid)
    with \<open>distance n n' (Suc x)\<close>
    have "n \<noteq> n'" by(fastforce elim:distance.cases dest:empty_path)
    have "n \<notin> backward_slice S"
    proof
      assume isin:"n \<in> backward_slice S"
      with \<open>valid_node n\<close> have "obs n (backward_slice S) = {n}"
        by(fastforce intro!:n_in_obs)
      with \<open>n' \<in> obs n (backward_slice S)\<close> \<open>n \<noteq> n'\<close> show False by simp
    qed
    from \<open>distance n n' (Suc x)\<close> obtain a where "valid_edge a" 
      and "n = sourcenode a" and "distance (targetnode a) n' x"
      and target:"targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                     distance (targetnode a') n' x \<and>
                                     valid_edge a' \<and> targetnode a' = nx)"
      by -(erule distance_successor_distance,simp+)
    from \<open>n' \<in> obs n (backward_slice S)\<close>
    have "obs n (backward_slice S) = {n'}"
      by(rule obs_singleton_element)
    with \<open>valid_edge a\<close> \<open>n \<notin> backward_slice S\<close> \<open>n = sourcenode a\<close>
    have disj:"obs (targetnode a) (backward_slice S) = {} \<or> 
               obs (targetnode a) (backward_slice S) = {n'}"
      by -(drule_tac S="backward_slice S" in edge_obs_subset,auto)
    from \<open>distance (targetnode a) n' x\<close> obtain asx where "targetnode a -asx\<rightarrow>* n'" 
      and "length asx = x" and "\<forall>as'. targetnode a -as'\<rightarrow>* n' \<longrightarrow> x \<le> length as'" 
      by(auto elim:distance.cases)
    from \<open>targetnode a -asx\<rightarrow>* n'\<close> \<open>n' \<in> (backward_slice S)\<close>
    obtain m where "\<exists>m. m \<in> obs (targetnode a) (backward_slice S)"
      by(fastforce elim:path_ex_obs)
    with disj have "n' \<in> obs (targetnode a) (backward_slice S)" by fastforce
    from IH[OF \<open>distance (targetnode a) n' x\<close> this,of "transfer (slice_kind S a) s"]
    obtain asx' where 
    moves:"S,slice_kind S \<turnstile> (targetnode a,transfer (slice_kind S a) s) =asx'\<Rightarrow>\<^sub>\<tau> 
                               (n',transfer (slice_kind S a) s)" by blast
    have "pred (slice_kind S a) s \<and> transfer (slice_kind S a) s = s"
    proof(cases "kind a")
      case (Update f)
      with \<open>n \<notin> backward_slice S\<close> \<open>n = sourcenode a\<close> have "slice_kind S a = \<Up>id" 
        by(fastforce intro:slice_kind_Upd)
      thus ?thesis by simp
    next
      case (Predicate Q)
      with \<open>n \<notin> backward_slice S\<close> \<open>n = sourcenode a\<close>
        \<open>n' \<in> obs n (backward_slice S)\<close> \<open>distance (targetnode a) n' x\<close>
        \<open>distance n n' (Suc x)\<close> target
      have "slice_kind S a =  (\<lambda>s. True)\<^sub>\<surd>"
        by(fastforce intro:slice_kind_Pred_obs_nearer_SOME)
      thus ?thesis by simp
    qed
    hence "pred (slice_kind S a) s" and "transfer (slice_kind S a) s = s"
      by simp_all
    with \<open>n \<notin> backward_slice S\<close> \<open>n = sourcenode a\<close> \<open>valid_edge a\<close>
    have "S,slice_kind S \<turnstile> (sourcenode a,s) -a\<rightarrow>\<^sub>\<tau> 
                             (targetnode a,transfer (slice_kind S a) s)"
      by(fastforce intro:silent_moveI)
    with moves \<open>transfer (slice_kind S a) s = s\<close> \<open>n = sourcenode a\<close>
    have "S,slice_kind S \<turnstile> (n,s) =a#asx'\<Rightarrow>\<^sub>\<tau> (n',s)"
      by(fastforce intro:silent_moves_Cons)
    thus "\<exists>as. S,slice_kind S \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s)" by blast
  qed
qed


inductive observable_move ::
  "'node set \<Rightarrow> ('edge \<Rightarrow> 'state edge_kind) \<Rightarrow> 'node \<Rightarrow> 'state \<Rightarrow> 'edge \<Rightarrow> 
  'node \<Rightarrow> 'state \<Rightarrow> bool" ("_,_ \<turnstile> '(_,_') -_\<rightarrow> '(_,_')" [51,50,0,0,50,0,0] 51) 
 
  where observable_moveI:
  "\<lbrakk>pred (f a) s; transfer (f a) s = s'; sourcenode a \<in> backward_slice S; 
    valid_edge a\<rbrakk>  
  \<Longrightarrow> S,f \<turnstile> (sourcenode a,s) -a\<rightarrow> (targetnode a,s')"


inductive observable_moves :: 
  "'node set \<Rightarrow> ('edge \<Rightarrow> 'state edge_kind) \<Rightarrow> 'node \<Rightarrow> 'state \<Rightarrow> 'edge list \<Rightarrow> 
  'node \<Rightarrow> 'state \<Rightarrow> bool" ("_,_ \<turnstile> '(_,_') =_\<Rightarrow> '(_,_')" [51,50,0,0,50,0,0] 51) 

  where observable_moves_snoc:
  "\<lbrakk>S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s'); S,f \<turnstile> (n',s') -a\<rightarrow> (n'',s'')\<rbrakk> 
  \<Longrightarrow> S,f \<turnstile> (n,s) =as@[a]\<Rightarrow> (n'',s'')"


lemma observable_move_notempty:
  "\<lbrakk>S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s'); as = []\<rbrakk> \<Longrightarrow> False"
by(induct rule:observable_moves.induct,simp)


lemma silent_move_observable_moves:
  "\<lbrakk>S,f \<turnstile> (n'',s'') =as\<Rightarrow> (n',s'); S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n'',s'')\<rbrakk>
  \<Longrightarrow> S,f \<turnstile> (n,s) =a#as\<Rightarrow> (n',s')"
proof(induct rule:observable_moves.induct)
  case (observable_moves_snoc S f nx sx as n' s' a' n'' s'')
  from \<open>S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (nx,sx)\<close> \<open>S,f \<turnstile> (nx,sx) =as\<Rightarrow>\<^sub>\<tau> (n',s')\<close>
  have "S,f \<turnstile> (n,s) =a#as\<Rightarrow>\<^sub>\<tau> (n',s')" by(rule silent_moves_Cons)
  with \<open>S,f \<turnstile> (n',s') -a'\<rightarrow> (n'',s'')\<close>
  have "S,f \<turnstile> (n,s) =(a#as)@[a']\<Rightarrow> (n'',s'')"
    by -(rule observable_moves.observable_moves_snoc)
  thus ?case by simp
qed


lemma observable_moves_preds_transfers_path:
  "S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s')
  \<Longrightarrow> preds (map f as) s \<and> transfers (map f as) s = s' \<and> n -as\<rightarrow>* n'"
proof(induct rule:observable_moves.induct)
  case (observable_moves_snoc S f n s as n' s' a n'' s'')
  have "valid_node n"
  proof(cases as)
    case Nil
    with \<open>S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s')\<close> have "n = n'" and "s = s'"
      by(auto elim:silent_moves.cases)
    with \<open>S,f \<turnstile> (n',s') -a\<rightarrow> (n'',s'')\<close> show ?thesis
      by(fastforce elim:observable_move.cases)
  next
    case (Cons a' as')
    with \<open>S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s')\<close> show ?thesis
      by(fastforce elim:silent_moves.cases silent_move.cases)
  qed
  with \<open>S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s')\<close>
  have "preds (map f as) s" and "transfers (map f as) s = s'"
    and "n -as\<rightarrow>* n'" by(auto dest:silent_moves_preds_transfers_path)
  from \<open>S,f \<turnstile> (n',s') -a\<rightarrow> (n'',s'')\<close> have "pred (f a) s'" 
    and "transfer (f a) s' = s''" and "n' = sourcenode a" and "n'' = targetnode a" 
    and "valid_edge a"
    by(auto elim:observable_move.cases)
  from \<open>n' = sourcenode a\<close> \<open>n'' = targetnode a\<close> \<open>valid_edge a\<close>
  have "n' -[a]\<rightarrow>* n''" by(fastforce intro:path.intros)
  with \<open>n -as\<rightarrow>* n'\<close> have "n -as@[a]\<rightarrow>* n''" by(rule path_Append)
  with \<open>preds (map f as) s\<close> \<open>pred (f a) s'\<close> \<open>transfer (f a) s' = s''\<close>
    \<open>transfers (map f as) s = s'\<close>
  show ?case by(simp add:transfers_split preds_split)
qed




subsection \<open>Relevant variables\<close>

inductive_set relevant_vars :: "'node set \<Rightarrow> 'node \<Rightarrow> 'var set" ("rv _")
for S :: "'node set" and n :: "'node"

where rvI:
  "\<lbrakk>n -as\<rightarrow>* n'; n' \<in> backward_slice S; V \<in> Use n';
    \<forall>nx \<in> set(sourcenodes as). V \<notin> Def nx\<rbrakk>
  \<Longrightarrow> V \<in> rv S n"


lemma rvE:
  assumes rv:"V \<in> rv S n"
  obtains as n' where "n -as\<rightarrow>* n'" and "n' \<in> backward_slice S" and "V \<in> Use n'"
  and "\<forall>nx \<in> set(sourcenodes as). V \<notin> Def nx"
using rv
by(atomize_elim,auto elim!:relevant_vars.cases)



lemma eq_obs_in_rv:
  assumes obs_eq:"obs n (backward_slice S) = obs n' (backward_slice S)" 
  and "x \<in> rv S n" shows "x \<in> rv S n'"
proof -
  from \<open>x \<in> rv S n\<close> obtain as m 
    where "n -as\<rightarrow>* m" and "m \<in> backward_slice S" and "x \<in> Use m"
    and "\<forall>nx\<in>set (sourcenodes as). x \<notin> Def nx"
    by(erule rvE)
  from \<open>n -as\<rightarrow>* m\<close> have "valid_node m" by(fastforce dest:path_valid_node)
  from \<open>n -as\<rightarrow>* m\<close> \<open>m \<in> backward_slice S\<close> 
  have "\<exists>nx as' as''. nx \<in> obs n (backward_slice S) \<and> n -as'\<rightarrow>* nx \<and> 
                                     nx -as''\<rightarrow>* m \<and> as = as'@as''"
  proof(cases "\<forall>nx \<in> set(sourcenodes as). nx \<notin> backward_slice S")
    case True
    with \<open>n -as\<rightarrow>* m\<close> \<open>m \<in> backward_slice S\<close> have "m \<in> obs n (backward_slice S)"
      by -(rule obs_elem)
    with \<open>n -as\<rightarrow>* m\<close> \<open>valid_node m\<close> show ?thesis by(blast intro:empty_path)
  next
    case False
    hence "\<exists>nx \<in> set(sourcenodes as). nx \<in> backward_slice S" by simp
    then obtain nx' ns ns' where "sourcenodes as = ns@nx'#ns'"
      and "nx' \<in> backward_slice S" 
      and "\<forall>x \<in> set ns. x \<notin> backward_slice S"
      by(fastforce elim!:split_list_first_propE)
    from \<open>sourcenodes as = ns@nx'#ns'\<close>
    obtain as' a' as'' where "ns = sourcenodes as'"
      and "as = as'@a'#as''" and "sourcenode a' = nx'"
      by(fastforce elim:map_append_append_maps simp:sourcenodes_def)
    from \<open>n -as\<rightarrow>* m\<close> \<open>as = as'@a'#as''\<close> \<open>sourcenode a' = nx'\<close>
    have "n -as'\<rightarrow>* nx'" and "valid_edge a'" and "targetnode a' -as''\<rightarrow>* m"
      by(fastforce dest:path_split)+
    with \<open>sourcenode a' = nx'\<close> have "nx' -a'#as''\<rightarrow>* m" by(fastforce intro:Cons_path)
    from \<open>n -as'\<rightarrow>* nx'\<close> \<open>nx' \<in> backward_slice S\<close>
      \<open>\<forall>x \<in> set ns. x \<notin> backward_slice S\<close> \<open>ns = sourcenodes as'\<close> 
    have "nx' \<in> obs n (backward_slice S)" 
      by(fastforce intro:obs_elem)
    with \<open>n -as'\<rightarrow>* nx'\<close> \<open>nx' -a'#as''\<rightarrow>* m\<close> \<open>as = as'@a'#as''\<close> show ?thesis by blast
  qed
  then obtain nx as' as'' where "nx \<in> obs n (backward_slice S)"
    and "n -as'\<rightarrow>* nx" and "nx -as''\<rightarrow>* m" and "as = as'@as''"
    by blast
  from \<open>nx \<in> obs n (backward_slice S)\<close> obs_eq 
  have "nx \<in> obs n' (backward_slice S)" by auto
  then obtain asx where "n' -asx\<rightarrow>* nx" 
    and "\<forall>ni \<in> set(sourcenodes asx). ni \<notin> backward_slice S" 
    and "nx \<in> backward_slice S"
    by(erule obsE)
  from \<open>as = as'@as''\<close> \<open>\<forall>nx\<in>set (sourcenodes as). x \<notin> Def nx\<close> 
  have "\<forall>ni\<in>set (sourcenodes as''). x \<notin> Def ni"
    by(auto simp:sourcenodes_def)
  from \<open>\<forall>ni \<in> set(sourcenodes asx). ni \<notin> backward_slice S\<close> \<open>n' -asx\<rightarrow>* nx\<close>
  have "\<forall>ni \<in> set(sourcenodes asx). x \<notin> Def ni"
  proof(induct asx arbitrary:n')
    case Nil thus ?case by(simp add:sourcenodes_def)
  next
    case (Cons ax' asx')
    note IH = \<open>\<And>n'. \<lbrakk>\<forall>ni\<in>set (sourcenodes asx'). ni \<notin> backward_slice S; 
      n' -asx'\<rightarrow>* nx\<rbrakk> 
        \<Longrightarrow> \<forall>ni\<in>set (sourcenodes asx'). x \<notin> Def ni\<close>
    from \<open>n' -ax'#asx'\<rightarrow>* nx\<close> have "n' -[]@ax'#asx'\<rightarrow>* nx" by simp
    hence "targetnode ax' -asx'\<rightarrow>* nx" and "n' = sourcenode ax'"
      by(fastforce dest:path_split)+
    from \<open>\<forall>ni\<in>set (sourcenodes (ax'#asx')). ni \<notin> backward_slice S\<close>
    have all:"\<forall>ni\<in>set (sourcenodes asx'). ni \<notin> backward_slice S" 
      and "sourcenode ax' \<notin> backward_slice S"
      by(auto simp:sourcenodes_def)
    from IH[OF all \<open>targetnode ax' -asx'\<rightarrow>* nx\<close>]
    have "\<forall>ni\<in>set (sourcenodes asx'). x \<notin> Def ni" .
    with \<open>\<forall>ni\<in>set (sourcenodes as''). x \<notin> Def ni\<close>
    have "\<forall>ni\<in>set (sourcenodes (asx'@as'')). x \<notin> Def ni"
      by(auto simp:sourcenodes_def)
    from \<open>n' -ax'#asx'\<rightarrow>* nx\<close> \<open>nx -as''\<rightarrow>* m\<close> have "n' -(ax'#asx')@as''\<rightarrow>* m" 
      by-(rule path_Append)
    hence "n' -ax'#asx'@as''\<rightarrow>* m" by simp
    have "x \<notin> Def (sourcenode ax')"
    proof
      assume "x \<in> Def (sourcenode ax')"
      with \<open>x \<in> Use m\<close> \<open>\<forall>ni\<in>set (sourcenodes (asx'@as'')). x \<notin> Def ni\<close>
        \<open>n' -ax'#asx'@as''\<rightarrow>* m\<close> \<open>n' = sourcenode ax'\<close> 
      have "n' influences x in m"
        by(auto simp:data_dependence_def)
      with \<open>m \<in> backward_slice S\<close> dd_closed have "n' \<in> backward_slice S" 
        by(auto simp:dd_closed)
      with \<open>n' = sourcenode ax'\<close> \<open>sourcenode ax' \<notin> backward_slice S\<close>
      show False by simp
    qed
    with \<open>\<forall>ni\<in>set (sourcenodes (asx'@as'')). x \<notin> Def ni\<close>
    show ?case by(simp add:sourcenodes_def)
  qed
  with \<open>\<forall>ni\<in>set (sourcenodes as''). x \<notin> Def ni\<close> 
  have "\<forall>ni\<in>set (sourcenodes (asx@as'')). x \<notin> Def ni"
    by(auto simp:sourcenodes_def)
  from \<open>n' -asx\<rightarrow>* nx\<close> \<open>nx -as''\<rightarrow>* m\<close> have "n' -asx@as''\<rightarrow>* m" by(rule path_Append)
  with \<open>m \<in> backward_slice S\<close> \<open>x \<in> Use m\<close> 
    \<open>\<forall>ni\<in>set (sourcenodes (asx@as'')). x \<notin> Def ni\<close> show "x \<in> rv S n'" by -(rule rvI)
qed


lemma closed_eq_obs_eq_rvs:
  fixes S :: "'node set"
  assumes "valid_node n" and "valid_node n'"
  and obs_eq:"obs n (backward_slice S) = obs n' (backward_slice S)"
  shows "rv S n = rv S n'"
proof
  show "rv S n \<subseteq> rv S n'"
  proof
    fix x assume "x \<in> rv S n"
    with \<open>valid_node n\<close> obs_eq show "x \<in> rv S n'" by -(rule eq_obs_in_rv)
  qed
next
  show "rv S n' \<subseteq> rv S n"
  proof
    fix x assume "x \<in> rv S n'"
    with \<open>valid_node n'\<close> obs_eq[THEN sym] show "x \<in> rv S n" by -(rule eq_obs_in_rv)
  qed
qed


lemma rv_edge_slice_kinds:
  assumes "valid_edge a" and "sourcenode a = n" and "targetnode a = n''"
  and "\<forall>V\<in>rv S n. state_val s V = state_val s' V"
  and "preds (slice_kinds S (a#as)) s" and "preds (slice_kinds S (a#asx)) s'"
  shows "\<forall>V\<in>rv S n''. state_val (transfer (slice_kind S a) s) V =
                       state_val (transfer (slice_kind S a) s') V"
proof
  fix V assume "V \<in> rv S n''"
  show "state_val (transfer (slice_kind S a) s) V =
    state_val (transfer (slice_kind S a) s') V"
  proof(cases "V \<in> Def n")
    case True
    show ?thesis
    proof(cases "sourcenode a \<in> backward_slice S")
      case True
      hence "slice_kind S a = kind a" by(rule slice_kind_in_slice)
      with \<open>preds (slice_kinds S (a#as)) s\<close> have "pred (kind a) s"
        by(simp add:slice_kinds_def)
      from \<open>slice_kind S a = kind a\<close> \<open>preds (slice_kinds S (a#asx)) s'\<close>
      have "pred (kind a) s'"
        by(simp add:slice_kinds_def)
      from \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> have "n -[]\<rightarrow>* n"
        by(fastforce intro:empty_path)
      with True \<open>sourcenode a = n\<close> have "\<forall>V \<in> Use n. V \<in> rv S n"
        by(fastforce intro:rvI simp:sourcenodes_def)
      with \<open>\<forall>V\<in>rv S n. state_val s V = state_val s' V\<close> \<open>sourcenode a = n\<close>
      have "\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V" by blast
      from \<open>valid_edge a\<close> this \<open>pred (kind a) s\<close> \<open>pred (kind a) s'\<close>
      have "\<forall>V \<in> Def (sourcenode a). state_val (transfer (kind a) s) V =
        state_val (transfer (kind a) s') V"
        by(rule CFG_edge_transfer_uses_only_Use)
      with \<open>V \<in> Def n\<close> \<open>sourcenode a = n\<close> \<open>slice_kind S a = kind a\<close>
      show ?thesis by simp
    next
      case False
      from \<open>V \<in> rv S n''\<close> obtain xs nx where "n'' -xs\<rightarrow>* nx"
        and "nx \<in> backward_slice S" and "V \<in> Use nx"
        and "\<forall>nx' \<in> set(sourcenodes xs). V \<notin> Def nx'" by(erule rvE)
      from \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>targetnode a = n''\<close> 
        \<open>n'' -xs\<rightarrow>* nx\<close>
      have "n -a#xs\<rightarrow>* nx" by -(rule path.Cons_path)
      with \<open>V \<in> Def n\<close> \<open>V \<in> Use nx\<close> \<open>\<forall>nx' \<in> set(sourcenodes xs). V \<notin> Def nx'\<close>
      have "n influences V in nx" by(fastforce simp:data_dependence_def)
      with \<open>nx \<in> backward_slice S\<close> have "n \<in> backward_slice S"
        by(rule dd_closed)
      with \<open>sourcenode a = n\<close> False have False by simp
      thus ?thesis by simp
    qed
  next
    case False
    from \<open>V \<in> rv S n''\<close> obtain xs nx where "n'' -xs\<rightarrow>* nx"
      and "nx \<in> backward_slice S" and "V \<in> Use nx"
      and "\<forall>nx' \<in> set(sourcenodes xs). V \<notin> Def nx'" by(erule rvE)
    from \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>targetnode a = n''\<close> \<open>n'' -xs\<rightarrow>* nx\<close>
    have "n -a#xs\<rightarrow>* nx" by -(rule path.Cons_path)
    from False \<open>\<forall>nx' \<in> set(sourcenodes xs). V \<notin> Def nx'\<close> \<open>sourcenode a = n\<close>
    have "\<forall>nx' \<in> set(sourcenodes (a#xs)). V \<notin> Def nx'"
      by(simp add:sourcenodes_def)
    with \<open>n -a#xs\<rightarrow>* nx\<close> \<open>nx \<in> backward_slice S\<close> \<open>V \<in> Use nx\<close>
    have "V \<in> rv S n" by(rule rvI)
    show ?thesis
    proof(cases "kind a")
      case (Predicate Q)
      show ?thesis
      proof(cases "sourcenode a \<in> backward_slice S")
        case True
        with Predicate have "slice_kind S a = (Q)\<^sub>\<surd>"
          by(simp add:slice_kind_in_slice)
        with \<open>\<forall>V\<in>rv S n. state_val s V = state_val s' V\<close> \<open>V \<in> rv S n\<close>
        show ?thesis by simp
      next
        case False
        with Predicate obtain Q' where "slice_kind S a = (Q')\<^sub>\<surd>" 
          by -(erule kind_Predicate_notin_slice_slice_kind_Predicate)
        with \<open>\<forall>V\<in>rv S n. state_val s V = state_val s' V\<close> \<open>V \<in> rv S n\<close>
        show ?thesis by simp
      qed
    next
      case (Update f)
      show ?thesis
      proof(cases "sourcenode a \<in> backward_slice S")
        case True
        hence "slice_kind S a = kind a" by(rule slice_kind_in_slice)
        from Update have "pred (kind a) s" by simp
        with \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>V \<notin> Def n\<close>
        have "state_val (transfer (kind a) s) V = state_val s V"
          by(fastforce intro:CFG_edge_no_Def_equal)
        from Update have "pred (kind a) s'" by simp
        with \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>V \<notin> Def n\<close>
        have "state_val (transfer (kind a) s') V = state_val s' V"
          by(fastforce intro:CFG_edge_no_Def_equal)
        with \<open>\<forall>V\<in>rv S n. state_val s V = state_val s' V\<close> \<open>V \<in> rv S n\<close>
          \<open>state_val (transfer (kind a) s) V = state_val s V\<close>
          \<open>slice_kind S a = kind a\<close>
        show ?thesis by fastforce
      next
        case False
        with Update have "slice_kind S a = \<Up>id" by -(rule slice_kind_Upd)
        with \<open>\<forall>V\<in>rv S n. state_val s V = state_val s' V\<close> \<open>V \<in> rv S n\<close>
        show ?thesis by fastforce
      qed
    qed
  qed
qed



lemma rv_branching_edges_slice_kinds_False:
  assumes "valid_edge a" and "valid_edge ax" 
  and "sourcenode a = n" and "sourcenode ax = n"
  and "targetnode a = n''" and "targetnode ax \<noteq> n''"
  and "preds (slice_kinds S (a#as)) s" and "preds (slice_kinds S (ax#asx)) s'"
  and "\<forall>V\<in>rv S n. state_val s V = state_val s' V"
  shows False
proof -
  from \<open>valid_edge a\<close> \<open>valid_edge ax\<close> \<open>sourcenode a = n\<close> \<open>sourcenode ax = n\<close>
    \<open>targetnode a = n''\<close> \<open>targetnode ax \<noteq> n''\<close>
  obtain Q Q' where "kind a = (Q)\<^sub>\<surd>" and "kind ax = (Q')\<^sub>\<surd>"
    and "\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)"
    by(auto dest:deterministic)
  from \<open>valid_edge a\<close> \<open>valid_edge ax\<close> \<open>sourcenode a = n\<close> \<open>sourcenode ax = n\<close>
    \<open>targetnode a = n''\<close> \<open>targetnode ax \<noteq> n''\<close>
  obtain P P' where "slice_kind S a = (P)\<^sub>\<surd>" 
    and "slice_kind S ax = (P')\<^sub>\<surd>"
    and "\<forall>s. (P s \<longrightarrow> \<not> P' s) \<and> (P' s \<longrightarrow> \<not> P s)"
    by -(erule slice_deterministic,auto)
  show ?thesis
  proof(cases "sourcenode a \<in> backward_slice S")
    case True
    hence "slice_kind S a = kind a" by(rule slice_kind_in_slice)
    with \<open>preds (slice_kinds S (a#as)) s\<close> \<open>kind a = (Q)\<^sub>\<surd>\<close> 
      \<open>slice_kind S a = (P)\<^sub>\<surd>\<close> have "pred (kind a) s"
      by(simp add:slice_kinds_def)
    from True \<open>sourcenode a = n\<close> \<open>sourcenode ax = n\<close>
    have "slice_kind S ax = kind ax" by(fastforce simp:slice_kind_in_slice)
    with \<open>preds (slice_kinds S (ax#asx)) s'\<close> \<open>kind ax = (Q')\<^sub>\<surd>\<close>
      \<open>slice_kind S ax = (P')\<^sub>\<surd>\<close> have "pred (kind ax) s'" 
      by(simp add:slice_kinds_def)
    with \<open>kind ax = (Q')\<^sub>\<surd>\<close> have "Q' s'" by simp
    from \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> have "n -[]\<rightarrow>* n"
      by(fastforce intro:empty_path)
    with True \<open>sourcenode a = n\<close> have "\<forall>V \<in> Use n. V \<in> rv S n"
      by(fastforce intro:rvI simp:sourcenodes_def)
    with \<open>\<forall>V\<in>rv S n. state_val s V = state_val s' V\<close> \<open>sourcenode a = n\<close>
    have "\<forall>V \<in> Use (sourcenode a). state_val s V = state_val s' V" by blast
    with \<open>valid_edge a\<close> \<open>pred (kind a) s\<close> have "pred (kind a) s'"
      by(rule CFG_edge_Uses_pred_equal)
    with \<open>kind a = (Q)\<^sub>\<surd>\<close> have "Q s'" by simp
    with \<open>Q' s'\<close> \<open>\<forall>s. (Q s \<longrightarrow> \<not> Q' s) \<and> (Q' s \<longrightarrow> \<not> Q s)\<close> have False by simp
    thus ?thesis by simp
  next
    case False
    with \<open>kind a = (Q)\<^sub>\<surd>\<close> \<open>slice_kind S a = (P)\<^sub>\<surd>\<close>
    have "P = (\<lambda>s. False) \<or> P = (\<lambda>s. True)"
      by(fastforce elim:kind_Predicate_notin_slice_slice_kind_Predicate)
    with \<open>slice_kind S a = (P)\<^sub>\<surd>\<close> \<open>preds (slice_kinds S (a#as)) s\<close>
    have "P = (\<lambda>s. True)" by(fastforce simp:slice_kinds_def)
    from \<open>kind ax = (Q')\<^sub>\<surd>\<close> \<open>slice_kind S ax = (P')\<^sub>\<surd>\<close> 
      \<open>sourcenode a = n\<close> \<open>sourcenode ax = n\<close> False
    have "P' = (\<lambda>s. False) \<or> P' = (\<lambda>s. True)"
      by(fastforce elim:kind_Predicate_notin_slice_slice_kind_Predicate)
    with \<open>slice_kind S ax = (P')\<^sub>\<surd>\<close> \<open>preds (slice_kinds S (ax#asx)) s'\<close>
    have "P' = (\<lambda>s. True)" by(fastforce simp:slice_kinds_def)
    with \<open>P = (\<lambda>s. True)\<close> \<open>\<forall>s. (P s \<longrightarrow> \<not> P' s) \<and> (P' s \<longrightarrow> \<not> P s)\<close>
    have False by blast
    thus ?thesis by simp
  qed
qed



subsection \<open>The set \<open>WS\<close>\<close>

inductive_set WS :: "'node set \<Rightarrow> (('node \<times> 'state) \<times> ('node \<times> 'state)) set"
for S :: "'node set"
where WSI:"\<lbrakk>obs n (backward_slice S) = obs n' (backward_slice S); 
            \<forall>V \<in> rv S n. state_val s V = state_val s' V;
            valid_node n; valid_node n'\<rbrakk>
  \<Longrightarrow> ((n,s),(n',s')) \<in> WS S"


lemma WSD:
  "((n,s),(n',s')) \<in> WS S 
  \<Longrightarrow> obs n (backward_slice S) = obs n' (backward_slice S) \<and> 
      (\<forall>V \<in> rv S n. state_val s V = state_val s' V) \<and>
      valid_node n \<and> valid_node n'"
by(auto elim:WS.cases)


lemma WS_silent_move:
  assumes "((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S" and "S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (n\<^sub>1',s\<^sub>1')"
  and "obs n\<^sub>1' (backward_slice S) \<noteq> {}" shows "((n\<^sub>1',s\<^sub>1'),(n\<^sub>2,s\<^sub>2)) \<in> WS S"
proof -
  from \<open>((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S\<close> have "valid_node n\<^sub>1" and "valid_node n\<^sub>2"
    by(auto dest:WSD)
  from \<open>S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) -a\<rightarrow>\<^sub>\<tau> (n\<^sub>1',s\<^sub>1')\<close> have "sourcenode a = n\<^sub>1"
    and "targetnode a = n\<^sub>1'" and "transfer (kind a) s\<^sub>1 = s\<^sub>1'"
    and "n\<^sub>1 \<notin> backward_slice S" and "valid_edge a" and "pred (kind a) s\<^sub>1"
    by(auto elim:silent_move.cases)
  from \<open>targetnode a = n\<^sub>1'\<close> \<open>valid_edge a\<close> have "valid_node n\<^sub>1'"
    by(auto simp:valid_node_def)
  have "(\<exists>m. obs n\<^sub>1' (backward_slice S) = {m}) \<or> obs n\<^sub>1' (backward_slice S) = {}"
    by(rule obs_singleton_disj)
  with \<open>obs n\<^sub>1' (backward_slice S) \<noteq> {}\<close> obtain n 
    where "obs n\<^sub>1' (backward_slice S) = {n}" by fastforce
  hence "n \<in> obs n\<^sub>1' (backward_slice S)" by auto
  then obtain as where "n\<^sub>1' -as\<rightarrow>* n" 
    and "\<forall>nx \<in> set(sourcenodes as). nx \<notin> (backward_slice S)" 
    and "n \<in> (backward_slice S)" by(erule obsE)
  from \<open>n\<^sub>1' -as\<rightarrow>* n\<close> \<open>valid_edge a\<close> \<open>sourcenode a = n\<^sub>1\<close> \<open>targetnode a = n\<^sub>1'\<close>
  have "n\<^sub>1 -a#as\<rightarrow>* n" by(rule Cons_path)
  moreover
  from \<open>\<forall>nx \<in> set(sourcenodes as). nx \<notin> (backward_slice S)\<close> \<open>sourcenode a = n\<^sub>1\<close>
    \<open>n\<^sub>1 \<notin> backward_slice S\<close> 
  have "\<forall>nx \<in> set(sourcenodes (a#as)). nx \<notin> (backward_slice S)"
    by(simp add:sourcenodes_def)
  ultimately have "n \<in> obs n\<^sub>1 (backward_slice S)" using \<open>n \<in> (backward_slice S)\<close> 
    by(rule obs_elem)
  hence "obs n\<^sub>1 (backward_slice S) = {n}" by(rule obs_singleton_element)
  with \<open>obs n\<^sub>1' (backward_slice S) = {n}\<close> 
  have "obs n\<^sub>1 (backward_slice S) = obs n\<^sub>1' (backward_slice S)"
    by simp
  with \<open>valid_node n\<^sub>1\<close> \<open>valid_node n\<^sub>1'\<close> have "rv S n\<^sub>1 = rv S n\<^sub>1'"
    by(rule closed_eq_obs_eq_rvs)
  from \<open>n \<in> obs n\<^sub>1 (backward_slice S)\<close> \<open>((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S\<close> 
  have "obs n\<^sub>1 (backward_slice S) = obs n\<^sub>2 (backward_slice S)"
    and "\<forall>V \<in> rv S n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V"
    by(fastforce dest:WSD)+
  from \<open>obs n\<^sub>1 (backward_slice S) = obs n\<^sub>2 (backward_slice S)\<close>
    \<open>obs n\<^sub>1 (backward_slice S) = {n}\<close> \<open>obs n\<^sub>1' (backward_slice S) = {n}\<close> 
  have "obs n\<^sub>1' (backward_slice S) = obs n\<^sub>2 (backward_slice S)" by simp
  have "\<forall>V \<in> rv S n\<^sub>1'. state_val s\<^sub>1' V = state_val s\<^sub>2 V"
  proof
    fix V assume "V \<in> rv S n\<^sub>1'"
    with \<open>rv S n\<^sub>1 = rv S n\<^sub>1'\<close> have "V \<in> rv S n\<^sub>1" by simp
    then obtain as n' where "n\<^sub>1 -as\<rightarrow>* n'" and "n' \<in> (backward_slice S)"
      and "V \<in> Use n'" and "\<forall>nx \<in> set(sourcenodes as). V \<notin> Def nx"
      by(erule rvE)
    with \<open>n\<^sub>1 \<notin> backward_slice S\<close> have "V \<notin> Def n\<^sub>1"
      by(auto elim:path.cases simp:sourcenodes_def)
    with \<open>valid_edge a\<close> \<open>sourcenode a = n\<^sub>1\<close> \<open>pred (kind a) s\<^sub>1\<close>
    have "state_val (transfer (kind a) s\<^sub>1) V = state_val s\<^sub>1 V"
      by(fastforce intro:CFG_edge_no_Def_equal)
    with \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> have "state_val s\<^sub>1' V = state_val s\<^sub>1 V" by simp
    from \<open>V \<in> rv S n\<^sub>1\<close> \<open>\<forall>V \<in> rv S n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V\<close>
    have "state_val s\<^sub>1 V = state_val s\<^sub>2 V" by simp
    with \<open>state_val s\<^sub>1' V = state_val s\<^sub>1 V\<close> 
    show "state_val s\<^sub>1' V = state_val s\<^sub>2 V" by simp
  qed
  with \<open>obs n\<^sub>1' (backward_slice S) = obs n\<^sub>2 (backward_slice S)\<close>
    \<open>valid_node n\<^sub>1'\<close> \<open>valid_node n\<^sub>2\<close> show ?thesis by(fastforce intro:WSI)
qed


lemma WS_silent_moves:
  "\<lbrakk>S,f \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow>\<^sub>\<tau> (n\<^sub>1',s\<^sub>1'); ((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S; f = kind;
    obs n\<^sub>1' (backward_slice S) \<noteq> {}\<rbrakk>
  \<Longrightarrow> ((n\<^sub>1',s\<^sub>1'),(n\<^sub>2,s\<^sub>2)) \<in> WS S"
proof(induct rule:silent_moves.induct)
  case silent_moves_Nil thus ?case by simp
next
  case (silent_moves_Cons S f n s a n' s' as n'' s'')
  note IH = \<open>\<lbrakk>((n',s'),(n\<^sub>2,s\<^sub>2)) \<in> WS S; f = kind; obs n'' (backward_slice S) \<noteq> {}\<rbrakk>
             \<Longrightarrow> ((n'',s''),(n\<^sub>2,s\<^sub>2)) \<in> WS S\<close>
  from \<open>S,f \<turnstile> (n',s') =as\<Rightarrow>\<^sub>\<tau> (n'',s'')\<close> \<open>obs n'' (backward_slice S) \<noteq> {}\<close>
  have "obs n' (backward_slice S) \<noteq> {}" by(fastforce dest:silent_moves_obs_slice)
  with \<open>((n,s),(n\<^sub>2,s\<^sub>2)) \<in> WS S\<close> \<open>S,f \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n',s')\<close> \<open>f = kind\<close>
  have "((n',s'),(n\<^sub>2,s\<^sub>2)) \<in> WS S" by -(rule WS_silent_move,simp+)
  from IH[OF this \<open>f = kind\<close> \<open>obs n'' (backward_slice S) \<noteq> {}\<close>]
  show ?case .
qed



lemma WS_observable_move:
  assumes "((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S" and "S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) -a\<rightarrow> (n\<^sub>1',s\<^sub>1')"
  obtains as where "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S"
  and "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (n\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
proof(atomize_elim)
  from \<open>((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S\<close> have "valid_node n\<^sub>1" by(auto dest:WSD)
  from \<open>S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) -a\<rightarrow> (n\<^sub>1',s\<^sub>1')\<close> have [simp]:"n\<^sub>1 = sourcenode a" 
    and [simp]:"n\<^sub>1' = targetnode a" and "pred (kind a) s\<^sub>1"
    and "transfer (kind a) s\<^sub>1 = s\<^sub>1'" and "n\<^sub>1 \<in> (backward_slice S)" 
    and "valid_edge a" and "pred (kind a) s\<^sub>1"
    by(auto elim:observable_move.cases)
  from  \<open>valid_edge a\<close> have "valid_node n\<^sub>1'" by(auto simp:valid_node_def)
  from \<open>valid_node n\<^sub>1\<close> \<open>n\<^sub>1 \<in> (backward_slice S)\<close> 
  have "obs n\<^sub>1 (backward_slice S) = {n\<^sub>1}" by(rule n_in_obs)
  with \<open>((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S\<close> have "obs n\<^sub>2 (backward_slice S) = {n\<^sub>1}" 
    and "\<forall>V \<in> rv S n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V" by(auto dest:WSD)
  from \<open>valid_node n\<^sub>1\<close> have "n\<^sub>1 -[]\<rightarrow>* n\<^sub>1" by(rule empty_path)
  with \<open>n\<^sub>1 \<in> (backward_slice S)\<close> have "\<forall>V \<in> Use n\<^sub>1. V \<in> rv S n\<^sub>1"
    by(fastforce intro:rvI simp:sourcenodes_def)
  with \<open>\<forall>V \<in> rv S n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V\<close>
  have "\<forall>V \<in> Use n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V" by blast
  with \<open>valid_edge a\<close>  \<open>pred (kind a) s\<^sub>1\<close> have "pred (kind a) s\<^sub>2"
    by(fastforce intro:CFG_edge_Uses_pred_equal)
  with \<open>n\<^sub>1 \<in> (backward_slice S)\<close> have "pred (slice_kind S a) s\<^sub>2"
    by(simp add:slice_kind_in_slice)
  from \<open>n\<^sub>1 \<in> (backward_slice S)\<close> obtain s\<^sub>2' 
    where "transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'"
    by(simp add:slice_kind_in_slice)
  with \<open>pred (slice_kind S a) s\<^sub>2\<close> \<open>n\<^sub>1 \<in> (backward_slice S)\<close> \<open>valid_edge a\<close> 
  have "S,slice_kind S \<turnstile> (n\<^sub>1,s\<^sub>2) -a\<rightarrow> (n\<^sub>1',s\<^sub>2')"
    by(fastforce intro:observable_moveI)
  from \<open>obs n\<^sub>2 (backward_slice S) = {n\<^sub>1}\<close>
  obtain as where "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as\<Rightarrow>\<^sub>\<tau> (n\<^sub>1,s\<^sub>2)"
    by(erule obs_silent_moves)
  with \<open>S,slice_kind S \<turnstile> (n\<^sub>1,s\<^sub>2) -a\<rightarrow> (n\<^sub>1',s\<^sub>2')\<close> 
  have "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (n\<^sub>1',s\<^sub>2')"
    by -(rule observable_moves_snoc)
  have "\<forall>V \<in> rv S n\<^sub>1'. state_val s\<^sub>1' V = state_val s\<^sub>2' V"
  proof
    fix V assume rv:"V \<in> rv S n\<^sub>1'"
    show "state_val s\<^sub>1' V = state_val s\<^sub>2' V"
    proof(cases "V \<in> Def n\<^sub>1")
      case True
      thus ?thesis
      proof(cases "kind a")
        case (Update f)
        with \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> have "s\<^sub>1' = f s\<^sub>1" by simp
        from Update[THEN sym] \<open>n\<^sub>1 \<in> (backward_slice S)\<close> 
        have "slice_kind S a = \<Up>f"
          by(fastforce intro:slice_kind_in_slice)
        with \<open>transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'\<close> have "s\<^sub>2' = f s\<^sub>2" by simp
        from \<open>valid_edge a\<close> \<open>\<forall>V \<in> Use n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V\<close>
          True Update \<open>s\<^sub>1' = f s\<^sub>1\<close> \<open>s\<^sub>2' = f s\<^sub>2\<close> show ?thesis
          by(fastforce dest:CFG_edge_transfer_uses_only_Use)
      next
        case (Predicate Q)
        with \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close> have "s\<^sub>1' = s\<^sub>1" by simp
        from Predicate[THEN sym] \<open>n\<^sub>1 \<in> (backward_slice S)\<close>
        have "slice_kind S a = (Q)\<^sub>\<surd>"
          by(fastforce intro:slice_kind_in_slice)
        with \<open>transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'\<close> have "s\<^sub>2' = s\<^sub>2" by simp
        with \<open>valid_edge a\<close> \<open>\<forall>V \<in> Use n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V\<close> 
          True Predicate \<open>s\<^sub>1' = s\<^sub>1\<close> \<open>pred (kind a) s\<^sub>1\<close> \<open>pred (kind a) s\<^sub>2\<close>
        show ?thesis by(auto dest:CFG_edge_transfer_uses_only_Use)
      qed
    next
      case False
      with \<open>valid_edge a\<close> \<open>transfer (kind a) s\<^sub>1 = s\<^sub>1'\<close>[THEN sym] 
        \<open>pred (kind a) s\<^sub>1\<close> \<open>pred (kind a) s\<^sub>2\<close>
      have "state_val s\<^sub>1' V = state_val s\<^sub>1 V"
        by(fastforce intro:CFG_edge_no_Def_equal)
      have "state_val s\<^sub>2' V = state_val s\<^sub>2 V"
      proof(cases "kind a")
        case (Update f)
        with  \<open>n\<^sub>1 \<in> (backward_slice S)\<close> have "slice_kind S a = kind a"
          by(fastforce intro:slice_kind_in_slice)
        with \<open>valid_edge a\<close> \<open>transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'\<close>[THEN sym] 
          False \<open>pred (kind a) s\<^sub>2\<close>
        show ?thesis by(fastforce intro:CFG_edge_no_Def_equal)
      next
        case (Predicate Q)
        with \<open>transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'\<close> have "s\<^sub>2 = s\<^sub>2'"
          by(cases "slice_kind S a",
            auto split:if_split_asm simp:slice_kind_def Let_def)
        thus ?thesis by simp
      qed
      from rv obtain as' nx where "n\<^sub>1' -as'\<rightarrow>* nx" 
        and "nx \<in> (backward_slice S)"
        and "V \<in> Use nx" and "\<forall>nx \<in> set(sourcenodes as'). V \<notin> Def nx"
        by(erule rvE)
      from \<open>\<forall>nx \<in> set(sourcenodes as'). V \<notin> Def nx\<close> False
      have "\<forall>nx \<in> set(sourcenodes (a#as')). V \<notin> Def nx"
        by(auto simp:sourcenodes_def)
      from  \<open>valid_edge a\<close> \<open>n\<^sub>1' -as'\<rightarrow>* nx\<close> have "n\<^sub>1 -a#as'\<rightarrow>* nx"
        by(fastforce intro:Cons_path)
      with \<open>nx \<in> (backward_slice S)\<close> \<open>V \<in> Use nx\<close> 
        \<open>\<forall>nx \<in> set(sourcenodes (a#as')). V \<notin> Def nx\<close>
      have "V \<in> rv S n\<^sub>1" by -(rule rvI)
      with \<open>\<forall>V \<in> rv S n\<^sub>1. state_val s\<^sub>1 V = state_val s\<^sub>2 V\<close> 
        \<open>state_val s\<^sub>1' V = state_val s\<^sub>1 V\<close> \<open>state_val s\<^sub>2' V = state_val s\<^sub>2 V\<close>
      show ?thesis by fastforce
    qed
  qed
  with \<open>valid_node n\<^sub>1'\<close> have "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',s\<^sub>2')) \<in> WS S" by(fastforce intro:WSI)
  with \<open>S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (n\<^sub>1',s\<^sub>2')\<close>
    \<open>transfer (slice_kind S a) s\<^sub>2 = s\<^sub>2'\<close> 
  show "\<exists>as. ((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfer (slice_kind S a) s\<^sub>2)) \<in> WS S \<and>
    S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as@[a]\<Rightarrow> (n\<^sub>1',transfer (slice_kind S a) s\<^sub>2)"
    by blast
qed



definition is_weak_sim :: 
  "(('node \<times> 'state) \<times> ('node \<times> 'state)) set \<Rightarrow> 'node set \<Rightarrow> bool"
  where "is_weak_sim R S \<equiv> 
  \<forall>n\<^sub>1 s\<^sub>1 n\<^sub>2 s\<^sub>2 n\<^sub>1' s\<^sub>1' as. ((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> R \<and> S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow> (n\<^sub>1',s\<^sub>1')
  \<longrightarrow> (\<exists>n\<^sub>2' s\<^sub>2' as'. ((n\<^sub>1',s\<^sub>1'),(n\<^sub>2',s\<^sub>2')) \<in> R \<and> 
                      S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as'\<Rightarrow> (n\<^sub>2',s\<^sub>2'))"


lemma WS_weak_sim:
  assumes "((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S" 
  and "S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow> (n\<^sub>1',s\<^sub>1')"
  shows "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)) \<in> WS S \<and>
  (\<exists>as'. S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as'@[last as]\<Rightarrow> 
                             (n\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2))"
proof -
  from \<open>S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow> (n\<^sub>1',s\<^sub>1')\<close> obtain a' as' n' s'
    where "S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as'\<Rightarrow>\<^sub>\<tau> (n',s')" 
    and "S,kind \<turnstile> (n',s') -a'\<rightarrow> (n\<^sub>1',s\<^sub>1')" and "as = as'@[a']"
    by(fastforce elim:observable_moves.cases)
  from \<open>S,kind \<turnstile> (n',s') -a'\<rightarrow> (n\<^sub>1',s\<^sub>1')\<close> have "obs n' (backward_slice S) = {n'}"
    by(fastforce elim:observable_move.cases intro!:n_in_obs)
  hence "obs n' (backward_slice S) \<noteq> {}" by fast
  with \<open>S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as'\<Rightarrow>\<^sub>\<tau> (n',s')\<close> \<open>((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S\<close> 
  have "((n',s'),(n\<^sub>2,s\<^sub>2)) \<in> WS S"
    by -(rule WS_silent_moves,simp+)
  with \<open>S,kind \<turnstile> (n',s') -a'\<rightarrow> (n\<^sub>1',s\<^sub>1')\<close> obtain asx 
    where "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfer (slice_kind S a') s\<^sub>2)) \<in> WS S"
    and "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =asx@[a']\<Rightarrow> 
    (n\<^sub>1',transfer (slice_kind S a') s\<^sub>2)"
    by(fastforce elim:WS_observable_move)
  with \<open>as = as'@[a']\<close> show
    "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2)) \<in> WS S \<and>
    (\<exists>as'. S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as'@[last as]\<Rightarrow> 
           (n\<^sub>1',transfer (slice_kind S (last as)) s\<^sub>2))" by simp blast
qed

text \<open>The following lemma states the correctness of static intraprocedural slicing:\\
  the simulation \<open>WS S\<close> is a desired weak simulation\<close>

theorem WS_is_weak_sim:"is_weak_sim (WS S) S"
by(fastforce dest:WS_weak_sim simp:is_weak_sim_def)


subsection \<open>@{term "n -as\<rightarrow>* n'"} and transitive closure of 
  @{term "S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s')"}\<close>

inductive trans_observable_moves :: 
  "'node set \<Rightarrow> ('edge \<Rightarrow> 'state edge_kind) \<Rightarrow> 'node \<Rightarrow> 'state \<Rightarrow> 'edge list \<Rightarrow> 
  'node \<Rightarrow> 'state \<Rightarrow> bool" ("_,_ \<turnstile> '(_,_') =_\<Rightarrow>* '(_,_')" [51,50,0,0,50,0,0] 51) 

where tom_Nil:
  "S,f \<turnstile> (n,s) =[]\<Rightarrow>* (n,s)"

| tom_Cons:
  "\<lbrakk>S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s'); S,f \<turnstile> (n',s') =as'\<Rightarrow>* (n'',s'')\<rbrakk>
  \<Longrightarrow> S,f \<turnstile> (n,s) =(last as)#as'\<Rightarrow>* (n'',s'')"


definition slice_edges :: "'node set \<Rightarrow> 'edge list \<Rightarrow> 'edge list"
  where "slice_edges S as \<equiv> [a \<leftarrow> as. sourcenode a \<in> backward_slice S]"


lemma silent_moves_no_slice_edges:
  "S,f \<turnstile> (n,s) =as\<Rightarrow>\<^sub>\<tau> (n',s') \<Longrightarrow> slice_edges S as = []"
by(induct rule:silent_moves.induct,auto elim:silent_move.cases simp:slice_edges_def)


lemma observable_moves_last_slice_edges:
  "S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s') \<Longrightarrow> slice_edges S as = [last as]"
by(induct rule:observable_moves.induct,
   fastforce dest:silent_moves_no_slice_edges elim:observable_move.cases 
            simp:slice_edges_def)


lemma slice_edges_no_nodes_in_slice:
  "slice_edges S as = [] 
  \<Longrightarrow> \<forall>nx \<in> set(sourcenodes as). nx \<notin> (backward_slice S)"
proof(induct as)
  case Nil thus ?case by(simp add:slice_edges_def sourcenodes_def)
next
  case (Cons a' as')
  note IH = \<open>slice_edges S as' = [] \<Longrightarrow>
    \<forall>nx\<in>set (sourcenodes as'). nx \<notin> backward_slice S\<close>
  from \<open>slice_edges S (a'#as') = []\<close> have "slice_edges S as' = []"
    and "sourcenode a' \<notin> backward_slice S"
    by(auto simp:slice_edges_def split:if_split_asm)
  from IH[OF \<open>slice_edges S as' = []\<close>] \<open>sourcenode a' \<notin> backward_slice S\<close>
  show ?case by(simp add:sourcenodes_def)
qed



lemma sliced_path_determ:
  "\<lbrakk>n -as\<rightarrow>* n'; n -as'\<rightarrow>* n'; slice_edges S as = slice_edges S as';
    preds (slice_kinds S as) s; preds (slice_kinds S as') s'; n' \<in> S;
    \<forall>V \<in> rv S n. state_val s V = state_val s' V\<rbrakk> \<Longrightarrow> as = as'"
proof(induct arbitrary:as' s s' rule:path.induct)
  case (empty_path n)
  from \<open>slice_edges S [] = slice_edges S as'\<close> 
  have "\<forall>nx \<in> set(sourcenodes as'). nx \<notin> (backward_slice S)"
    by(fastforce intro!:slice_edges_no_nodes_in_slice simp:slice_edges_def)
  with \<open>n -as'\<rightarrow>* n\<close> show ?case
  proof(induct nx\<equiv>"n" as' nx'\<equiv>"n" rule:path.induct)
    case (Cons_path n'' as a)
    from \<open>valid_node n\<close> \<open>n \<in> S\<close> have "n \<in> backward_slice S" by(rule refl)
    with \<open>\<forall>nx\<in>set (sourcenodes (a # as)). nx \<notin> backward_slice S\<close> 
      \<open>sourcenode a = n\<close>
    have False by(simp add:sourcenodes_def)
    thus ?case by simp
  qed simp
next
  case (Cons_path n'' as n' a n)
  note IH = \<open>\<And>as' s s'. \<lbrakk>n'' -as'\<rightarrow>* n'; slice_edges S as = slice_edges S as';
    preds (slice_kinds S as) s; preds (slice_kinds S as') s'; n' \<in> S;
    \<forall>V\<in>rv S n''. state_val s V = state_val s' V\<rbrakk> \<Longrightarrow> as = as'\<close>
  show ?case
  proof(cases as')
    case Nil
    with \<open>n -as'\<rightarrow>* n'\<close> have "n = n'" by fastforce
    from Nil \<open>slice_edges S (a#as) = slice_edges S as'\<close> \<open>sourcenode a = n\<close>
    have "n \<notin> backward_slice S" by(fastforce simp:slice_edges_def)
    from \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>n = n'\<close> \<open>n' \<in> S\<close>
    have "n \<in> backward_slice S" by(fastforce intro:refl)
    with \<open>n = n'\<close> \<open>n \<notin> backward_slice S\<close> have False by simp
    thus ?thesis by simp
  next
    case (Cons ax asx)
    with \<open>n -as'\<rightarrow>* n'\<close> have "n = sourcenode ax" and "valid_edge ax" 
      and "targetnode ax -asx\<rightarrow>* n'" by(auto elim:path_split_Cons)
    show ?thesis
    proof(cases "targetnode ax = n''")
      case True
      with \<open>targetnode ax -asx\<rightarrow>* n'\<close> have "n'' -asx\<rightarrow>* n'" by simp
      from \<open>valid_edge ax\<close> \<open>valid_edge a\<close> \<open>n = sourcenode ax\<close> \<open>sourcenode a = n\<close>
        True \<open>targetnode a = n''\<close> have "ax = a" by(fastforce intro:edge_det)
      from \<open>slice_edges S (a#as) = slice_edges S as'\<close> Cons 
        \<open>n = sourcenode ax\<close> \<open>sourcenode a = n\<close>
      have "slice_edges S as = slice_edges S asx"
        by(cases "n \<in> backward_slice S")(auto simp:slice_edges_def)
      from \<open>preds (slice_kinds S (a#as)) s\<close> 
      have preds1:"preds (slice_kinds S as) (transfer (slice_kind S a) s)"
        by(simp add:slice_kinds_def)
      from \<open>preds (slice_kinds S as') s'\<close> Cons \<open>ax = a\<close>
      have preds2:"preds (slice_kinds S asx) (transfer (slice_kind S a) s')"
        by(simp add:slice_kinds_def)
      from \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>targetnode a = n''\<close>
        \<open>preds (slice_kinds S (a#as)) s\<close> \<open>preds (slice_kinds S as') s'\<close>
        \<open>ax = a\<close> Cons \<open>\<forall>V\<in>rv S n. state_val s V = state_val s' V\<close>
      have "\<forall>V\<in>rv S n''. state_val (transfer (slice_kind S a) s) V =
                          state_val (transfer (slice_kind S a) s') V"
        by -(rule rv_edge_slice_kinds,auto)
      from IH[OF \<open>n'' -asx\<rightarrow>* n'\<close> \<open>slice_edges S as = slice_edges S asx\<close>
        preds1 preds2 \<open>n' \<in> S\<close> this] Cons \<open>ax = a\<close> show ?thesis by simp
    next
      case False
      with \<open>valid_edge a\<close> \<open>valid_edge ax\<close> \<open>sourcenode a = n\<close> \<open>n = sourcenode ax\<close>
        \<open>targetnode a = n''\<close> \<open>preds (slice_kinds S (a#as)) s\<close>
        \<open>preds (slice_kinds S as') s'\<close> Cons
        \<open>\<forall>V\<in>rv S n. state_val s V = state_val s' V\<close>
      have False by -(erule rv_branching_edges_slice_kinds_False,auto)
      thus ?thesis by simp
    qed
  qed
qed



lemma path_trans_observable_moves:
  assumes "n -as\<rightarrow>* n'" and "preds (kinds as) s" and "transfers (kinds as) s = s'"
  obtains n'' s'' as' as'' where "S,kind \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* (n'',s'')"
  and "S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',s')" 
  and "slice_edges S as = slice_edges S as''" and "n -as''@as'\<rightarrow>* n'"
proof(atomize_elim)
  from \<open>n -as\<rightarrow>* n'\<close> \<open>preds (kinds as) s\<close> \<open>transfers (kinds as) s = s'\<close>
  show "\<exists>n'' s'' as' as''. 
    S,kind \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* (n'',s'') \<and>
    S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',s') \<and> slice_edges S as = slice_edges S as'' \<and>
    n -as''@as'\<rightarrow>* n'"
  proof(induct arbitrary:s rule:path.induct)
    case (empty_path n)
    from \<open>transfers (kinds []) s = s'\<close> have "s = s'" by(simp add:kinds_def)
    have "S,kind \<turnstile> (n,s) =[]\<Rightarrow>* (n,s)" by(rule tom_Nil)
    have "S,kind \<turnstile> (n,s) =[]\<Rightarrow>\<^sub>\<tau> (n,s)" by(rule silent_moves_Nil)
    with \<open>S,kind \<turnstile> (n,s) =[]\<Rightarrow>* (n,s)\<close> \<open>s = s'\<close> \<open>valid_node n\<close>
    show ?case
      apply(rule_tac x="n" in exI)
      apply(rule_tac x="s" in exI)
      apply(rule_tac x="[]" in exI)
      apply(rule_tac x="[]" in exI)
      by(fastforce intro:path.empty_path simp:slice_edges_def)
  next
    case (Cons_path n'' as n' a n)
    note IH = \<open>\<And>s. \<lbrakk>preds (kinds as) s; transfers (kinds as) s = s'\<rbrakk>
      \<Longrightarrow> \<exists>nx s'' as' as''. S,kind \<turnstile> (n'',s) =slice_edges S as\<Rightarrow>* (nx,s'') \<and>
            S,kind \<turnstile> (nx,s'') =as'\<Rightarrow>\<^sub>\<tau> (n',s') \<and> 
            slice_edges S as = slice_edges S as'' \<and> n'' -as''@as'\<rightarrow>* n'\<close>
    from \<open>preds (kinds (a#as)) s\<close> \<open>transfers (kinds (a#as)) s = s'\<close>
    have "preds (kinds as) (transfer (kind a) s)" 
      "transfers (kinds as) (transfer (kind a) s) = s'" by(simp_all add:kinds_def)
    from IH[OF this] obtain nx sx asx asx'
      where "S,kind \<turnstile> (n'',transfer (kind a) s) =slice_edges S as\<Rightarrow>* (nx,sx)"
      and "S,kind \<turnstile> (nx,sx) =asx\<Rightarrow>\<^sub>\<tau> (n',s')"
      and "slice_edges S as = slice_edges S asx'"
      and "n'' -asx'@asx\<rightarrow>* n'"
      by clarsimp
    from \<open>preds (kinds (a#as)) s\<close> have "pred (kind a) s" by(simp add:kinds_def)
    show ?case
    proof(cases "n \<in> backward_slice S")
      case True
      with \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>targetnode a = n''\<close> \<open>pred (kind a) s\<close>
      have "S,kind \<turnstile> (n,s) -a\<rightarrow> (n'',transfer (kind a) s)"
        by(fastforce intro:observable_moveI)
      hence "S,kind \<turnstile> (n,s) =[]@[a]\<Rightarrow> (n'',transfer (kind a) s)"
        by(fastforce intro:observable_moves_snoc silent_moves_Nil)
      with \<open>S,kind \<turnstile> (n'',transfer (kind a) s) =slice_edges S as\<Rightarrow>* (nx,sx)\<close>
      have "S,kind \<turnstile> (n,s) =a#slice_edges S as\<Rightarrow>* (nx,sx)"
        by(fastforce dest:tom_Cons)
      with \<open>S,kind \<turnstile> (nx,sx) =asx\<Rightarrow>\<^sub>\<tau> (n',s')\<close>
        \<open>slice_edges S as = slice_edges S asx'\<close> \<open>n'' -asx'@asx\<rightarrow>* n'\<close>
        \<open>sourcenode a = n\<close> \<open>valid_edge a\<close> \<open>targetnode a = n''\<close> True
      show ?thesis
        apply(rule_tac x="nx" in exI)
        apply(rule_tac x="sx" in exI)
        apply(rule_tac x="asx" in exI)
        apply(rule_tac x="a#asx'" in exI)
        by(auto intro:path.Cons_path simp:slice_edges_def)
    next
      case False
      with \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>targetnode a = n''\<close> \<open>pred (kind a) s\<close>
      have "S,kind \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n'',transfer (kind a) s)"
        by(fastforce intro:silent_moveI)
      from \<open>S,kind \<turnstile> (n'',transfer (kind a) s) =slice_edges S as\<Rightarrow>* (nx,sx)\<close>
      obtain f s'' asx'' where "S,f \<turnstile> (n'',s'') =asx''\<Rightarrow>* (nx,sx)"
        and "f = kind" and "s'' = transfer (kind a) s" 
        and "asx'' = slice_edges S as" by simp
      from \<open>S,f \<turnstile> (n'',s'') =asx''\<Rightarrow>* (nx,sx)\<close> \<open>f = kind\<close>
        \<open>asx'' = slice_edges S as\<close> \<open>s'' = transfer (kind a) s\<close>
        \<open>S,kind \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (n'',transfer (kind a) s)\<close> 
        \<open>S,kind \<turnstile> (nx,sx) =asx\<Rightarrow>\<^sub>\<tau> (n',s')\<close> \<open>slice_edges S as = slice_edges S asx'\<close>
        \<open>n'' -asx'@asx\<rightarrow>* n'\<close> False
      show ?thesis
      proof(induct rule:trans_observable_moves.induct)
        case (tom_Nil S f ni si)
        have "S,kind \<turnstile> (n,s) =[]\<Rightarrow>* (n,s)" by(rule trans_observable_moves.tom_Nil)
        from \<open>S,kind \<turnstile> (ni,si) =asx\<Rightarrow>\<^sub>\<tau> (n',s')\<close>
          \<open>S,kind \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (ni,transfer (kind a) s)\<close> 
          \<open>si = transfer (kind a) s\<close>
        have "S,kind \<turnstile> (n,s) =a#asx\<Rightarrow>\<^sub>\<tau> (n',s')"
          by(fastforce intro:silent_moves_Cons)
        with \<open>valid_edge a\<close> \<open>sourcenode a = n\<close>
        have "n -a#asx\<rightarrow>* n'" by(fastforce dest:silent_moves_preds_transfers_path)
        with \<open>sourcenode a = n\<close> \<open>valid_edge a\<close> \<open>targetnode a = n''\<close>
          \<open>[] = slice_edges S as\<close> \<open>n \<notin> backward_slice S\<close>
          \<open>S,kind \<turnstile> (n,s) =a#asx\<Rightarrow>\<^sub>\<tau> (n',s')\<close>
        show ?case
          apply(rule_tac x="n" in exI)
          apply(rule_tac x="s" in exI)
          apply(rule_tac x="a#asx" in exI)
          apply(rule_tac x="[]" in exI)
          by(fastforce simp:slice_edges_def intro:trans_observable_moves.tom_Nil)
      next
        case (tom_Cons S f ni si asi ni' si' asi' n'' s'')
        from \<open>S,f \<turnstile> (ni,si) =asi\<Rightarrow> (ni',si')\<close> have "asi \<noteq> []"
          by(fastforce dest:observable_move_notempty)
        from \<open>S,kind \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (ni,transfer (kind a) s)\<close>
        have "valid_edge a" and "sourcenode a = n" and "targetnode a = ni"
          by(auto elim:silent_move.cases)
        from \<open>S,kind \<turnstile> (n,s) -a\<rightarrow>\<^sub>\<tau> (ni,transfer (kind a) s)\<close> \<open>f = kind\<close>
          \<open>si = transfer (kind a) s\<close> \<open>S,f \<turnstile> (ni,si) =asi\<Rightarrow> (ni',si')\<close>
        have "S,f \<turnstile> (n,s) =a#asi\<Rightarrow> (ni',si')"
          by(fastforce intro:silent_move_observable_moves)
        with \<open>S,f \<turnstile> (ni',si') =asi'\<Rightarrow>* (n'',s'')\<close>
        have "S,f \<turnstile> (n,s) =(last (a#asi))#asi'\<Rightarrow>* (n'',s'')"
          by -(rule trans_observable_moves.tom_Cons)
        with \<open>f = kind\<close> \<open>last asi # asi' = slice_edges S as\<close> \<open>n \<notin> backward_slice S\<close>
          \<open>S,kind \<turnstile> (n'',s'') =asx\<Rightarrow>\<^sub>\<tau> (n',s')\<close>  \<open>sourcenode a = n\<close> \<open>asi \<noteq> []\<close>
          \<open>ni -asx'@asx\<rightarrow>* n'\<close> \<open>slice_edges S as = slice_edges S asx'\<close>
          \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>targetnode a = ni\<close>
        show ?case
          apply(rule_tac x="n''" in exI)
          apply(rule_tac x="s''" in exI)
          apply(rule_tac x="asx" in exI)
          apply(rule_tac x="a#asx'" in exI)
          by(auto intro:path.Cons_path simp:slice_edges_def)
      qed
    qed
  qed
qed


lemma WS_weak_sim_trans:
  assumes "((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S"
  and "S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow>* (n\<^sub>1',s\<^sub>1')" and "as \<noteq> []"
  shows "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfers (slice_kinds S as) s\<^sub>2)) \<in> WS S \<and> 
         S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as\<Rightarrow>* (n\<^sub>1',transfers (slice_kinds S as) s\<^sub>2)"
proof -
  obtain f where "f = kind" by simp
  with \<open>S,kind \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow>* (n\<^sub>1',s\<^sub>1')\<close> 
  have "S,f \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow>* (n\<^sub>1',s\<^sub>1')" by simp
  from \<open>S,f \<turnstile> (n\<^sub>1,s\<^sub>1) =as\<Rightarrow>* (n\<^sub>1',s\<^sub>1')\<close> \<open>((n\<^sub>1,s\<^sub>1),(n\<^sub>2,s\<^sub>2)) \<in> WS S\<close> \<open>as \<noteq> []\<close> \<open>f = kind\<close>
  show "((n\<^sub>1',s\<^sub>1'),(n\<^sub>1',transfers (slice_kinds S as) s\<^sub>2)) \<in> WS S \<and>
    S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as\<Rightarrow>* (n\<^sub>1',transfers (slice_kinds S as) s\<^sub>2)"
  proof(induct arbitrary:n\<^sub>2 s\<^sub>2 rule:trans_observable_moves.induct)
    case tom_Nil thus ?case by simp
  next
    case (tom_Cons S f n s as n' s' as' n'' s'')
    note IH = \<open>\<And>n\<^sub>2 s\<^sub>2. \<lbrakk>((n',s'),(n\<^sub>2,s\<^sub>2)) \<in> WS S; as' \<noteq> []; f = kind\<rbrakk>
      \<Longrightarrow> ((n'',s''),(n'',transfers (slice_kinds S as') s\<^sub>2)) \<in> WS S \<and>
      S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =as'\<Rightarrow>* (n'',transfers (slice_kinds S as') s\<^sub>2)\<close>
    from \<open>S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s')\<close>
    obtain asx ax nx sx where "S,f \<turnstile> (n,s) =asx\<Rightarrow>\<^sub>\<tau> (nx,sx)"
      and "S,f \<turnstile> (nx,sx) -ax\<rightarrow> (n',s')" and "as = asx@[ax]"
      by(fastforce elim:observable_moves.cases)
    from \<open>S,f \<turnstile> (nx,sx) -ax\<rightarrow> (n',s')\<close> have "obs nx (backward_slice S) = {nx}"
      by(fastforce intro!:n_in_obs elim:observable_move.cases)
    with \<open>S,f \<turnstile> (n,s) =asx\<Rightarrow>\<^sub>\<tau> (nx,sx)\<close> \<open>((n,s),(n\<^sub>2,s\<^sub>2)) \<in> WS S\<close> \<open>f = kind\<close>
    have "((nx,sx),(n\<^sub>2,s\<^sub>2)) \<in> WS S" by(fastforce intro:WS_silent_moves)
    with \<open>S,f \<turnstile> (nx,sx) -ax\<rightarrow> (n',s')\<close> \<open>f = kind\<close>
    obtain asx' where "((n',s'),(n',transfer (slice_kind S ax) s\<^sub>2)) \<in> WS S"
      and "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =asx'@[ax]\<Rightarrow> 
      (n',transfer (slice_kind S ax) s\<^sub>2)"
      by(fastforce elim:WS_observable_move)
    show ?case
    proof(cases "as' = []")
      case True
      with \<open>S,f \<turnstile> (n',s') =as'\<Rightarrow>* (n'',s'')\<close> have "n' = n'' \<and> s' = s''"
        by(fastforce elim:trans_observable_moves.cases dest:observable_move_notempty)
      from \<open>S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =asx'@[ax]\<Rightarrow> 
                               (n',transfer (slice_kind S ax) s\<^sub>2)\<close>
      have "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =(last (asx'@[ax]))#[]\<Rightarrow>* 
                               (n',transfer (slice_kind S ax) s\<^sub>2)"
        by(fastforce intro:trans_observable_moves.intros)
      with \<open>((n',s'),(n',transfer (slice_kind S ax) s\<^sub>2)) \<in> WS S\<close> \<open>as = asx@[ax]\<close>
        \<open>n' = n'' \<and> s' = s''\<close> True
      show ?thesis by(fastforce simp:slice_kinds_def)
    next
      case False
      from IH[OF \<open>((n',s'),(n',transfer (slice_kind S ax) s\<^sub>2)) \<in> WS S\<close> this 
        \<open>f = kind\<close>]
      have "((n'',s''),(n'',transfers (slice_kinds S as') 
        (transfer (slice_kind S ax) s\<^sub>2))) \<in> WS S"
        and "S,slice_kind S \<turnstile> (n',transfer (slice_kind S ax) s\<^sub>2) 
        =as'\<Rightarrow>* (n'',transfers (slice_kinds S as')
                     (transfer (slice_kind S ax) s\<^sub>2))" by simp_all
      with \<open>S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =asx'@[ax]\<Rightarrow> 
                               (n',transfer (slice_kind S ax) s\<^sub>2)\<close>
      have "S,slice_kind S \<turnstile> (n\<^sub>2,s\<^sub>2) =(last (asx'@[ax]))#as'\<Rightarrow>* 
        (n'',transfers (slice_kinds S as') (transfer (slice_kind S ax) s\<^sub>2))"
        by(fastforce intro:trans_observable_moves.tom_Cons)
      with \<open>((n'',s''),(n'',transfers (slice_kinds S as') 
        (transfer (slice_kind S ax) s\<^sub>2))) \<in> WS S\<close> False \<open>as = asx@[ax]\<close>
      show ?thesis by(fastforce simp:slice_kinds_def)
    qed
  qed
qed


lemma transfers_slice_kinds_slice_edges:
  "transfers (slice_kinds S (slice_edges S as)) s = transfers (slice_kinds S as) s"
proof(induct as arbitrary:s)
  case Nil thus ?case by(simp add:slice_kinds_def slice_edges_def)
next
  case (Cons a' as')
  note IH = \<open>\<And>s. transfers (slice_kinds S (slice_edges S as')) s =
                  transfers (slice_kinds S as') s\<close>
  show ?case
  proof(cases "sourcenode a' \<in> backward_slice S")
    case True
    hence eq:"transfers (slice_kinds S (slice_edges S (a'#as'))) s
            = transfers (slice_kinds S (slice_edges S as')) 
                (transfer (slice_kind S a') s)"
      by(simp add:slice_edges_def slice_kinds_def)
    have "transfers (slice_kinds S (a'#as')) s
        = transfers (slice_kinds S as') (transfer (slice_kind S a') s)"
      by(simp add:slice_kinds_def)
    with eq IH[of "transfer (slice_kind S a') s"] show ?thesis by simp
  next
    case False
    hence eq:"transfers (slice_kinds S (slice_edges S (a'#as'))) s
            = transfers (slice_kinds S (slice_edges S as')) s"
      by(simp add:slice_edges_def slice_kinds_def)
    from False have "transfer (slice_kind S a') s = s"
      by(cases "kind a'",auto simp:slice_kind_def Let_def)
    hence "transfers (slice_kinds S (a'#as')) s
         = transfers (slice_kinds S as') s"
      by(simp add:slice_kinds_def)
    with eq IH[of s] show ?thesis by simp
  qed
qed


lemma trans_observable_moves_preds:
  assumes "S,f \<turnstile> (n,s) =as\<Rightarrow>* (n',s')" and "valid_node n"
  obtains as' where "preds (map f as') s" and "slice_edges S as' = as"
  and "n -as'\<rightarrow>* n'"
proof(atomize_elim)
  from \<open>S,f \<turnstile> (n,s) =as\<Rightarrow>* (n',s')\<close> \<open>valid_node n\<close>
  show "\<exists>as'. preds (map f as') s \<and> slice_edges S as' = as \<and> n -as'\<rightarrow>* n'"
  proof(induct rule:trans_observable_moves.induct)
    case tom_Nil thus ?case 
      by(rule_tac x="[]" in exI,fastforce intro:empty_path simp:slice_edges_def)
  next
    case (tom_Cons S f n s as n' s' as' n'' s'')
    note IH = \<open>valid_node n' 
      \<Longrightarrow> \<exists>asx. preds (map f asx) s' \<and> slice_edges S asx = as' \<and> n' -asx\<rightarrow>* n''\<close>
    from \<open>S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s')\<close>
    have "preds (map f as) s" and "transfers (map f as) s = s'"
      and "n -as\<rightarrow>* n'"
      by(fastforce dest:observable_moves_preds_transfers_path)+
    from \<open>n -as\<rightarrow>* n'\<close> have "valid_node n'" by(fastforce dest:path_valid_node)
    from \<open>S,f \<turnstile> (n,s) =as\<Rightarrow> (n',s')\<close> have "slice_edges S as = [last as]"
      by(rule observable_moves_last_slice_edges)
    from IH[OF \<open>valid_node n'\<close>]
    obtain asx where "preds (map f asx) s'" and "slice_edges S asx = as'"
      and "n' -asx\<rightarrow>* n''"
      by blast
    from \<open>n -as\<rightarrow>* n'\<close> \<open>n' -asx\<rightarrow>* n''\<close> have "n -as@asx\<rightarrow>* n''" by(rule path_Append)
    from \<open>preds (map f asx) s'\<close> \<open>transfers (map f as) s = s'\<close>[THEN sym]
      \<open>preds (map f as) s\<close>
    have "preds (map f (as@asx)) s" by(simp add:preds_split)
    with \<open>slice_edges S as = [last as]\<close> \<open>slice_edges S asx = as'\<close> 
      \<open>n -as@asx\<rightarrow>* n''\<close> show ?case
      by(rule_tac x="as@asx" in exI,auto simp:slice_edges_def)
  qed
qed



lemma exists_sliced_path_preds:
  assumes "n -as\<rightarrow>* n'" and "slice_edges S as = []" and "n' \<in> backward_slice S"
  obtains as' where "n -as'\<rightarrow>* n'" and "preds (slice_kinds S as') s"
  and "slice_edges S as' = []"
proof(atomize_elim)
  from \<open>slice_edges S as = []\<close>
  have "\<forall>nx \<in> set(sourcenodes as). nx \<notin> (backward_slice S)"
    by(rule slice_edges_no_nodes_in_slice)
  with \<open>n -as\<rightarrow>* n'\<close> \<open>n' \<in> backward_slice S\<close> have "n' \<in> obs n (backward_slice S)"
    by -(rule obs_elem)
  hence "obs n (backward_slice S) = {n'}" by(rule obs_singleton_element)
  from \<open>n -as\<rightarrow>* n'\<close> have "valid_node n" and "valid_node n'"
    by(fastforce dest:path_valid_node)+
  from \<open>n -as\<rightarrow>* n'\<close> obtain x where "distance n n' x" and "x \<le> length as"
    by(erule every_path_distance)
  from \<open>distance n n' x\<close> \<open>obs n (backward_slice S) = {n'}\<close>
  show "\<exists>as'. n -as'\<rightarrow>* n' \<and> preds (slice_kinds S as') s \<and> 
              slice_edges S as' = []"
  proof(induct x arbitrary:n rule:nat.induct)
    case zero
    from \<open>distance n n' 0\<close> have "n = n'" by(fastforce elim:distance.cases)
    with \<open>valid_node n'\<close> show ?case
      by(rule_tac x="[]" in exI,
        auto intro:empty_path simp:slice_kinds_def slice_edges_def)
  next
    case (Suc x)
    note IH = \<open>\<And>n. \<lbrakk>distance n n' x; obs n (backward_slice S) = {n'}\<rbrakk>
      \<Longrightarrow> \<exists>as'. n -as'\<rightarrow>* n' \<and> preds (slice_kinds S as') s \<and> 
               slice_edges S as' = []\<close>
    from \<open>distance n n' (Suc x)\<close> obtain a 
      where "valid_edge a" and "n = sourcenode a" 
      and "distance (targetnode a) n' x"
      and target:"targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
      distance (targetnode a') n' x \<and>
      valid_edge a' \<and> targetnode a' = nx)"
      by(auto elim:distance_successor_distance)
    have "n \<notin> backward_slice S"
    proof
      assume "n \<in> backward_slice S"
      from \<open>valid_edge a\<close> \<open>n = sourcenode a\<close> have "valid_node n" by simp
      with \<open>n \<in> backward_slice S\<close> have "obs n (backward_slice S) = {n}"
        by -(rule n_in_obs)
      with \<open>obs n (backward_slice S) = {n'}\<close> have "n = n'" by simp
      with \<open>valid_node n\<close> have "n -[]\<rightarrow>* n'" by(fastforce intro:empty_path)
      with \<open>distance n n' (Suc x)\<close> show False
        by(fastforce elim:distance.cases)
    qed
    from \<open>distance (targetnode a) n' x\<close> \<open>n' \<in> backward_slice S\<close>
    obtain m where "m \<in> obs (targetnode a) (backward_slice S)"
      by(fastforce elim:distance.cases path_ex_obs)
    from \<open>valid_edge a\<close> \<open>n \<notin> backward_slice S\<close> \<open>n = sourcenode a\<close>
    have "obs (targetnode a) (backward_slice S) \<subseteq> 
      obs (sourcenode a) (backward_slice S)"
      by -(rule edge_obs_subset,auto)
    with \<open>m \<in> obs (targetnode a) (backward_slice S)\<close> \<open>n = sourcenode a\<close>
      \<open>obs n (backward_slice S) = {n'}\<close>
    have "n' \<in> obs (targetnode a) (backward_slice S)" by auto
    hence "obs (targetnode a) (backward_slice S) = {n'}" 
      by(rule obs_singleton_element)
    from IH[OF \<open>distance (targetnode a) n' x\<close> this]
    obtain as where "targetnode a -as\<rightarrow>* n'" and "preds (slice_kinds S as) s"
      and "slice_edges S as = []" by blast
    from \<open>targetnode a -as\<rightarrow>* n'\<close> \<open>valid_edge a\<close> \<open>n = sourcenode a\<close>
    have "n -a#as\<rightarrow>* n'" by(fastforce intro:Cons_path)
    from \<open>slice_edges S as = []\<close> \<open>n \<notin> backward_slice S\<close> \<open>n = sourcenode a\<close>
    have "slice_edges S (a#as) = []" by(simp add:slice_edges_def)
    show ?case
    proof(cases "kind a")
      case (Update f)
      with \<open>n \<notin> backward_slice S\<close> \<open>n = sourcenode a\<close> have "slice_kind S a = \<Up>id"
        by(fastforce intro:slice_kind_Upd)
      hence "transfer (slice_kind S a) s = s" and "pred (slice_kind S a) s"
        by simp_all
      with \<open>preds (slice_kinds S as) s\<close> have "preds (slice_kinds S (a#as)) s"
        by(simp add:slice_kinds_def)
      with \<open>n -a#as\<rightarrow>* n'\<close> \<open>slice_edges S (a#as) = []\<close> show ?thesis
        by blast
    next
      case (Predicate Q)
      with \<open>n \<notin> backward_slice S\<close> \<open>n = sourcenode a\<close> \<open>distance n n' (Suc x)\<close>  
        \<open>obs n (backward_slice S) = {n'}\<close> \<open>distance (targetnode a) n' x\<close>
        \<open>targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
        distance (targetnode a') n' x \<and>
        valid_edge a' \<and> targetnode a' = nx)\<close>
      have "slice_kind S a = (\<lambda>s. True)\<^sub>\<surd>"
        by(fastforce intro:slice_kind_Pred_obs_nearer_SOME)
      hence "transfer (slice_kind S a) s = s" and "pred (slice_kind S a) s"
        by simp_all
      with \<open>preds (slice_kinds S as) s\<close> have "preds (slice_kinds S (a#as)) s"
        by(simp add:slice_kinds_def)
      with \<open>n -a#as\<rightarrow>* n'\<close> \<open>slice_edges S (a#as) = []\<close> show ?thesis by blast
    qed
  qed
qed


theorem fundamental_property_of_static_slicing:
  assumes path:"n -as\<rightarrow>* n'" and preds:"preds (kinds as) s" and "n' \<in> S"
  obtains as' where "preds (slice_kinds S as') s"
  and "(\<forall>V \<in> Use n'. state_val (transfers (slice_kinds S as') s) V = 
                     state_val (transfers (kinds as) s) V)"
  and "slice_edges S as = slice_edges S as'" and "n -as'\<rightarrow>* n'"
proof(atomize_elim)
  from path preds obtain n'' s'' as' as''
    where "S,kind \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* (n'',s'')"
    and "S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)"
    and "slice_edges S as = slice_edges S as''"
    and "n -as''@as'\<rightarrow>* n'"
    by -(erule_tac S="S" in path_trans_observable_moves,auto)
  from path have "valid_node n" and "valid_node n'" 
    by(fastforce dest:path_valid_node)+
  from \<open>valid_node n\<close> have "((n,s),(n,s)) \<in> WS S" by(fastforce intro:WSI)
  from \<open>valid_node n'\<close> \<open>n' \<in> S\<close> have "obs n' (backward_slice S) = {n'}"
    by(fastforce intro!:n_in_obs refl)
  from \<open>valid_node n'\<close> have "n'-[]\<rightarrow>* n'" by(fastforce intro:empty_path)
  with \<open>valid_node n'\<close> \<open>n' \<in> S\<close> have "\<forall>V \<in> Use n'. V \<in> rv S n'"
    by(fastforce intro:rvI refl simp:sourcenodes_def)
  show "\<exists>as'. preds (slice_kinds S as') s \<and>
    (\<forall>V \<in> Use n'. state_val (transfers (slice_kinds S as') s) V = 
                  state_val (transfers (kinds as) s) V) \<and>
    slice_edges S as = slice_edges S as' \<and> n -as'\<rightarrow>* n'"
  proof(cases "slice_edges S as = []")
    case True
    hence "preds (slice_kinds S []) s" and "slice_edges S [] = slice_edges S as"
      by(simp_all add:slice_kinds_def slice_edges_def)
    from \<open>S,kind \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* (n'',s'')\<close> True
    have "n = n''" and "s = s''"
      by(fastforce elim:trans_observable_moves.cases)+
    with \<open>S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)\<close>
    have "S,kind \<turnstile> (n,s) =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)" by simp
    with \<open>valid_node n\<close> have "n -as'\<rightarrow>* n'"
      by(fastforce dest:silent_moves_preds_transfers_path)
    from \<open>S,kind \<turnstile> (n,s) =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)\<close>
    have "slice_edges S as' = []" by(fastforce dest:silent_moves_no_slice_edges)
    with \<open>n -as'\<rightarrow>* n'\<close> \<open>valid_node n'\<close> \<open>n' \<in> S\<close> obtain asx
      where "n -asx\<rightarrow>* n'" and "preds (slice_kinds S asx) s"
      and "slice_edges S asx = []"
      by -(erule exists_sliced_path_preds,auto intro:refl)
    from \<open>S,kind \<turnstile> (n,s) =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)\<close>
      \<open>((n,s),(n,s)) \<in> WS S\<close> \<open>obs n' (backward_slice S) = {n'}\<close>
    have "((n',transfers (kinds as) s),(n,s)) \<in> WS S"
      by(fastforce intro:WS_silent_moves)
    with True have "\<forall>V \<in> rv S n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S as)) s) V"
      by(fastforce dest:WSD simp:slice_edges_def slice_kinds_def)
    with \<open>\<forall>V \<in> Use n'. V \<in> rv S n'\<close>
    have "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S as)) s) V" by simp
    with \<open>slice_edges S asx = []\<close> \<open>slice_edges S [] = slice_edges S as\<close>
    have "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S asx)) s) V"
      by(simp add:slice_edges_def)
    hence "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S asx) s) V"
      by(simp add:transfers_slice_kinds_slice_edges)
    with \<open>n -asx\<rightarrow>* n'\<close> \<open>preds (slice_kinds S asx) s\<close>
      \<open>slice_edges S asx = []\<close> \<open>slice_edges S [] = slice_edges S as\<close>
    show ?thesis
      by(rule_tac x="asx" in exI,simp add:slice_edges_def)
  next
    case False
    with \<open>S,kind \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* (n'',s'')\<close> \<open>((n,s),(n,s)) \<in> WS S\<close>
    have "((n'',s''),(n'',transfers (slice_kinds S (slice_edges S as)) s)) \<in> WS S"
      "S,slice_kind S \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* 
      (n'',transfers (slice_kinds S (slice_edges S as)) s)"
      by(fastforce dest:WS_weak_sim_trans)+
    from \<open>S,slice_kind S \<turnstile> (n,s) =slice_edges S as\<Rightarrow>* 
                             (n'',transfers (slice_kinds S (slice_edges S as)) s)\<close>
      \<open>valid_node n\<close>
    obtain asx where "preds (slice_kinds S asx) s" 
      and "slice_edges S asx = slice_edges S as"
      and "n -asx\<rightarrow>* n''"
      by(fastforce elim:trans_observable_moves_preds simp:slice_kinds_def)
    from \<open>n -asx\<rightarrow>* n''\<close> have "valid_node n''" by(fastforce dest:path_valid_node)
    with \<open>S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)\<close>
    have "n'' -as'\<rightarrow>* n'"
      by(fastforce dest:silent_moves_preds_transfers_path)
    from \<open>S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)\<close>
    have "slice_edges S as' = []" by(fastforce dest:silent_moves_no_slice_edges)
    with \<open>n'' -as'\<rightarrow>* n'\<close> \<open>valid_node n'\<close> \<open>n' \<in> S\<close> obtain asx'
      where "n'' -asx'\<rightarrow>* n'" and "slice_edges S asx' = []"
      and "preds (slice_kinds S asx') (transfers (slice_kinds S asx) s)"
      by -(erule exists_sliced_path_preds,auto intro:refl)
    from \<open>n -asx\<rightarrow>* n''\<close> \<open>n'' -asx'\<rightarrow>* n'\<close> have "n -asx@asx'\<rightarrow>* n'"
      by(rule path_Append)
    from \<open>slice_edges S asx = slice_edges S as\<close> \<open>slice_edges S asx' = []\<close>
    have "slice_edges S as = slice_edges S (asx@asx')"
      by(auto simp:slice_edges_def)
    from \<open>preds (slice_kinds S asx') (transfers (slice_kinds S asx) s)\<close>
      \<open>preds (slice_kinds S asx) s\<close>
    have "preds (slice_kinds S (asx@asx')) s" 
      by(simp add:slice_kinds_def preds_split)
    from \<open>obs n' (backward_slice S) = {n'}\<close>
      \<open>S,kind \<turnstile> (n'',s'') =as'\<Rightarrow>\<^sub>\<tau> (n',transfers (kinds as) s)\<close>
      \<open>((n'',s''),(n'',transfers (slice_kinds S (slice_edges S as)) s)) \<in> WS S\<close>
    have "((n',transfers (kinds as) s),
      (n'',transfers (slice_kinds S (slice_edges S as)) s)) \<in> WS S"
      by(fastforce intro:WS_silent_moves)
    hence "\<forall>V \<in> rv S n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S as)) s) V"
      by(fastforce dest:WSD)
    with \<open>\<forall>V \<in> Use n'. V \<in> rv S n'\<close> \<open>slice_edges S asx = slice_edges S as\<close>
    have "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S asx)) s) V"
      by fastforce
    with \<open>slice_edges S asx' = []\<close>
    have "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (slice_edges S (asx@asx'))) s) V"
      by(auto simp:slice_edges_def)
    hence "\<forall>V \<in> Use n'. state_val (transfers (kinds as) s) V = 
      state_val (transfers (slice_kinds S (asx@asx')) s) V"
      by(simp add:transfers_slice_kinds_slice_edges)
    with \<open>preds (slice_kinds S (asx@asx')) s\<close> \<open>n -asx@asx'\<rightarrow>* n'\<close>
      \<open>slice_edges S as = slice_edges S (asx@asx')\<close>
    show ?thesis by simp blast
  qed
qed


end


subsection \<open>The fundamental property of (static) slicing related to the semantics\<close>

locale BackwardSlice_wf = 
  BackwardSlice sourcenode targetnode kind valid_edge Entry Def Use state_val 
  backward_slice +
  CFG_semantics_wf sourcenode targetnode kind valid_edge Entry sem identifies
  for sourcenode :: "'edge \<Rightarrow> 'node" and targetnode :: "'edge \<Rightarrow> 'node"
  and kind :: "'edge \<Rightarrow> 'state edge_kind" and valid_edge :: "'edge \<Rightarrow> bool"
  and Entry :: "'node" ("'('_Entry'_')") and Def :: "'node \<Rightarrow> 'var set"
  and Use :: "'node \<Rightarrow> 'var set" and state_val :: "'state \<Rightarrow> 'var \<Rightarrow> 'val"
  and backward_slice :: "'node set \<Rightarrow> 'node set" 
  and sem :: "'com \<Rightarrow> 'state \<Rightarrow> 'com \<Rightarrow> 'state \<Rightarrow> bool" 
    ("((1\<langle>_,/_\<rangle>) \<Rightarrow>/ (1\<langle>_,/_\<rangle>))" [0,0,0,0] 81)
  and identifies :: "'node \<Rightarrow> 'com \<Rightarrow> bool" ("_ \<triangleq> _" [51, 0] 80)

begin


theorem fundamental_property_of_path_slicing_semantically:
  assumes "n \<triangleq> c" and "\<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>"
  obtains n' as where "n -as\<rightarrow>* n'" and "preds (slice_kinds {n'} as) s" and "n' \<triangleq> c'"
  and "\<forall>V \<in> Use n'. state_val (transfers (slice_kinds {n'} as) s) V = state_val s' V"
proof(atomize_elim)
  from \<open>n \<triangleq> c\<close> \<open>\<langle>c,s\<rangle> \<Rightarrow> \<langle>c',s'\<rangle>\<close> obtain n' as where "n -as\<rightarrow>* n'"
    and "transfers (kinds as) s = s'" and "preds (kinds as) s" and "n' \<triangleq> c'"
    by(fastforce dest:fundamental_property)
  from \<open>n -as\<rightarrow>* n'\<close> \<open>preds (kinds as) s\<close> obtain as'
    where "preds (slice_kinds {n'} as') s"
    and vals:"\<forall>V \<in> Use n'. state_val (transfers (slice_kinds {n'} as') s) V = 
    state_val (transfers (kinds as) s) V" and "n -as'\<rightarrow>* n'"
    by -(erule fundamental_property_of_static_slicing,auto)
  from \<open>transfers (kinds as) s = s'\<close> vals have "\<forall>V \<in> Use n'.
    state_val (transfers (slice_kinds {n'} as') s) V = state_val s' V"
    by simp
  with \<open>preds (slice_kinds {n'} as') s\<close> \<open>n -as'\<rightarrow>* n'\<close> \<open> n' \<triangleq> c'\<close>
  show "\<exists>as n'. n -as\<rightarrow>* n' \<and> preds (slice_kinds {n'} as) s \<and> n' \<triangleq> c' \<and>
    (\<forall>V\<in>Use n'. state_val (transfers (slice_kinds {n'} as) s) V = state_val s' V)"
    by blast
qed


end

end
