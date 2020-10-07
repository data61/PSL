chapter \<open>Static Intraprocedural Slicing\<close>

theory Distance imports "../Basic/CFG" begin

text \<open>
  Static Slicing analyses a CFG prior to execution. Whereas dynamic
  slicing can provide better results for certain inputs (i.e.\ trace and
  initial state), static slicing is more conservative but provides
  results independent of inputs. 

  Correctness for static slicing is
  defined differently than correctness of dynamic slicing by a weak
  simulation between nodes and states when traversing the original and
  the sliced graph. The weak simulation property demands that if a
  (node,state) tuples $(n_1,s_1)$ simulates $(n_2,s_2)$
  and making an observable move in the original graph leads from 
  $(n_1,s_1)$ to $(n_1',s_1')$, this tuple simulates a 
  tuple $(n_2,s_2)$ which is the result of making an
  observable move in the sliced graph beginning in $(n_2',s_2')$.

  We also show how a ``dynamic slicing style'' correctness criterion for 
  static slicing of a given trace and initial state could look like.

  This formalization of static intraprocedural slicing is instantiable
  with three different kinds of control dependences: standard control,
  weak control and weak order dependence. The correctness proof for
  slicing is independent of the control dependence used, it bases only
  on one property every control dependence definition hass to fulfill.
\<close>

section \<open>Distance of Paths\<close>

context CFG begin

inductive distance :: "'node \<Rightarrow> 'node \<Rightarrow> nat \<Rightarrow> bool"
where distanceI: 
  "\<lbrakk>n -as\<rightarrow>* n'; length as = x; \<forall>as'. n -as'\<rightarrow>* n' \<longrightarrow> x \<le> length as'\<rbrakk>
  \<Longrightarrow> distance n n' x"


lemma every_path_distance:
  assumes "n -as\<rightarrow>* n'"
  obtains x where "distance n n' x" and "x \<le> length as"
proof -
  have "\<exists>x. distance n n' x \<and> x \<le> length as"
  proof(cases "\<exists>as'. n -as'\<rightarrow>* n' \<and> 
                     (\<forall>asx. n -asx\<rightarrow>* n' \<longrightarrow> length as' \<le> length asx)")
    case True
    then obtain as' 
      where "n -as'\<rightarrow>* n' \<and> (\<forall>asx. n -asx\<rightarrow>* n' \<longrightarrow> length as' \<le> length asx)" 
      by blast
    hence "n -as'\<rightarrow>* n'" and all:"\<forall>asx. n -asx\<rightarrow>* n' \<longrightarrow> length as' \<le> length asx"
      by simp_all
    hence "distance n n' (length as')" by(fastforce intro:distanceI)
    from \<open>n -as\<rightarrow>* n'\<close> all have "length as' \<le> length as" by fastforce
    with \<open>distance n n' (length as')\<close> show ?thesis by blast
  next
    case False
    hence all:"\<forall>as'. n -as'\<rightarrow>* n' \<longrightarrow> (\<exists>asx. n -asx\<rightarrow>* n' \<and> length as' > length asx)"
      by fastforce
    have "wf (measure length)" by simp
    from \<open>n -as\<rightarrow>* n'\<close> have "as \<in> {as. n -as\<rightarrow>* n'}" by simp
    with \<open>wf (measure length)\<close> obtain as' where "as' \<in> {as. n -as\<rightarrow>* n'}" 
      and notin:"\<And>as''. (as'',as') \<in> (measure length) \<Longrightarrow> as'' \<notin> {as. n -as\<rightarrow>* n'}"
      by(erule wfE_min)
    from \<open>as' \<in> {as. n -as\<rightarrow>* n'}\<close> have "n -as'\<rightarrow>* n'" by simp
    with all obtain asx where "n -asx\<rightarrow>* n'"
      and "length as' > length asx"
      by blast
    with notin have  "asx \<notin> {as. n -as\<rightarrow>* n'}" by simp
    hence "\<not> n -asx\<rightarrow>* n'" by simp
    with \<open>n -asx\<rightarrow>* n'\<close> have False by simp
    thus ?thesis by simp
  qed
  with that show ?thesis by blast
qed


lemma distance_det:
  "\<lbrakk>distance n n' x; distance n n' x'\<rbrakk> \<Longrightarrow> x = x'"
apply(erule distance.cases)+ apply clarsimp
apply(erule_tac x="asa" in allE) apply(erule_tac x="as" in allE)
by simp


lemma only_one_SOME_dist_edge:
  assumes valid:"valid_edge a" and dist:"distance (targetnode a) n' x"
  shows "\<exists>!a'. sourcenode a = sourcenode a' \<and> distance (targetnode a') n' x \<and>
               valid_edge a' \<and>
               targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                              distance (targetnode a') n' x \<and>
                                              valid_edge a' \<and> targetnode a' = nx)"
proof(rule ex_ex1I)
  show "\<exists>a'. sourcenode a = sourcenode a' \<and> 
             distance (targetnode a') n' x \<and> valid_edge a' \<and>
             targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                            distance (targetnode a') n' x \<and>
                                            valid_edge a' \<and> targetnode a' = nx)"
  proof -
    have "(\<exists>a'. sourcenode a = sourcenode a' \<and> 
                distance (targetnode a') n' x \<and> valid_edge a' \<and> 
                targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                               distance (targetnode a') n' x \<and>
                                               valid_edge a' \<and> targetnode a' = nx)) =
      (\<exists>nx. \<exists>a'. sourcenode a = sourcenode a' \<and> distance (targetnode a') n' x \<and> 
                 valid_edge a' \<and> targetnode a' = nx)"
      apply(unfold some_eq_ex[of "\<lambda>nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                distance (targetnode a') n' x \<and>valid_edge a' \<and>  targetnode a' = nx"])
      by simp
    also have "\<dots>" using valid dist by blast
    finally show ?thesis .
  qed
next
  fix a' ax
  assume "sourcenode a = sourcenode a' \<and> 
    distance (targetnode a') n' x \<and> valid_edge a' \<and>
    targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                   distance (targetnode a') n' x \<and> 
                                   valid_edge a' \<and> targetnode a' = nx)"
    and "sourcenode a = sourcenode ax \<and> 
    distance (targetnode ax) n' x \<and> valid_edge ax \<and>
    targetnode ax = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                   distance (targetnode a') n' x \<and> 
                                   valid_edge a' \<and> targetnode a' = nx)"
  thus "a' = ax" by(fastforce intro!:edge_det)
qed


lemma distance_successor_distance:
  assumes "distance n n' x" and "x \<noteq> 0" 
  obtains a where "valid_edge a" and "n = sourcenode a" 
  and "distance (targetnode a) n' (x - 1)"
  and "targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                     distance (targetnode a') n' (x - 1) \<and>
                                     valid_edge a' \<and> targetnode a' = nx)"
proof -
  have "\<exists>a. valid_edge a \<and> n = sourcenode a \<and> distance (targetnode a) n' (x - 1) \<and>
    targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                  distance (targetnode a') n' (x - 1) \<and>
                                  valid_edge a' \<and> targetnode a' = nx)"
  proof(rule ccontr)
    assume "\<not> (\<exists>a. valid_edge a \<and> n = sourcenode a \<and> 
                   distance (targetnode a) n' (x - 1) \<and> 
                   targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and> 
                                                 distance (targetnode a') n' (x - 1) \<and>
                                                 valid_edge a' \<and> targetnode a' = nx))"
    hence imp:"\<forall>a. valid_edge a \<and> n = sourcenode a \<and>
                   targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') n' (x - 1) \<and>
                                                 valid_edge a' \<and> targetnode a' = nx)
                 \<longrightarrow> \<not> distance (targetnode a) n' (x - 1)" by blast
    from \<open>distance n n' x\<close> obtain as where "n -as\<rightarrow>* n'" and "x = length as"
      and "\<forall>as'. n -as'\<rightarrow>* n' \<longrightarrow> x \<le> length as'"
      by(auto elim:distance.cases)
    thus False using imp
    proof(induct rule:path.induct)
      case (empty_path n)
      from \<open>x = length []\<close> \<open>x \<noteq> 0\<close> show False by simp
    next
      case (Cons_path n'' as n' a n)
      note imp = \<open>\<forall>a. valid_edge a \<and> n = sourcenode a \<and>
                      targetnode a = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                                 distance (targetnode a') n' (x - 1) \<and>
                                                 valid_edge a' \<and> targetnode a' = nx)
                    \<longrightarrow> \<not> distance (targetnode a) n' (x - 1)\<close>
      note all = \<open>\<forall>as'. n -as'\<rightarrow>* n' \<longrightarrow> x \<le> length as'\<close>
      from \<open>n'' -as\<rightarrow>* n'\<close> obtain y where "distance n'' n' y"
        and "y \<le> length as" by(erule every_path_distance)
      from \<open>distance n'' n' y\<close> obtain as' where "n'' -as'\<rightarrow>* n'"
        and "y = length as'"
        by(auto elim:distance.cases)
      show False
      proof(cases "y < length as")
        case True
        from \<open>valid_edge a\<close> \<open>sourcenode a = n\<close> \<open>targetnode a = n''\<close> \<open>n'' -as'\<rightarrow>* n'\<close>
        have "n -a#as'\<rightarrow>* n'" by -(rule path.Cons_path)
        with all have "x \<le> length (a#as')" by blast
        with \<open>x = length (a#as)\<close> True \<open>y = length as'\<close> show False by simp
      next
        case False
        with \<open>y \<le> length as\<close> \<open>x = length (a#as)\<close> have "y = x - 1" by simp
        from \<open>targetnode a = n''\<close> \<open>distance n'' n' y\<close>
        have "distance (targetnode a) n' y" by simp
        with \<open>valid_edge a\<close>
        obtain a' where "sourcenode a = sourcenode a'"
          and "distance (targetnode a') n' y" and "valid_edge a'"
          and "targetnode a' = (SOME nx. \<exists>a'. sourcenode a = sourcenode a' \<and>
                                              distance (targetnode a') n' y \<and>
                                              valid_edge a' \<and> targetnode a' = nx)"
          by(auto dest:only_one_SOME_dist_edge)
        with imp \<open>sourcenode a = n\<close> \<open>y = x - 1\<close> show False by fastforce
      qed
    qed
  qed
  with that show ?thesis by blast
qed

end

end


