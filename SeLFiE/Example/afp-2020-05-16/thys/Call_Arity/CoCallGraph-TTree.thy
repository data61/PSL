theory "CoCallGraph-TTree"
imports CoCallGraph "TTree-HOLCF"
begin

lemma interleave_ccFromList:
  "xs \<in> interleave ys zs \<Longrightarrow> ccFromList xs = ccFromList ys \<squnion> ccFromList zs \<squnion> ccProd (set ys) (set zs)"
  by (induction rule: interleave_induct)
     (auto simp add: interleave_set ccProd_comm ccProd_insert2[where S' = "set xs" for xs]  ccProd_insert1[where S' = "set xs" for xs] )


lift_definition ccApprox :: "var ttree \<Rightarrow> CoCalls"
  is "\<lambda> xss .  lub (ccFromList ` xss)".

lemma ccApprox_paths: "ccApprox t = lub (ccFromList ` (paths t))" by transfer simp

lemma ccApprox_strict[simp]: "ccApprox \<bottom> = \<bottom>"
  by (simp add: ccApprox_paths empty_is_bottom[symmetric])

lemma in_ccApprox: "(x--y\<in>(ccApprox t)) \<longleftrightarrow> (\<exists> xs \<in> paths t. (x--y\<in>(ccFromList xs)))"
  unfolding ccApprox_paths
  by transfer auto

lemma ccApprox_mono: "paths t \<subseteq> paths t' \<Longrightarrow> ccApprox t \<sqsubseteq> ccApprox t'"
  by (rule below_CoCallsI) (auto simp add: in_ccApprox)

lemma ccApprox_mono': "t \<sqsubseteq>  t' \<Longrightarrow> ccApprox t \<sqsubseteq> ccApprox t'"
  by (metis below_set_def ccApprox_mono paths_mono_iff)

lemma ccApprox_belowI: "(\<And> xs. xs \<in> paths t \<Longrightarrow> ccFromList xs \<sqsubseteq> G) \<Longrightarrow> ccApprox t \<sqsubseteq> G"
  unfolding ccApprox_paths
  by transfer auto

lemma ccApprox_below_iff: "ccApprox t \<sqsubseteq> G \<longleftrightarrow> (\<forall> xs \<in> paths t. ccFromList xs \<sqsubseteq> G)"
  unfolding ccApprox_paths by transfer auto

lemma cc_restr_ccApprox_below_iff: "cc_restr S (ccApprox t) \<sqsubseteq> G \<longleftrightarrow> (\<forall> xs \<in> paths t. cc_restr S (ccFromList xs) \<sqsubseteq> G)"
  unfolding ccApprox_paths cc_restr_lub
  by transfer auto

lemma ccFromList_below_ccApprox:
  "xs \<in> paths t \<Longrightarrow> ccFromList xs \<sqsubseteq> ccApprox t" 
by (rule below_CoCallsI)(auto simp add: in_ccApprox)

lemma ccApprox_nxt_below:
  "ccApprox (nxt t x) \<sqsubseteq> ccApprox t"
by (rule below_CoCallsI)(auto simp add: in_ccApprox paths_nxt_eq elim!:  bexI[rotated])

lemma ccApprox_ttree_restr_nxt_below:
  "ccApprox (ttree_restr S (nxt t x)) \<sqsubseteq> ccApprox (ttree_restr S t)"
by (rule below_CoCallsI)
   (auto simp add: in_ccApprox filter_paths_conv_free_restr[symmetric] paths_nxt_eq  elim!:  bexI[rotated])

lemma ccApprox_ttree_restr[simp]: "ccApprox (ttree_restr S t) = cc_restr S (ccApprox t)"
  by (rule CoCalls_eqI) (auto simp add: in_ccApprox filter_paths_conv_free_restr[symmetric] )

lemma ccApprox_both: "ccApprox (t \<otimes>\<otimes> t') = ccApprox t \<squnion> ccApprox t' \<squnion> ccProd (carrier t) (carrier t')"
proof (rule below_antisym)
  show "ccApprox (t \<otimes>\<otimes> t') \<sqsubseteq> ccApprox t \<squnion> ccApprox t' \<squnion> ccProd (carrier t) (carrier t')"
  by (rule below_CoCallsI)
     (auto 4 4  simp add: in_ccApprox paths_both Union_paths_carrier[symmetric]  interleave_ccFromList)
next
  have "ccApprox t \<sqsubseteq> ccApprox (t \<otimes>\<otimes> t')"
    by (rule ccApprox_mono[OF both_contains_arg1])
  moreover
  have "ccApprox t' \<sqsubseteq> ccApprox (t \<otimes>\<otimes> t')"
    by (rule ccApprox_mono[OF both_contains_arg2])
  moreover
  have "ccProd (carrier t) (carrier t') \<sqsubseteq> ccApprox (t \<otimes>\<otimes> t')"
  proof(rule ccProd_belowI)
    fix x y
    assume "x \<in> carrier t" and "y \<in> carrier t'"
    then obtain xs ys where "x \<in> set xs" and "y \<in> set ys"
      and "xs \<in> paths t" and "ys \<in> paths t'" by (auto simp add: Union_paths_carrier[symmetric])
    hence "xs @ ys \<in> paths (t \<otimes>\<otimes> t')" by (metis paths_both append_interleave)
    moreover
    from \<open>x \<in> set xs\<close> \<open>y \<in> set ys\<close>
    have "x--y\<in>(ccFromList (xs@ys))" by simp
    ultimately
    show "x--y\<in>(ccApprox (t \<otimes>\<otimes> t'))" by (auto simp add: in_ccApprox simp del: ccFromList_append)
  qed
  ultimately
  show "ccApprox t \<squnion> ccApprox t' \<squnion> ccProd (carrier t) (carrier t') \<sqsubseteq> ccApprox (t \<otimes>\<otimes> t')"
    by (simp add: join_below_iff)
qed

lemma ccApprox_many_calls[simp]:
  "ccApprox (many_calls x) = ccProd {x} {x}"
  by transfer' (rule CoCalls_eqI, auto)

lemma ccApprox_single[simp]:
  "ccApprox (TTree.single y) = \<bottom>"
  by transfer' auto

lemma ccApprox_either[simp]: "ccApprox (t \<oplus>\<oplus> t') = ccApprox t \<squnion> ccApprox t'"
  by transfer' (rule CoCalls_eqI, auto)

(* could work, but tricky
lemma ccApprox_lub_nxt: "ccApprox t = (\<Squnion> x \<in>UNIV. ccApprox (nxt t x) \<squnion> (ccProd {x} (carrier (nxt t x))))"
*)

lemma wild_recursion:
  assumes "ccApprox  t \<sqsubseteq> G"
  assumes "\<And> x. x \<notin> S \<Longrightarrow> f x = empty"
  assumes "\<And> x. x \<in> S \<Longrightarrow> ccApprox (f x) \<sqsubseteq> G"
  assumes "\<And> x. x \<in> S \<Longrightarrow> ccProd (ccNeighbors x G) (carrier (f x)) \<sqsubseteq> G"
  shows "ccApprox (ttree_restr (-S) (substitute f T t)) \<sqsubseteq> G"
proof(rule ccApprox_belowI)
  fix xs
  define seen :: "var set" where "seen = {}"

  assume "xs \<in> paths (ttree_restr (- S) (substitute f T t))"
  then obtain xs' xs'' where "xs = [x\<leftarrow>xs' . x \<notin> S]" and "substitute'' f T xs'' xs'" and "xs'' \<in> paths t"
    by (auto simp add: filter_paths_conv_free_restr2[symmetric] substitute_substitute'')
 
  note this(2)
  moreover
  from \<open>ccApprox t \<sqsubseteq> G\<close> and \<open>xs'' \<in> paths t\<close>
  have  "ccFromList xs'' \<sqsubseteq> G"
    by (auto simp add: ccApprox_below_iff)
  moreover
  note assms(2)
  moreover
  from assms(3,4)
  have "\<And> x ys. x \<in> S \<Longrightarrow> ys \<in> paths (f x) \<Longrightarrow> ccFromList ys \<sqsubseteq> G"
    and "\<And> x ys. x \<in> S \<Longrightarrow> ys \<in> paths (f x) \<Longrightarrow> ccProd (ccNeighbors x G) (set ys) \<sqsubseteq> G"
    by (auto simp add: ccApprox_below_iff Union_paths_carrier[symmetric] cc_lub_below_iff)
  moreover
  have "ccProd seen (set xs'') \<sqsubseteq> G" unfolding seen_def by simp
  ultimately 
  have "ccFromList [x\<leftarrow>xs' . x \<notin> S] \<sqsubseteq> G \<and> ccProd (seen) (set xs') \<sqsubseteq> G"
  proof(induction f T xs'' xs' arbitrary: seen rule: substitute''.induct[case_names Nil Cons])
  case Nil thus ?case by simp
  next
  case (Cons zs f x xs' xs T ys)
    
    have seen_x: "ccProd seen {x} \<sqsubseteq> G"
      using \<open>ccProd seen (set (x # xs)) \<sqsubseteq> G\<close>
      by (auto simp add: ccProd_insert2[where S' = "set xs" for xs] join_below_iff)

    show ?case
    proof(cases "x \<in> S")
      case True

      from \<open>ccFromList (x # xs) \<sqsubseteq> G\<close>
      have "ccProd {x} (set xs) \<sqsubseteq> G" by (auto simp add: join_below_iff)
      hence subset1: "set xs \<subseteq> ccNeighbors x G" by transfer auto

      from \<open>ccProd seen (set (x # xs)) \<sqsubseteq> G\<close>
      have subset2: "seen  \<subseteq> ccNeighbors x G"
        by (auto simp add: subset_ccNeighbors ccProd_insert2[where S' = "set xs" for xs] join_below_iff ccProd_comm)

      from subset1 and subset2
      have "seen \<union> set xs \<subseteq> ccNeighbors x G" by auto
      hence "ccProd (seen \<union> set xs) (set zs) \<sqsubseteq> ccProd (ccNeighbors x G) (set zs)"
        by (rule ccProd_mono1)
      also
      from \<open>x \<in> S\<close>  \<open>zs \<in> paths (f x)\<close>
      have "\<dots> \<sqsubseteq> G"
        by (rule Cons.prems(4))
      finally
      have "ccProd (seen \<union> set xs) (set zs) \<sqsubseteq> G" by this simp
     
      with \<open>x \<in> S\<close> Cons.prems Cons.hyps
      have "ccFromList [x\<leftarrow>ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd (seen) (set ys) \<sqsubseteq> G"
          apply -
          apply (rule Cons.IH)
          apply (auto simp add: f_nxt_def  join_below_iff  interleave_ccFromList interleave_set  ccProd_insert2[where S' = "set xs" for xs]
                  split: if_splits)
          done
      with  \<open>x \<in> S\<close>  seen_x
      show "ccFromList [x\<leftarrow>x # ys . x \<notin> S] \<sqsubseteq> G  \<and> ccProd seen (set (x#ys)) \<sqsubseteq> G" 
          by (auto simp add: ccProd_insert2[where S' = "set xs" for xs] join_below_iff)
    next
      case False

      from False Cons.prems Cons.hyps
      have *: "ccFromList [x\<leftarrow>ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd ((insert x seen)) (set ys) \<sqsubseteq> G"
        apply -
        apply (rule Cons.IH[where seen = "insert x seen"])
        apply (auto simp add: ccApprox_both join_below_iff ttree_restr_both interleave_ccFromList insert_Diff_if
                   simp add:  ccProd_insert2[where S' = "set xs" for xs]
                   simp add:  ccProd_insert1[where S' = "seen"])
        done
      moreover
      from False *
      have "ccProd {x} (set ys) \<sqsubseteq>  G"
        by (auto simp add: insert_Diff_if ccProd_insert1[where S' = "seen"] join_below_iff)
      hence "ccProd {x} {x \<in> set ys. x \<notin> S} \<sqsubseteq> G"
        by (rule below_trans[rotated, OF _ ccProd_mono2]) auto
      moreover
      note False seen_x
      ultimately
      show "ccFromList [x\<leftarrow>x # ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd (seen) (set (x # ys)) \<sqsubseteq> G"
        by (auto simp add: join_below_iff  simp add: insert_Diff_if  ccProd_insert2[where S' = "set xs" for xs]   ccProd_insert1[where S' = "seen"])
    qed
  qed
  with \<open>xs = _\<close>
  show "ccFromList xs \<sqsubseteq> G" by simp
qed

lemma wild_recursion_thunked:
  assumes "ccApprox  t \<sqsubseteq> G"
  assumes "\<And> x. x \<notin> S \<Longrightarrow> f x = empty"
  assumes "\<And> x. x \<in> S \<Longrightarrow> ccApprox (f x) \<sqsubseteq> G"
  assumes "\<And> x. x \<in> S \<Longrightarrow> ccProd (ccNeighbors x G - {x} \<inter> T) (carrier (f x)) \<sqsubseteq> G"
  shows "ccApprox (ttree_restr (-S) (substitute f T t)) \<sqsubseteq> G"
proof(rule ccApprox_belowI)
  fix xs

  define seen :: "var set" where "seen = {}"
  define seen_T :: "var set" where "seen_T = {}"

  assume "xs \<in> paths (ttree_restr (- S) (substitute f T t))"
  then obtain xs' xs'' where "xs = [x\<leftarrow>xs' . x \<notin> S]" and "substitute'' f T xs'' xs'" and "xs'' \<in> paths t"
    by (auto simp add: filter_paths_conv_free_restr2[symmetric] substitute_substitute'')
 
  note this(2)
  moreover
  from \<open>ccApprox t \<sqsubseteq> G\<close> and \<open>xs'' \<in> paths t\<close>
  have  "ccFromList xs'' \<sqsubseteq> G"
    by (auto simp add: ccApprox_below_iff)
  hence  "ccFromList xs'' G|` (- seen_T) \<sqsubseteq> G"
    by (rule rev_below_trans[OF _ cc_restr_below_arg])
  moreover
  note assms(2)
  moreover
  from assms(3,4)
  have "\<And> x ys. x \<in> S \<Longrightarrow> ys \<in> paths (f x) \<Longrightarrow> ccFromList ys \<sqsubseteq> G"
    and "\<And> x ys. x \<in> S \<Longrightarrow> ys \<in> paths (f x) \<Longrightarrow> ccProd (ccNeighbors x G - {x} \<inter> T) (set ys) \<sqsubseteq> G"
    by (auto simp add: ccApprox_below_iff seen_T_def Union_paths_carrier[symmetric] cc_lub_below_iff)
  moreover
  have "ccProd seen (set xs'' - seen_T) \<sqsubseteq> G" unfolding seen_def seen_T_def by simp
  moreover
  have "seen \<inter> S = {}" unfolding seen_def by simp
  moreover
  have "seen_T \<subseteq> S" unfolding seen_T_def by simp
  moreover
  have "\<And> x. x \<in> seen_T \<Longrightarrow> f x = empty"  unfolding seen_T_def by simp
  ultimately 
  have "ccFromList [x\<leftarrow>xs' . x \<notin> S] \<sqsubseteq> G \<and> ccProd (seen) (set xs' - seen_T) \<sqsubseteq> G"
  proof(induction f T xs'' xs' arbitrary: seen seen_T rule: substitute''.induct[case_names Nil Cons])
  case Nil thus ?case by simp
  next
  case (Cons zs f x xs' xs T ys)

    let  ?seen_T = "if x \<in> T then insert x seen_T else seen_T"
    have subset: "- insert x seen_T \<subseteq> - seen_T" by auto
    have subset2: "set xs \<inter> - insert x seen_T \<subseteq> insert x (set xs) \<inter> - seen_T" by auto
    have subset3: "set zs \<inter> - insert x seen_T \<subseteq> set zs" by auto
    have subset4: "set xs \<inter> - seen_T \<subseteq> insert x (set xs) \<inter> - seen_T" by auto
    have subset5: "set zs \<inter> - seen_T \<subseteq> set zs" by auto
    have subset6: "set ys - seen_T \<subseteq> (set ys - ?seen_T) \<union> {x}" by auto

    show ?case
    proof(cases "x \<in> seen_T")
      assume "x \<in> seen_T"
      
      have [simp]: "f x = empty" using \<open>x \<in> seen_T\<close> Cons.prems by auto
      have [simp]: "f_nxt f T x = f" by (auto simp add: f_nxt_def split:if_splits)
      have [simp]: "zs = []" using \<open>zs \<in> paths (f x)\<close> by simp
      have [simp]: "xs' = xs" using \<open>xs' \<in> xs \<otimes> zs\<close> by simp
      have [simp]: "x \<in> S" using \<open>x \<in> seen_T\<close> Cons.prems by auto

      from Cons.hyps Cons.prems
      have "ccFromList [x\<leftarrow>ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd seen (set ys - seen_T) \<sqsubseteq> G"
        apply -
        apply (rule Cons.IH[where seen_T = seen_T])
        apply (auto simp add: join_below_iff Diff_eq)
        apply (erule below_trans[OF ccProd_mono[OF order_refl subset4]])
        done
      thus ?thesis using \<open>x \<in> seen_T\<close> by simp
    next
      assume "x \<notin> seen_T"

      have seen_x: "ccProd seen {x} \<sqsubseteq> G"
        using \<open>ccProd seen (set (x # xs) - seen_T) \<sqsubseteq> G\<close> \<open>x \<notin> seen_T\<close>
        by (auto simp add: insert_Diff_if ccProd_insert2[where S' = "set xs - seen_T" for xs] join_below_iff)
  
      show ?case
      proof(cases "x \<in> S")
        case True
  
        from \<open>cc_restr (- seen_T) (ccFromList (x # xs)) \<sqsubseteq> G\<close>
        have "ccProd {x} (set xs - seen_T) \<sqsubseteq> G" using \<open>x \<notin> seen_T\<close>  by (auto simp add: join_below_iff Diff_eq)
        hence "set xs - seen_T \<subseteq> ccNeighbors x G" by transfer auto
        moreover
        
        from seen_x
        have "seen  \<subseteq> ccNeighbors x G" by (simp add: subset_ccNeighbors   ccProd_comm)
        moreover
        have "x \<notin> seen" using True \<open>seen \<inter> S = {}\<close> by auto
  
        ultimately
        have "seen \<union> (set xs \<inter> - ?seen_T) \<subseteq> ccNeighbors x G - {x}\<inter>T" by auto
        hence "ccProd (seen \<union> (set xs \<inter> - ?seen_T)) (set zs) \<sqsubseteq> ccProd (ccNeighbors x G - {x}\<inter>T) (set zs)"
          by (rule ccProd_mono1)
        also
        from \<open>x \<in> S\<close>  \<open>zs \<in> paths (f x)\<close>
        have "\<dots> \<sqsubseteq> G"
          by (rule Cons.prems(4))
        finally
        have "ccProd (seen \<union> (set xs \<inter> - ?seen_T)) (set zs) \<sqsubseteq> G" by this simp
  
        with \<open>x \<in> S\<close> Cons.prems Cons.hyps(1,2)
        have "ccFromList [x\<leftarrow>ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd (seen) (set ys - ?seen_T) \<sqsubseteq> G"
            apply -
            apply (rule Cons.IH[where seen_T = "?seen_T"])
            apply (auto simp add: Un_Diff Int_Un_distrib2 Diff_eq f_nxt_def  join_below_iff  interleave_ccFromList interleave_set  ccProd_insert2[where S' = "set xs" for xs]
                    split: if_splits)
            apply (erule below_trans[OF cc_restr_mono1[OF subset]])
            apply (rule below_trans[OF cc_restr_below_arg], simp)
            apply (erule below_trans[OF ccProd_mono[OF order_refl Int_lower1]])
            apply (rule below_trans[OF cc_restr_below_arg], simp)
            apply (erule below_trans[OF ccProd_mono[OF order_refl Int_lower1]])
            apply (erule below_trans[OF ccProd_mono[OF order_refl subset2]])
            apply (erule below_trans[OF ccProd_mono[OF order_refl subset3]])
            apply (erule below_trans[OF ccProd_mono[OF order_refl subset4]])
            apply (erule below_trans[OF ccProd_mono[OF order_refl subset5]])
            done
        with  \<open>x \<in> S\<close>  seen_x \<open>x \<notin> seen_T\<close>
        show "ccFromList [x\<leftarrow>x # ys . x \<notin> S] \<sqsubseteq> G  \<and> ccProd seen (set (x#ys) - seen_T) \<sqsubseteq> G" 
            apply (auto simp add: insert_Diff_if ccProd_insert2[where S' = "set ys - seen_T" for xs] join_below_iff)
            apply (rule below_trans[OF ccProd_mono[OF order_refl subset6]])
            apply (subst ccProd_union2)
            apply (auto simp add: join_below_iff)
            done
      next
        case False
  
        from False Cons.prems Cons.hyps
        have *: "ccFromList [x\<leftarrow>ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd ((insert x seen)) (set ys - seen_T) \<sqsubseteq> G"
          apply -
          apply (rule Cons.IH[where seen = "insert x seen" and seen_T = seen_T])
          apply (auto simp add: \<open>x \<notin> seen_T\<close> Diff_eq ccApprox_both join_below_iff ttree_restr_both interleave_ccFromList insert_Diff_if
                     simp add:  ccProd_insert2[where S' = "set xs \<inter> - seen_T" for xs]
                     simp add:  ccProd_insert1[where S' = "seen"])
          done
        moreover
        {
        from False *
        have "ccProd {x} (set ys - seen_T) \<sqsubseteq>  G"
          by (auto simp add: insert_Diff_if ccProd_insert1[where S' = "seen"] join_below_iff)
        hence "ccProd {x} {x \<in> set ys - seen_T. x \<notin> S} \<sqsubseteq> G"
          by (rule below_trans[rotated, OF _ ccProd_mono2]) auto
        also have "{x \<in> set ys - seen_T. x \<notin> S} =  {x \<in> set ys. x \<notin> S}"
          using \<open>seen_T \<subseteq> S\<close> by auto
        finally
        have "ccProd {x} {x \<in> set ys. x \<notin> S} \<sqsubseteq> G".
        }
        moreover
        note False seen_x
        ultimately
        show "ccFromList [x\<leftarrow>x # ys . x \<notin> S] \<sqsubseteq> G \<and> ccProd (seen) (set (x # ys) - seen_T) \<sqsubseteq> G"
          by (auto simp add: join_below_iff  simp add: insert_Diff_if  ccProd_insert2[where S' = "set ys - seen_T" for xs]   ccProd_insert1[where S' = "seen"])
      qed
    qed
  qed
  with \<open>xs = _\<close>
  show "ccFromList xs \<sqsubseteq> G" by simp
qed


inductive_set valid_lists :: "var set \<Rightarrow> CoCalls \<Rightarrow> var list set"
  for S G
  where  "[] \<in> valid_lists S G"
  | "set xs \<subseteq> ccNeighbors x G \<Longrightarrow> xs \<in> valid_lists S G \<Longrightarrow> x \<in> S \<Longrightarrow> x#xs \<in> valid_lists S G"

inductive_simps valid_lists_simps[simp]: "[] \<in> valid_lists S G" "(x#xs) \<in> valid_lists S G"
inductive_cases vald_lists_ConsE: "(x#xs) \<in> valid_lists S G"

lemma  valid_lists_downset_aux:
  "xs \<in> valid_lists S CoCalls \<Longrightarrow> butlast xs \<in> valid_lists S CoCalls"
  by (induction xs) (auto dest: in_set_butlastD)

lemma valid_lists_subset: "xs \<in> valid_lists S G \<Longrightarrow> set xs \<subseteq> S"
  by (induction rule: valid_lists.induct) auto

lemma valid_lists_mono1:
  assumes "S \<subseteq> S'"
  shows "valid_lists S G \<subseteq> valid_lists S' G"
proof
  fix xs
  assume "xs \<in> valid_lists S G"
  thus "xs \<in> valid_lists S' G"
    by (induction rule: valid_lists.induct) (auto dest: subsetD[OF assms])
qed

lemma valid_lists_chain1:
   assumes "chain Y" 
   assumes "xs \<in> valid_lists (\<Union>(Y ` UNIV)) G"
   shows "\<exists> i. xs \<in> valid_lists (Y i) G"
proof-
  note \<open>chain Y\<close>
  moreover
  from assms(2)
  have "set xs \<subseteq> \<Union>(Y ` UNIV)" by (rule valid_lists_subset)
  moreover
  have "finite (set xs)" by simp
  ultimately
  have "\<exists>i. set xs \<subseteq> Y i" by (rule finite_subset_chain)
  then obtain i where "set xs \<subseteq> Y i"..

  from assms(2) this
  have "xs \<in> valid_lists (Y i) G" by (induction rule:valid_lists.induct) auto
  thus ?thesis..
qed

lemma valid_lists_chain2:
   assumes "chain Y" 
   assumes "xs \<in> valid_lists S (\<Squnion>i. Y i)"
   shows "\<exists> i. xs \<in> valid_lists S  (Y i)"
using assms(2)
proof(induction rule:valid_lists.induct[case_names Nil Cons])
  case Nil thus ?case by simp
next
  case (Cons xs x)

  from \<open>chain Y\<close>
  have "chain (\<lambda> i. ccNeighbors x (Y i))"
    apply (rule ch2ch_monofun[OF monofunI, rotated])
    unfolding below_set_def
    by (rule ccNeighbors_mono)
  moreover
  from \<open>set xs \<subseteq> ccNeighbors x (\<Squnion> i. Y i)\<close>
  have "set xs \<subseteq> (\<Union> i. ccNeighbors x (Y i))"
    by (simp add:  lub_set)
  moreover
  have "finite (set xs)" by simp
  ultimately
  have "\<exists>i. set xs \<subseteq> ccNeighbors x (Y i)" by (rule finite_subset_chain)
  then obtain i where i: "set xs \<subseteq> ccNeighbors x (Y i)"..

  from Cons.IH
  obtain j where j: "xs \<in> valid_lists S (Y j)"..

  from i
  have "set xs \<subseteq> ccNeighbors x (Y (max i j))"
    by (rule order_trans[OF _ ccNeighbors_mono[OF chain_mono[OF \<open>chain Y\<close> max.cobounded1]]])
  moreover
  from j
  have "xs \<in> valid_lists S (Y (max i j))" 
    by (induction rule: valid_lists.induct)
       (auto del: subsetI elim: order_trans[OF _ ccNeighbors_mono[OF chain_mono[OF \<open>chain Y\<close> max.cobounded2]]])
  moreover
  note \<open>x \<in> S\<close>
  ultimately
  have "x # xs \<in> valid_lists S (Y (max i j))" by rule
  thus ?case..
qed

lemma valid_lists_cc_restr: "valid_lists S G = valid_lists S (cc_restr S G)"
proof(rule set_eqI)
  fix xs
  show "(xs \<in> valid_lists S G) = (xs \<in> valid_lists S (cc_restr S G))"
    by (induction xs) (auto dest: subsetD[OF valid_lists_subset])
qed

lemma interleave_valid_list:
  "xs \<in> ys \<otimes> zs \<Longrightarrow> ys \<in> valid_lists S G \<Longrightarrow> zs \<in> valid_lists S' G' \<Longrightarrow> xs \<in> valid_lists (S \<union> S') (G \<squnion> (G' \<squnion> ccProd S S'))"
proof (induction rule:interleave_induct)
  case Nil
  show ?case by simp
next
  case (left ys zs xs x)

  from \<open>x # ys \<in> valid_lists S G\<close>
  have "x \<in> S" and "set ys \<subseteq> ccNeighbors x G" and "ys \<in> valid_lists S G"
    by auto
 
  from \<open>xs \<in> ys \<otimes> zs\<close>
  have "set xs = set ys \<union> set zs" by (rule interleave_set)
  with \<open>set ys \<subseteq> ccNeighbors x G\<close> valid_lists_subset[OF \<open>zs \<in> valid_lists S' G'\<close>]
  have "set xs \<subseteq> ccNeighbors x (G \<squnion> (G' \<squnion> ccProd S S'))"
    by (auto simp add: ccNeighbors_ccProd \<open>x \<in> S\<close>)
  moreover
  from \<open>ys \<in> valid_lists S G\<close> \<open>zs \<in> valid_lists S' G'\<close>
  have "xs \<in> valid_lists (S \<union> S') (G \<squnion> (G' \<squnion> ccProd S S'))"
    by (rule left.IH)
  moreover
  from \<open>x \<in> S\<close>
  have "x \<in> S \<union> S'" by simp
  ultimately
  show ?case..
next
  case (right ys zs xs x)

  from \<open>x # zs \<in> valid_lists S' G'\<close>
  have "x \<in> S'" and "set zs \<subseteq> ccNeighbors x G'" and "zs \<in> valid_lists S' G'"
    by auto
 
  from \<open>xs \<in> ys \<otimes> zs\<close>
  have "set xs = set ys \<union> set zs" by (rule interleave_set)
  with \<open>set zs \<subseteq> ccNeighbors x G'\<close> valid_lists_subset[OF \<open>ys \<in> valid_lists S G\<close>]
  have "set xs \<subseteq> ccNeighbors x (G \<squnion> (G' \<squnion> ccProd S S'))"
    by (auto simp add: ccNeighbors_ccProd \<open>x \<in> S'\<close>)
  moreover
  from \<open>ys \<in> valid_lists S G\<close> \<open>zs \<in> valid_lists S' G'\<close>
  have "xs \<in> valid_lists (S \<union> S') (G \<squnion> (G' \<squnion> ccProd S S'))"
    by (rule right.IH)
  moreover
  from \<open>x \<in> S'\<close>
  have "x \<in> S \<union> S'" by simp
  ultimately
  show ?case..
qed

lemma interleave_valid_list':
  "xs \<in> valid_lists (S \<union> S') G \<Longrightarrow> \<exists> ys zs. xs \<in> ys \<otimes> zs \<and> ys \<in> valid_lists S G \<and> zs \<in> valid_lists S' G"
proof(induction rule: valid_lists.induct[case_names Nil Cons])
  case Nil show ?case by simp
next
  case (Cons xs x)
  then obtain ys zs where "xs \<in> ys \<otimes> zs" "ys \<in> valid_lists S G" "zs \<in> valid_lists S' G" by auto

    from \<open>xs \<in> ys \<otimes> zs\<close> have "set xs = set ys \<union> set zs" by (rule interleave_set)
    with \<open>set xs \<subseteq> ccNeighbors x G\<close> 
    have "set ys \<subseteq> ccNeighbors x G" and "set zs \<subseteq> ccNeighbors x G"  by auto
  
  from \<open>x \<in> S \<union> S'\<close>
  show ?case
  proof
    assume "x \<in> S"
    with \<open>set ys \<subseteq> ccNeighbors x G\<close> \<open>ys \<in> valid_lists S G\<close>
    have "x # ys \<in> valid_lists S G"
      by rule
    moreover
    from \<open>xs \<in> ys \<otimes> zs\<close>
    have "x#xs \<in> x#ys \<otimes> zs"..
    ultimately
    show ?thesis using \<open>zs \<in> valid_lists S' G\<close> by blast
  next
    assume "x \<in> S'"
    with \<open>set zs \<subseteq> ccNeighbors x G\<close> \<open>zs \<in> valid_lists S' G\<close>
    have "x # zs \<in> valid_lists S' G"
      by rule
    moreover
    from \<open>xs \<in> ys \<otimes> zs\<close>
    have "x#xs \<in> ys \<otimes> x#zs"..
    ultimately
    show ?thesis using \<open>ys \<in> valid_lists S G\<close> by blast
  qed
qed

lemma many_calls_valid_list:
  "xs \<in> valid_lists {x} (ccProd {x} {x}) \<Longrightarrow> xs \<in> range (\<lambda>n. replicate n x)"
  by (induction rule: valid_lists.induct) (auto, metis UNIV_I image_iff replicate_Suc)

lemma filter_valid_lists:
  "xs \<in> valid_lists S G \<Longrightarrow> filter P xs \<in> valid_lists {a \<in> S. P a} G"
by (induction rule:valid_lists.induct) auto

lift_definition ccTTree :: "var set \<Rightarrow> CoCalls \<Rightarrow> var ttree" is "\<lambda> S G. valid_lists S G" 
  by (auto intro: valid_lists_downset_aux)

lemma paths_ccTTree[simp]: "paths (ccTTree S G) = valid_lists S G" by transfer auto

lemma carrier_ccTTree[simp]: "carrier (ccTTree S G) = S"
  apply transfer
  apply (auto dest: valid_lists_subset)
  apply (rule_tac x = "[x]" in bexI)
  apply auto
  done

lemma valid_lists_ccFromList:
  "xs \<in> valid_lists S G \<Longrightarrow> ccFromList xs \<sqsubseteq> cc_restr S G"
by (induction rule:valid_lists.induct)
   (auto simp add: join_below_iff subset_ccNeighbors ccProd_below_cc_restr elim: subsetD[OF valid_lists_subset])

lemma ccApprox_ccTTree[simp]: "ccApprox (ccTTree S G) = cc_restr S G"
proof (transfer' fixing: S G, rule below_antisym)
  show "lub (ccFromList ` valid_lists S G) \<sqsubseteq> cc_restr S G"
    apply (rule is_lub_thelub_ex)
    apply (metis coCallsLub_is_lub)
    apply (rule is_ubI)
    apply clarify
    apply (erule valid_lists_ccFromList)
    done
next
  show "cc_restr S G \<sqsubseteq> lub (ccFromList ` valid_lists S G)"
  proof (rule below_CoCallsI)
    fix x y
    have "x--y\<in>(ccFromList [y,x])" by simp
    moreover
    assume "x--y\<in>(cc_restr S G)"
    hence "[y,x] \<in> valid_lists S G"  by (auto simp add: elem_ccNeighbors)
    ultimately
    show "x--y\<in>(lub (ccFromList ` valid_lists S G))"
      by (rule in_CoCallsLubI[OF _ imageI])
  qed
qed

lemma below_ccTTreeI:
  assumes "carrier t \<subseteq> S" and "ccApprox t \<sqsubseteq> G"
  shows "t \<sqsubseteq> ccTTree S G"
unfolding paths_mono_iff[symmetric] below_set_def
proof
  fix xs
  assume "xs \<in> paths t"
  with assms
  have "xs \<in> valid_lists S G"
  proof(induction xs arbitrary : t)
  case Nil thus ?case by simp
  next
  case (Cons x xs)
    from \<open>x # xs \<in> paths t\<close>
    have "possible t x" and "xs \<in> paths (nxt t x)" by (auto simp add: Cons_path)

    have "ccProd {x} (set xs) \<sqsubseteq> ccFromList (x # xs)" by simp
    also
    from \<open>x # xs \<in> paths t\<close> 
    have "\<dots> \<sqsubseteq> ccApprox t"
      by (rule ccFromList_below_ccApprox)
    also
    note \<open>ccApprox t \<sqsubseteq> G\<close>
    finally
    have "ccProd {x} (set xs) \<sqsubseteq> G" by this simp_all
    hence "set xs \<subseteq> ccNeighbors x G" unfolding subset_ccNeighbors.
    moreover
    have "xs \<in> valid_lists S G"
    proof(rule Cons.IH)
      show "xs \<in> paths (nxt t x)" by fact
    next
      from \<open>carrier t \<subseteq> S\<close>
      show "carrier (nxt t x) \<subseteq> S" 
        by (rule order_trans[OF carrier_nxt_subset])
    next
      from \<open>ccApprox t \<sqsubseteq> G\<close>
      show "ccApprox (nxt t x) \<sqsubseteq> G" 
        by (rule below_trans[OF ccApprox_nxt_below])
    qed
    moreover
    from  \<open>carrier t \<subseteq> S\<close> and \<open>possible t x\<close>
    have "x \<in> S" by (rule carrier_possible_subset)
    ultimately
    show ?case..
  qed
    
  thus "xs \<in> paths (ccTTree S G)" by (metis paths_ccTTree)
qed    

lemma ccTTree_mono1:
  "S \<subseteq> S' \<Longrightarrow> ccTTree S G \<sqsubseteq> ccTTree S' G"
  by (rule below_ccTTreeI) (auto simp add:  cc_restr_below_arg)

lemma cont_ccTTree1:
  "cont (\<lambda> S. ccTTree S G)"
  apply (rule contI2)
  apply (rule monofunI)
  apply (erule ccTTree_mono1[folded below_set_def])
  
  apply (rule ttree_belowI)
  apply (simp add: paths_Either lub_set lub_is_either)
  apply (drule (1) valid_lists_chain1[rotated])
  apply simp
  done

lemma ccTTree_mono2:
  "G \<sqsubseteq> G' \<Longrightarrow> ccTTree S G \<sqsubseteq> ccTTree S G'"
  apply (rule ttree_belowI)
  apply simp
  apply (induct_tac  rule:valid_lists.induct) apply assumption
  apply simp
  apply simp
  apply (erule (1) order_trans[OF _ ccNeighbors_mono])
  done

lemma ccTTree_mono:
  "S \<subseteq> S' \<Longrightarrow> G \<sqsubseteq> G' \<Longrightarrow> ccTTree S G \<sqsubseteq> ccTTree S' G'"
  by (metis below_trans[OF ccTTree_mono1 ccTTree_mono2])


lemma cont_ccTTree2:
  "cont (ccTTree S)"
  apply (rule contI2)
  apply (rule monofunI)
  apply (erule ccTTree_mono2)

  apply (rule ttree_belowI)
  apply (simp add: paths_Either lub_set lub_is_either)
  apply (drule (1) valid_lists_chain2)
  apply simp
  done

lemmas cont_ccTTree = cont_compose2[where c = ccTTree, OF cont_ccTTree1 cont_ccTTree2, simp, cont2cont]

lemma ccTTree_below_singleI:
  assumes "S \<inter> S' = {}"
  shows "ccTTree S G \<sqsubseteq> singles S'"
proof-
  {
  fix xs x
  assume "xs \<in> valid_lists S G" and "x \<in> S'"
  from this assms
  have "length [x'\<leftarrow>xs . x' = x] \<le> Suc 0"
  by(induction rule: valid_lists.induct[case_names Nil Cons]) auto
  }
  thus ?thesis by transfer auto
qed


lemma ccTTree_cc_restr: "ccTTree S G = ccTTree S (cc_restr S G)"
  by transfer' (rule valid_lists_cc_restr)

lemma ccTTree_cong_below: "cc_restr S G \<sqsubseteq> cc_restr S G' \<Longrightarrow> ccTTree S G \<sqsubseteq> ccTTree S G'"
  by (metis ccTTree_mono2 ccTTree_cc_restr)
  
lemma ccTTree_cong: "cc_restr S G = cc_restr S G' \<Longrightarrow> ccTTree S G = ccTTree S G'"
  by (metis ccTTree_cc_restr)

lemma either_ccTTree:
  "ccTTree S G \<oplus>\<oplus> ccTTree S' G' \<sqsubseteq> ccTTree (S \<union> S') (G \<squnion> G')"
  by (auto intro!: either_belowI ccTTree_mono)
 

lemma interleave_ccTTree: 
   "ccTTree S G \<otimes>\<otimes> ccTTree S' G' \<sqsubseteq> ccTTree (S \<union> S') (G \<squnion> G' \<squnion> ccProd S S')"
   by transfer' (auto, erule (2) interleave_valid_list)

lemma interleave_ccTTree': 
   "ccTTree (S \<union> S') G \<sqsubseteq> ccTTree S G \<otimes>\<otimes> ccTTree S' G"
   by transfer' (auto dest!:  interleave_valid_list')

lemma many_calls_ccTTree:
  shows "many_calls x = ccTTree {x} (ccProd {x} {x})"
  apply(transfer')
  apply (auto intro: many_calls_valid_list)
  apply (induct_tac n)
  apply (auto simp add: ccNeighbors_ccProd)
  done

lemma filter_valid_lists':
  "xs \<in> valid_lists {x' \<in> S. P x'} G \<Longrightarrow> xs \<in> filter P ` valid_lists S G"
proof (induction xs )
  case Nil thus ?case by auto  (metis filter.simps(1) image_iff valid_lists_simps(1))
next
  case (Cons x xs)
  from Cons.prems
  have "set xs \<subseteq> ccNeighbors x G" and "xs \<in> valid_lists {x' \<in> S. P x'} G" and "x \<in> S" and "P x" by auto

  from this(2) have "set xs \<subseteq> {x' \<in> S. P x'}" by (rule valid_lists_subset)
  hence "\<forall>x \<in> set xs. P x" by auto
  hence [simp]: "filter P xs = xs" by (rule filter_True)
  
  from Cons.IH[OF \<open>xs \<in> _\<close>]
  have "xs \<in> filter P ` valid_lists S G".

  from  \<open>xs \<in> valid_lists {x' \<in> S. P x'} G\<close>
  have "xs \<in> valid_lists S G" by (rule subsetD[OF valid_lists_mono1, rotated]) auto

  from \<open>set xs \<subseteq> ccNeighbors x G\<close> this \<open>x \<in> S\<close>
  have "x # xs \<in> valid_lists S G" by rule

  hence "filter P (x # xs) \<in> filter P ` valid_lists S G" by (rule imageI)
  thus ?case using \<open>P x\<close> \<open>filter P xs =xs\<close> by simp
qed

lemma without_ccTTree[simp]:
   "without x (ccTTree S G) = ccTTree (S - {x}) G"
by (transfer' fixing: x) (auto dest: filter_valid_lists'  filter_valid_lists[where P = "(\<lambda> x'. x'\<noteq> x)"]  simp add: set_diff_eq)

lemma ttree_restr_ccTTree[simp]:
   "ttree_restr S' (ccTTree S G) = ccTTree (S \<inter> S') G"
by (transfer' fixing: S') (auto dest: filter_valid_lists'  filter_valid_lists[where P = "(\<lambda> x'. x' \<in> S')"]  simp add:Int_def)

lemma repeatable_ccTTree_ccSquare: "S \<subseteq> S' \<Longrightarrow> repeatable (ccTTree S (ccSquare S'))"
   unfolding repeatable_def
   by transfer (auto simp add:ccNeighbors_ccSquare dest: subsetD[OF valid_lists_subset])


text \<open>An alternative definition\<close>

inductive valid_lists' :: "var set \<Rightarrow> CoCalls \<Rightarrow> var set \<Rightarrow> var list \<Rightarrow> bool"
  for S G
  where  "valid_lists' S G prefix []"
  | "prefix \<subseteq> ccNeighbors x G \<Longrightarrow> valid_lists' S G (insert x prefix) xs \<Longrightarrow> x \<in> S \<Longrightarrow> valid_lists' S G prefix (x#xs)"

inductive_simps valid_lists'_simps[simp]: "valid_lists' S G prefix []" "valid_lists' S G prefix (x#xs)"
inductive_cases vald_lists'_ConsE: "valid_lists' S G prefix (x#xs)"

lemma valid_lists_valid_lists':
  "xs \<in> valid_lists S G \<Longrightarrow> ccProd prefix (set xs) \<sqsubseteq> G \<Longrightarrow> valid_lists' S G prefix xs"
proof(induction arbitrary: prefix rule: valid_lists.induct[case_names Nil Cons])
  case Nil thus ?case by simp
next
  case (Cons xs x)

  from Cons.prems Cons.hyps Cons.IH[where prefix = "insert x prefix"]
  show ?case
  by (auto simp add: insert_is_Un[where A = "set xs"]  insert_is_Un[where A = prefix]
                     join_below_iff subset_ccNeighbors elem_ccNeighbors ccProd_comm simp del: Un_insert_left )
qed

lemma valid_lists'_valid_lists_aux:
  "valid_lists' S G prefix xs \<Longrightarrow>  x \<in> prefix \<Longrightarrow> ccProd (set xs) {x} \<sqsubseteq> G"
proof(induction  rule: valid_lists'.induct[case_names Nil Cons])
  case Nil thus ?case by simp
next
  case (Cons prefix x xs)
  thus ?case
    apply (auto simp add: ccProd_insert2[where S' = prefix] ccProd_insert1[where S' = "set xs"] join_below_iff subset_ccNeighbors)
    by (metis Cons.hyps(1) dual_order.trans empty_subsetI insert_subset subset_ccNeighbors)
qed

lemma valid_lists'_valid_lists:
  "valid_lists' S G prefix xs \<Longrightarrow> xs \<in> valid_lists S G"
proof(induction  rule: valid_lists'.induct[case_names Nil Cons])
  case Nil thus ?case by simp
next
  case (Cons prefix x xs)
  thus ?case
    by (auto simp add: insert_is_Un[where A = "set xs"]  insert_is_Un[where A = prefix]
                   join_below_iff subset_ccNeighbors elem_ccNeighbors ccProd_comm simp del: Un_insert_left 
         intro: valid_lists'_valid_lists_aux)
qed

text \<open>Yet another definition\<close>

lemma valid_lists_characterization:
  "xs \<in> valid_lists S G \<longleftrightarrow> set xs \<subseteq> S \<and> (\<forall>n. ccProd (set (take n xs)) (set (drop n xs)) \<sqsubseteq> G)"
proof(safe)
  fix x
  assume "xs \<in> valid_lists S G"
  from  valid_lists_subset[OF this]
  show "x \<in> set xs \<Longrightarrow> x \<in> S" by auto
next
  fix n
  assume "xs \<in> valid_lists S G"
  thus "ccProd (set (take n xs)) (set (drop n xs)) \<sqsubseteq> G"
  proof(induction arbitrary: n rule: valid_lists.induct[case_names Nil Cons])
    case Nil thus ?case by simp
  next
    case (Cons xs x)
    show ?case
    proof(cases n)
      case 0 thus ?thesis by simp
    next
      case (Suc n)
      with Cons.hyps Cons.IH[where n = n]
      show ?thesis
      apply (auto simp add: ccProd_insert1[where S' = "set xs" for xs] join_below_iff subset_ccNeighbors)
      by (metis dual_order.trans set_drop_subset subset_ccNeighbors)
    qed
  qed
next
  assume "set xs \<subseteq> S"
  and "\<forall> n. ccProd (set (take n xs)) (set (drop n xs)) \<sqsubseteq> G" 
  thus "xs \<in> valid_lists S G"
  proof (induction xs)
    case Nil thus ?case by simp
  next
    case (Cons x xs)
    from \<open>\<forall>n. ccProd (set (take n (x # xs))) (set (drop n (x # xs))) \<sqsubseteq> G\<close>
    have "\<forall>n. ccProd (set (take n xs)) (set (drop n xs)) \<sqsubseteq> G"
      by -(rule, erule_tac x = "Suc n" in allE, auto simp add: ccProd_insert1[where S' = "set xs" for xs] join_below_iff)
    from Cons.prems Cons.IH[OF _ this]
    have "xs \<in> valid_lists S G" by auto
    with Cons.prems(1)  spec[OF \<open>\<forall>n. ccProd (set (take n (x # xs))) (set (drop n (x # xs))) \<sqsubseteq> G\<close>, where x = 1]
    show ?case by (simp add: subset_ccNeighbors)
  qed
qed

end
