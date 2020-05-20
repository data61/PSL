theory SestoftGC
imports Sestoft 
begin

inductive gc_step :: "conf \<Rightarrow> conf \<Rightarrow> bool" (infix "\<Rightarrow>\<^sub>G" 50) where
  normal:  "c \<Rightarrow> c' \<Longrightarrow> c \<Rightarrow>\<^sub>G c'"
| dropUpd: "(\<Gamma>, e, Upd x # S) \<Rightarrow>\<^sub>G (\<Gamma>, e, S @ [Dummy x])"
(*
| drop: "x \<in> domA \<Gamma>  \<Longrightarrow> (\<Gamma>, e, S) \<Rightarrow>\<^sub>G (delete x \<Gamma>, e, S @ [Dummy x])"
*)

lemmas gc_step_intros[intro] =
  normal[OF step.intros(1)] normal[OF step.intros(2)] normal[OF step.intros(3)]
  normal[OF step.intros(4)] normal[OF step.intros(5)]  dropUpd

abbreviation gc_steps (infix "\<Rightarrow>\<^sub>G\<^sup>*" 50) where "gc_steps \<equiv> gc_step\<^sup>*\<^sup>*"
lemmas converse_rtranclp_into_rtranclp[of gc_step, OF _ r_into_rtranclp, trans]

lemma var_onceI:
  assumes "map_of \<Gamma> x = Some e"
  shows "(\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G\<^sup>* (delete x \<Gamma>, e , S@[Dummy x])"
proof-
  from assms 
  have "(\<Gamma>, Var x, S) \<Rightarrow>\<^sub>G (delete x \<Gamma>, e , Upd x # S)"..
  moreover
  have "\<dots> \<Rightarrow>\<^sub>G  (delete x \<Gamma>, e, S@[Dummy x])"..
  ultimately
  show ?thesis by (rule converse_rtranclp_into_rtranclp[OF _ r_into_rtranclp])
qed

(*
lemma lam_and_restrict:
  assumes "atom ` domA \<Delta> \<sharp>* \<Gamma>" and "atom ` domA \<Delta> \<sharp>* S"
  assumes "V \<subseteq> domA \<Delta>"
  shows "(\<Gamma>, Let \<Delta> e, S) \<Rightarrow>\<^sub>G\<^sup>* (restrictA V \<Delta> @ \<Gamma>, e, S)"
proof-
  from assms(1,2) have "(\<Gamma>, Let \<Delta> e, S) \<Rightarrow>\<^sub>G (\<Delta> @ \<Gamma>, e, S)"..
  also
  have "\<dots> \<Rightarrow>\<^sub>G (restrictA (V \<union> domA \<Gamma>) (\<Delta> @ \<Gamma>), e, S)"..
  also
  from fresh_distinct[OF assms(1)]
  have "restrictA (V \<union> domA \<Gamma>) \<Delta> = restrictA V \<Delta>" by (induction \<Delta>) auto
  hence "restrictA (V \<union> domA \<Gamma>) (\<Delta> @ \<Gamma>) = restrictA V \<Delta> @ \<Gamma>"
    by (simp add: restrictA_append restrictA_noop)
  finally show ?thesis.
qed
*)

lemma normal_trans:  "c \<Rightarrow>\<^sup>* c' \<Longrightarrow> c \<Rightarrow>\<^sub>G\<^sup>* c'"
  by (induction rule:rtranclp_induct)
     (simp, metis normal rtranclp.rtrancl_into_rtrancl)

fun to_gc_conf :: "var list \<Rightarrow> conf \<Rightarrow> conf"
  where "to_gc_conf r (\<Gamma>, e, S) = (restrictA (- set r) \<Gamma>, e, restr_stack (- set r) S @ (map Dummy (rev r)))"

lemma restr_stack_map_Dummy[simp]: "restr_stack V (map Dummy l) = map Dummy l"
  by (induction l) auto

lemma restr_stack_append[simp]: "restr_stack V (l@l') = restr_stack V l @ restr_stack V l'"
  by (induction l rule: restr_stack.induct) auto

lemma to_gc_conf_append[simp]:
  "to_gc_conf (r@r') c = to_gc_conf r (to_gc_conf r' c)"
  by (cases c) auto

lemma to_gc_conf_eqE[elim!]:
  assumes  "to_gc_conf r c = (\<Gamma>, e, S)"
  obtains \<Gamma>' S' where "c = (\<Gamma>', e, S')" and "\<Gamma> = restrictA (- set r) \<Gamma>'" and "S = restr_stack (- set r) S' @ map Dummy (rev r)"
  using assms by (cases c) auto

fun safe_hd :: "'a list \<Rightarrow> 'a option"
 where  "safe_hd (x#_) = Some x"
     |  "safe_hd [] = None"

lemma safe_hd_None[simp]: "safe_hd xs = None \<longleftrightarrow> xs = []"
  by (cases xs) auto

abbreviation r_ok :: "var list \<Rightarrow> conf \<Rightarrow> bool"
  where "r_ok r c \<equiv> set r \<subseteq> domA (fst c) \<union> upds (snd (snd c))"

lemma subset_bound_invariant:
  "invariant step (r_ok r)"
proof
  fix x y
  assume "x \<Rightarrow> y" and "r_ok r x" thus "r_ok r y"
  by (induction) auto
qed

lemma safe_hd_restr_stack[simp]:
  "Some a = safe_hd (restr_stack V (a # S)) \<longleftrightarrow> restr_stack V (a # S) = a # restr_stack V S"
  apply (cases a)
  apply (auto split: if_splits)
  apply (thin_tac "P a" for P)
  apply (induction S rule: restr_stack.induct)
  apply (auto split: if_splits)
  done

lemma sestoftUnGCStack:
  assumes "heap_upds_ok (\<Gamma>, S)"
  obtains \<Gamma>' S' where
    "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Gamma>', e, S')"
    "to_gc_conf r (\<Gamma>, e, S) = to_gc_conf r (\<Gamma>', e, S')"
    "\<not> isVal e \<or> safe_hd S' = safe_hd (restr_stack (- set r) S')"
proof-
  show ?thesis
  proof(cases "isVal e")
    case False
    thus ?thesis using assms  by -(rule that, auto)
  next
    case True
    from that assms 
    show ?thesis
    apply (atomize_elim)
    proof(induction S arbitrary: \<Gamma>)
      case Nil thus ?case by (fastforce)
    next
      case (Cons s S)
      show ?case
      proof(cases "Some s = safe_hd (restr_stack (- set r) (s#S))")
        case True
        thus ?thesis
          using \<open>isVal e\<close> \<open>heap_upds_ok (\<Gamma>, s # S)\<close>
          apply auto
          apply (intro exI conjI)
          apply (rule rtranclp.intros(1))
          apply auto
          done
      next
        case False
        then obtain x where [simp]: "s = Upd x" and [simp]: "x \<in> set r"
          by(cases s) (auto split: if_splits)
      
        from \<open>heap_upds_ok (\<Gamma>, s # S)\<close> \<open>s = Upd x\<close>
        have [simp]: "x \<notin> domA \<Gamma>" and "heap_upds_ok ((x,e) # \<Gamma>, S)"
          by (auto dest: heap_upds_okE) 

        have "(\<Gamma>, e, s # S) \<Rightarrow>\<^sup>* (\<Gamma>, e, Upd x # S)" unfolding \<open>s = _\<close> ..
        also have "\<dots> \<Rightarrow> ((x,e) # \<Gamma>, e, S)" by (rule step.var\<^sub>2[OF \<open>x \<notin> domA \<Gamma>\<close> \<open>isVal e\<close>])
        also
        from Cons.IH[OF \<open>heap_upds_ok ((x,e) # \<Gamma>, S)\<close> ]
        obtain \<Gamma>' S' where  "((x,e) # \<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Gamma>', e, S')"
            and res: "to_gc_conf r ((x,e) # \<Gamma>, e, S) = to_gc_conf r (\<Gamma>', e, S')"
                     "(\<not> isVal e \<or> safe_hd S' = safe_hd (restr_stack (- set r) S'))"
          by blast
        note this(1)
        finally
        have "(\<Gamma>, e, s # S) \<Rightarrow>\<^sup>* (\<Gamma>', e, S')".
        thus ?thesis  using res by auto
      qed
    qed
  qed
qed

lemma perm_exI_trivial:
  "P x x \<Longrightarrow> \<exists> \<pi>. P (\<pi> \<bullet> x) x"
by (rule exI[where x = "0::perm"]) auto

lemma upds_list_restr_stack[simp]:
  "upds_list (restr_stack V S) = filter (\<lambda> x. x\<in>V) (upds_list S)"
by (induction S rule: restr_stack.induct) auto

lemma heap_upd_ok_to_gc_conf:
  "heap_upds_ok (\<Gamma>, S) \<Longrightarrow> to_gc_conf r (\<Gamma>, e, S) = (\<Gamma>'', e'', S'') \<Longrightarrow> heap_upds_ok (\<Gamma>'', S'')"
by (auto simp add: heap_upds_ok.simps)

lemma delete_restrictA_conv:
  "delete x \<Gamma> = restrictA (-{x}) \<Gamma>"
by (induction \<Gamma>) auto

lemma sestoftUnGCstep:
  assumes "to_gc_conf r c \<Rightarrow>\<^sub>G d"
  assumes "heap_upds_ok_conf c"
  assumes "closed c"
  and "r_ok r c"
  shows   "\<exists> r' c'. c \<Rightarrow>\<^sup>* c' \<and> d = to_gc_conf r' c' \<and> r_ok r' c'"
proof-
  obtain \<Gamma> e S where "c = (\<Gamma>, e, S)" by (cases c) auto
  with assms
  have "heap_upds_ok (\<Gamma>,S)" and "closed (\<Gamma>, e, S)" and "r_ok r (\<Gamma>, e, S)" by auto
  from sestoftUnGCStack[OF this(1)]
  obtain \<Gamma>' S' where
    "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Gamma>', e, S')"
    and *: "to_gc_conf r (\<Gamma>, e, S) = to_gc_conf r (\<Gamma>', e, S')"
    and disj: "\<not> isVal e \<or> safe_hd S' = safe_hd (restr_stack (- set r) S')"
    by metis

  from invariant_starE[OF \<open>_ \<Rightarrow>\<^sup>* _\<close> heap_upds_ok_invariant]  \<open>heap_upds_ok (\<Gamma>,S)\<close>
  have "heap_upds_ok (\<Gamma>', S')" by auto

  from invariant_starE[OF \<open>_ \<Rightarrow>\<^sup>* _\<close> closed_invariant  \<open>closed (\<Gamma>, e, S)\<close> ]
  have "closed (\<Gamma>', e, S')" by auto

  from invariant_starE[OF \<open>_ \<Rightarrow>\<^sup>* _\<close> subset_bound_invariant \<open>r_ok r (\<Gamma>, e, S)\<close> ]
  have "r_ok r (\<Gamma>', e, S')" by auto

  from assms(1)[unfolded \<open>c =_ \<close> *]
  have "\<exists> r' \<Gamma>'' e'' S''. (\<Gamma>', e, S') \<Rightarrow>\<^sup>* (\<Gamma>'', e'', S'') \<and> d = to_gc_conf r' (\<Gamma>'', e'', S'') \<and> r_ok r' (\<Gamma>'', e'', S'')"
  proof(cases rule: gc_step.cases)
    case normal
    hence "\<exists> \<Gamma>'' e'' S''. (\<Gamma>', e, S') \<Rightarrow> (\<Gamma>'', e'', S'') \<and> d = to_gc_conf r (\<Gamma>'', e'', S'')"
    proof(cases rule: step.cases)
      case app\<^sub>1
      thus ?thesis
        apply auto
        apply (intro exI conjI)
        apply (rule  step.intros)
        apply auto
        done
    next
      case (app\<^sub>2 \<Gamma> y ea x S)
      thus ?thesis
        using disj 
        apply (cases S')
        apply auto
        apply (intro exI conjI)
        apply (rule step.intros)
        apply auto
        done
    next
      case var\<^sub>1
      thus ?thesis
        apply auto
        apply (intro  exI conjI)
        apply (rule step.intros)
        apply (auto simp add: restr_delete_twist)
        done
    next
      case var\<^sub>2
      thus ?thesis
        using disj 
        apply (cases S')
        apply auto
        apply (intro exI conjI)
        apply (rule step.intros)
        apply (auto split: if_splits dest: Upd_eq_restr_stackD2)
        done
    next
      case (let\<^sub>1 \<Delta>'' \<Gamma>'' S'' e')

      from \<open>closed (\<Gamma>', e, S')\<close> let\<^sub>1
      have "closed (\<Gamma>', Let \<Delta>'' e', S')" by simp

      from fresh_distinct[OF let\<^sub>1(3)] fresh_distinct_fv[OF let\<^sub>1(4)]
      have "domA \<Delta>'' \<inter> domA \<Gamma>'' = {}" and "domA \<Delta>'' \<inter> upds S'' = {}"  and "domA \<Delta>'' \<inter> dummies S'' = {}" 
        by (auto dest: subsetD[OF ups_fv_subset] subsetD[OF dummies_fv_subset])
      moreover
      from let\<^sub>1(1)
      have "domA \<Gamma>' \<union> upds S' \<subseteq> domA \<Gamma>'' \<union> upds S'' \<union> dummies S''"
        by auto
      ultimately
      have disj: "domA \<Delta>'' \<inter> domA \<Gamma>' = {}" "domA \<Delta>'' \<inter> upds S' = {}"
        by auto
      
      from \<open>domA \<Delta>'' \<inter> dummies S'' = {}\<close> let\<^sub>1(1)
      have "domA \<Delta>'' \<inter> set r = {}" by auto
      hence [simp]: "restrictA (- set r) \<Delta>'' = \<Delta>''"
        by (auto intro: restrictA_noop)

      from let\<^sub>1(1-3)
      show ?thesis
        apply auto
        apply (intro  exI[where x = "r"] exI[where x = "\<Delta>'' @ \<Gamma>'"] exI[where x = "S'"] conjI)
        apply (rule let\<^sub>1_closed[OF \<open>closed (\<Gamma>', Let \<Delta>'' e', S')\<close> disj])
        apply (auto simp add: restrictA_append)
        done
    next
      case if\<^sub>1
      thus ?thesis
        apply auto
        apply (intro exI[where x = "0::perm"] exI conjI)
        unfolding permute_zero
        apply (rule step.intros)
        apply (auto)
        done
    next
      case if\<^sub>2
      thus ?thesis
        using disj
        apply (cases S')
        apply auto
        apply (intro exI exI conjI)
        apply (rule step.if\<^sub>2[where b = True, simplified] step.if\<^sub>2[where b = False, simplified])
        apply (auto split: if_splits dest: Upd_eq_restr_stackD2)
        apply (intro exI conjI)
        apply (rule step.if\<^sub>2[where b = True, simplified] step.if\<^sub>2[where b = False, simplified])
        apply (auto split: if_splits dest: Upd_eq_restr_stackD2)
        done
    qed
    with invariantE[OF subset_bound_invariant _ \<open>r_ok r (\<Gamma>', e, S')\<close>]
    show ?thesis by blast
  next
  case (dropUpd \<Gamma>'' e'' x S'')
    from \<open>to_gc_conf r (\<Gamma>', e, S') = (\<Gamma>'', e'', Upd x # S'')\<close>
    have "x \<notin> set r" by (auto dest!: arg_cong[where f = upds])
    
    from \<open>heap_upds_ok (\<Gamma>', S')\<close> and \<open>to_gc_conf r (\<Gamma>', e, S') = (\<Gamma>'', e'', Upd x # S'')\<close>
    have "heap_upds_ok (\<Gamma>'', Upd x # S'')" by (rule heap_upd_ok_to_gc_conf)
    hence [simp]: "x \<notin> domA \<Gamma>''" "x \<notin> upds S''" by (auto dest: heap_upds_ok_upd)

    have "to_gc_conf (x # r) (\<Gamma>', e, S') = to_gc_conf ([x]@ r) (\<Gamma>', e, S')" by simp
    also have "\<dots> = to_gc_conf [x] (to_gc_conf r (\<Gamma>', e, S'))" by (rule to_gc_conf_append)
    also have "\<dots> = to_gc_conf [x] (\<Gamma>'', e'', Upd x # S'')" unfolding \<open>to_gc_conf r (\<Gamma>', e, S') = _\<close>..
    also have "\<dots> = (\<Gamma>'', e'', S''@[Dummy x])" by (auto intro: restrictA_noop)
    also have "\<dots> = d" using \<open> d= _\<close> by simp
    finally have "to_gc_conf (x # r) (\<Gamma>', e, S') = d".
    moreover
    from \<open>to_gc_conf r (\<Gamma>', e, S') = (\<Gamma>'', e'', Upd x # S'')\<close>
    have "x \<in> upds S'" by (auto dest!: arg_cong[where f = upds])
    with \<open>r_ok r (\<Gamma>', e, S')\<close>
    have "r_ok (x # r) (\<Gamma>', e, S')" by auto
    moreover
    note \<open>to_gc_conf r (\<Gamma>', e, S') = (\<Gamma>'', e'', Upd x # S'')\<close>
    ultimately
    show ?thesis by fastforce
(*
  next
    case (drop x \<Gamma>'' e'' S'')
    from `to_gc_conf r (\<Gamma>', e, S') = (\<Gamma>'', e'', S'')` and `x \<in> domA \<Gamma>''`
    have "x \<notin> set r" by auto

    from `heap_upds_ok (\<Gamma>', S')` and  `to_gc_conf r (\<Gamma>', e, S') = (\<Gamma>'', e'', S'')`
    have "heap_upds_ok (\<Gamma>'', S'')" by (rule heap_upd_ok_to_gc_conf)
    with `x \<in> domA \<Gamma>''`
    have [simp]: "x \<notin> upds S''" by (metis heap_upds_okE)


    have "to_gc_conf (x # r) (\<Gamma>', e, S') = to_gc_conf ([x]@ r) (\<Gamma>', e, S')" by simp
    also have "\<dots> = to_gc_conf [x] (to_gc_conf r (\<Gamma>', e, S'))" by (rule to_gc_conf_append)
    also have "\<dots> = to_gc_conf [x] (\<Gamma>'', e'', S'')" unfolding `to_gc_conf r (\<Gamma>', e, S') = _`..
    also have "\<dots> = (delete x \<Gamma>'', e'', S''@[Dummy x])" by (auto  simp add: delete_restrictA_conv)
    also have "\<dots> = d" using ` d= _` by simp
    finally have "to_gc_conf (x # r) (\<Gamma>', e, S') = d".
    moreover
    from `to_gc_conf r (\<Gamma>', e, S') = _` `x \<in> domA \<Gamma>''`
    have "x \<in> domA \<Gamma>'" by auto
    with `r_ok r (\<Gamma>', e, S')`
    have "r_ok (x # r) (\<Gamma>', e, S')" by auto
    moreover
    note `to_gc_conf r (\<Gamma>', e, S') = _`
    ultimately
    show ?thesis by fastforce
*)
  qed
  then obtain r' \<Gamma>'' e'' S''
    where "(\<Gamma>', e, S') \<Rightarrow>\<^sup>* (\<Gamma>'', e'', S'')"
    and "d = to_gc_conf r' (\<Gamma>'', e'', S'')"
    and "r_ok r' (\<Gamma>'', e'', S'')"
    by metis 

  from  \<open>(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Gamma>', e, S')\<close> and \<open>(\<Gamma>', e, S') \<Rightarrow>\<^sup>* (\<Gamma>'', e'', S'')\<close>
  have "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Gamma>'', e'', S'')" by (rule rtranclp_trans)
  with \<open>d = _\<close> \<open>r_ok r' _\<close>
  show ?thesis unfolding \<open>c = _\<close> by auto
qed


lemma sestoftUnGC:
  assumes "(to_gc_conf r c) \<Rightarrow>\<^sub>G\<^sup>* d" and "heap_upds_ok_conf c" and "closed c" and "r_ok r c"
  shows   "\<exists> r' c'. c \<Rightarrow>\<^sup>* c' \<and> d = to_gc_conf r' c' \<and> r_ok r' c'"
using assms
proof(induction rule: rtranclp_induct)
  case base
  thus ?case by blast
next
  case (step d' d'')
  then obtain r' c' where "c \<Rightarrow>\<^sup>*  c'" and "d' = to_gc_conf r' c'" and "r_ok r' c'"  by auto

  from invariant_starE[OF \<open>_ \<Rightarrow>\<^sup>* _\<close> heap_upds_ok_invariant]  \<open>heap_upds_ok _\<close>
  have "heap_upds_ok_conf c'".

  from invariant_starE[OF \<open>_ \<Rightarrow>\<^sup>* _\<close> closed_invariant]  \<open>closed _\<close> 
  have "closed c'".

  from step \<open>d' = to_gc_conf r' c'\<close>
  have "to_gc_conf r' c' \<Rightarrow>\<^sub>G d''" by simp
  from this \<open>heap_upds_ok_conf c'\<close> \<open>closed c'\<close> \<open>r_ok r' c'\<close>
  have "\<exists> r'' c''. c' \<Rightarrow>\<^sup>* c'' \<and> d'' = to_gc_conf r'' c'' \<and> r_ok r'' c''"
    by (rule sestoftUnGCstep)
  then obtain r'' c'' where "c' \<Rightarrow>\<^sup>* c''" and "d'' = to_gc_conf r'' c''" and "r_ok r'' c''" by auto
  
  from \<open>c' \<Rightarrow>\<^sup>*  c''\<close> \<open>c \<Rightarrow>\<^sup>*  c'\<close>
  have "c \<Rightarrow>\<^sup>* c''" by auto
  with \<open>d'' = _\<close> \<open>r_ok r'' c''\<close>
  show ?case by blast
qed

lemma dummies_unchanged_invariant:
  "invariant step (\<lambda> (\<Gamma>, e, S) . dummies S = V)" (is "invariant _ ?I")
proof
  fix c c'
  assume "c \<Rightarrow> c'" and "?I c"
  thus "?I c'" by (induction) auto
qed
  
lemma sestoftUnGC':
  assumes "([], e, []) \<Rightarrow>\<^sub>G\<^sup>* (\<Gamma>, e', map Dummy r)"
  assumes "isVal e'"
  assumes "fv e = ({}::var set)"
  shows   "\<exists> \<Gamma>''. ([], e, []) \<Rightarrow>\<^sup>* (\<Gamma>'', e', []) \<and> \<Gamma> = restrictA (- set r) \<Gamma>'' \<and> set r \<subseteq> domA \<Gamma>''"
proof-
 from sestoftUnGC[where r = "[]" and c = "([], e, [])", simplified, OF assms(1,3)]
 obtain r' \<Gamma>' S'
  where "([], e, []) \<Rightarrow>\<^sup>* (\<Gamma>', e', S')"
    and "\<Gamma> = restrictA (- set r') \<Gamma>'"
    and "map Dummy r = restr_stack (- set r') S' @ map Dummy (rev r')"
    and "r_ok r' (\<Gamma>', e', S')"
    by auto

  from invariant_starE[OF \<open>([], e, []) \<Rightarrow>\<^sup>* (\<Gamma>', e', S')\<close> dummies_unchanged_invariant]
  have "dummies S' = {}" by auto
  with  \<open>map Dummy r = restr_stack (- set r') S' @ map Dummy (rev r')\<close>
  have "restr_stack (- set r') S' = []" and [simp]: "r = rev r'"
  by (induction S' rule: restr_stack.induct) (auto split: if_splits)
  
  from invariant_starE[OF \<open>_ \<Rightarrow>\<^sup>* _\<close> heap_upds_ok_invariant]
  have "heap_upds_ok (\<Gamma>', S')" by auto
 
  from \<open>isVal e'\<close> sestoftUnGCStack[where e = e', OF \<open>heap_upds_ok (\<Gamma>', S')\<close> ]
  obtain \<Gamma>'' S''
    where "(\<Gamma>', e', S') \<Rightarrow>\<^sup>* (\<Gamma>'', e', S'')"
    and "to_gc_conf r (\<Gamma>', e', S') = to_gc_conf r (\<Gamma>'', e', S'')"
    and "safe_hd S'' = safe_hd (restr_stack (- set r) S'')"
    by metis

  from this (2,3) \<open>restr_stack (- set r') S' = []\<close>
  have "S'' = []" by auto

  from  \<open>([], e, []) \<Rightarrow>\<^sup>* (\<Gamma>', e', S')\<close>  and \<open>(\<Gamma>', e', S') \<Rightarrow>\<^sup>* (\<Gamma>'', e', S'')\<close> and \<open>S'' = []\<close>
  have "([], e, []) \<Rightarrow>\<^sup>*  (\<Gamma>'', e', [])" by auto
  moreover
  have "\<Gamma> = restrictA (- set r) \<Gamma>''" using \<open>to_gc_conf r _ = _\<close> \<open>\<Gamma> = _\<close> by auto
  moreover
  from invariant_starE[OF \<open>(\<Gamma>', e', S') \<Rightarrow>\<^sup>* (\<Gamma>'', e', S'')\<close> subset_bound_invariant \<open>r_ok r' (\<Gamma>', e', S')\<close>]
  have "set r \<subseteq> domA \<Gamma>''" using \<open>S'' = []\<close> by auto
  ultimately
  show ?thesis by blast
qed

end

