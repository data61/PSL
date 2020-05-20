section \<open>\isaheader{List Based Sets}\<close>
theory Impl_List_Set
imports
  "../../Iterator/Iterator" 
  "../Intf/Intf_Set" 
begin
  (* TODO: Move *)
  lemma list_all2_refl_conv:
    "list_all2 P xs xs \<longleftrightarrow> (\<forall>x\<in>set xs. P x x)"
    by (induct xs) auto

  primrec glist_member :: "('a\<Rightarrow>'a\<Rightarrow>bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" where
    "glist_member eq x [] \<longleftrightarrow> False"
  | "glist_member eq x (y#ys) \<longleftrightarrow> eq x y \<or> glist_member eq x ys"

  lemma param_glist_member[param]: 
    "(glist_member,glist_member)\<in>(Ra\<rightarrow>Ra\<rightarrow>Id) \<rightarrow> Ra \<rightarrow> \<langle>Ra\<rangle>list_rel \<rightarrow> Id"
    unfolding glist_member_def
    by (parametricity)

  lemma list_member_alt: "List.member = (\<lambda>l x. glist_member (=) x l)"
  proof (intro ext)
    fix x l
    show "List.member l x = glist_member (=) x l"
      by (induct l) (auto simp: List.member_rec)
  qed

  thm List.insert_def
  definition 
    "glist_insert eq x xs = (if glist_member eq x xs then xs else x#xs)" 

  lemma param_glist_insert[param]:
    "(glist_insert, glist_insert) \<in> (R\<rightarrow>R\<rightarrow>Id) \<rightarrow> R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
    unfolding glist_insert_def[abs_def]
    by (parametricity)


  primrec rev_append where
    "rev_append [] ac = ac"
  | "rev_append (x#xs) ac = rev_append xs (x#ac)"

  lemma rev_append_eq: "rev_append l ac = rev l @ ac"
    by (induct l arbitrary: ac) auto

  (*
  primrec glist_delete_aux1 :: "('a\<Rightarrow>'a\<Rightarrow>bool) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "glist_delete_aux1 eq x [] = []"
  | "glist_delete_aux1 eq x (y#ys) = (
      if eq x y then 
        ys 
      else y#glist_delete_aux1 eq x ys)"

  primrec glist_delete_aux2 :: "('a\<Rightarrow>'a\<Rightarrow>_) \<Rightarrow> _" where
    "glist_delete_aux2 eq ac x [] = ac"
  | "glist_delete_aux2 eq ac x (y#ys) = (if eq x y then rev_append ys ac else
      glist_delete_aux2 eq (y#ac) x ys
    )"

  lemma glist_delete_aux2_eq1:
    "glist_delete_aux2 eq ac x l = rev (glist_delete_aux1 eq x l) @ ac"
    by (induct l arbitrary: ac) (auto simp: rev_append_eq)

  definition "glist_delete eq x l = glist_delete_aux2 eq [] x l"
  *)

  primrec glist_delete_aux :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> _" where
    "glist_delete_aux eq x [] as = as"
  | "glist_delete_aux eq x (y#ys) as = (
      if eq x y then rev_append as ys 
      else glist_delete_aux eq x ys (y#as)
    )"

  definition glist_delete where 
    "glist_delete eq x l \<equiv> glist_delete_aux eq x l []"

  lemma param_glist_delete[param]:
    "(glist_delete, glist_delete) \<in> (R\<rightarrow>R\<rightarrow>Id) \<rightarrow> R \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
    unfolding glist_delete_def[abs_def]
      glist_delete_aux_def
      rev_append_def
    by (parametricity)


lemma list_rel_Range:
    "\<forall>x'\<in>set l'. x' \<in> Range R \<Longrightarrow> l' \<in> Range (\<langle>R\<rangle>list_rel)"
proof (induction l')
  case Nil thus ?case by force
next
  case (Cons x' xs')
    then obtain xs where "(xs,xs') \<in> \<langle>R\<rangle> list_rel" by force
    moreover from Cons.prems obtain x where "(x,x') \<in> R" by force
    ultimately have "(x#xs, x'#xs') \<in> \<langle>R\<rangle> list_rel" by simp
    thus ?case ..
qed

  text \<open>All finite sets can be represented\<close>
  lemma list_set_rel_range:
    "Range (\<langle>R\<rangle>list_set_rel) = { S. finite S \<and> S\<subseteq>Range R }"
      (is "?A = ?B")
  proof (intro equalityI subsetI)
    fix s' assume "s' \<in> ?A"
    then obtain l l' where A: "(l,l') \<in> \<langle>R\<rangle>list_rel" and
       B: "s' = set l'" and C: "distinct l'"
        unfolding list_set_rel_def br_def by blast
    moreover have "set l' \<subseteq> Range R"
        by (induction rule: list_rel_induct[OF A], auto)
    ultimately show "s' \<in> ?B" by simp
  next
    fix s' assume A: "s' \<in> ?B"
    then obtain l' where B: "set l' = s'" and C: "distinct l'"
        using finite_distinct_list by blast
    hence "(l',s') \<in> br set distinct" by (simp add: br_def)
    
    moreover from A and B have "\<forall>x\<in>set l'. x \<in> Range R" by blast
    from list_rel_Range[OF this] obtain l
        where "(l,l') \<in> \<langle>R\<rangle>list_rel" by blast

    ultimately show "s' \<in> ?A" unfolding list_set_rel_def by fast
  qed

  lemmas [autoref_rel_intf] = REL_INTFI[of list_set_rel i_set]

  lemma list_set_rel_finite[autoref_ga_rules]:
    "finite_set_rel (\<langle>R\<rangle>list_set_rel)"
    unfolding finite_set_rel_def list_set_rel_def
    by (auto simp: br_def)

  lemma list_set_rel_sv[relator_props]:
    "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>list_set_rel)"
    unfolding list_set_rel_def
    by tagged_solver
    
  (* TODO: Move to Misc *)
  lemma Id_comp_Id: "Id O Id = Id" by simp

  lemma glist_member_id_impl: 
    "(glist_member (=), (\<in>)) \<in> Id \<rightarrow> br set distinct \<rightarrow> Id"
  proof (intro fun_relI, goal_cases)
    case (1 x x' l s') thus ?case
      by (induct l arbitrary: s') (auto simp: br_def)
  qed

  lemma glist_insert_id_impl:
    "(glist_insert (=), Set.insert) \<in> Id \<rightarrow> br set distinct \<rightarrow> br set distinct"
  proof -
    have IC: "\<And>x s. insert x s = (if x\<in>s then s else insert x s)" by auto

    show ?thesis
      apply (intro fun_relI)
      apply (subst IC)
      unfolding glist_insert_def
      apply (parametricity add: glist_member_id_impl)
      apply (auto simp: br_def)
      done
  qed

  lemma glist_delete_id_impl:
    "(glist_delete (=), \<lambda>x s. s-{x})
    \<in> Id\<rightarrow>br set distinct \<rightarrow> br set distinct"
  proof (intro fun_relI)
    fix x x':: 'a and s and s' :: "'a set"
    assume XREL: "(x, x') \<in> Id" and SREL: "(s, s') \<in> br set distinct"
    from XREL have [simp]: "x'=x" by simp

    {
      fix a and a' :: "'a set"
      assume "(a,a')\<in>br set distinct" and "s' \<inter> a' = {}"
      hence "(glist_delete_aux (=) x s a, s'-{x'} \<union> a')\<in>br set distinct"
        using SREL
      proof (induction s arbitrary: a s' a')
        case Nil thus ?case by (simp add: br_def)
      next
        case (Cons y s) 
        show ?case proof (cases "x=y")
          case True with Cons show ?thesis 
            by (auto simp add: br_def rev_append_eq)
        next
          case False
          have "glist_delete_aux (=) x (y # s) a 
            = glist_delete_aux (=) x s (y#a)" by (simp add: False)
          also have "(\<dots>,set s - {x'} \<union> insert y a')\<in>br set distinct"
            apply (rule Cons.IH[of "y#a" "insert y a'" "set s"])
            using Cons.prems by (auto simp: br_def)
          also have "set s - {x'} \<union> insert y a' = (s' - {x'}) \<union> a'"
          proof -
            from Cons.prems have [simp]: "s' = insert y (set s)"
              by (auto simp: br_def)
            show ?thesis using False by auto
          qed
          finally show ?thesis .
        qed
      qed
    }
    from this[of "[]" "{}"]     
    show "(glist_delete (=) x s, s' - {x'}) \<in> br set distinct"
      unfolding glist_delete_def
      by (simp add: br_def)
  qed
    
  lemma list_set_autoref_empty[autoref_rules]:
    "([],{})\<in>\<langle>R\<rangle>list_set_rel"
    by (auto simp: list_set_rel_def br_def)

  lemma list_set_autoref_member[autoref_rules]:
    assumes "GEN_OP eq (=) (R\<rightarrow>R\<rightarrow>Id)"
    shows "(glist_member eq,(\<in>)) \<in> R \<rightarrow> \<langle>R\<rangle>list_set_rel \<rightarrow> Id"
    using assms
    apply (intro fun_relI)
    unfolding list_set_rel_def
    apply (erule relcompE)
    apply (simp del: pair_in_Id_conv)
    apply (subst Id_comp_Id[symmetric])
    apply (rule relcompI[rotated])
    apply (rule glist_member_id_impl[param_fo])
    apply (rule IdI)
    apply assumption
    apply parametricity
    done

  lemma list_set_autoref_insert[autoref_rules]:
    assumes "GEN_OP eq (=) (R\<rightarrow>R\<rightarrow>Id)"
    shows "(glist_insert eq,Set.insert) 
      \<in> R \<rightarrow> \<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>list_set_rel"
    using assms
    apply (intro fun_relI)
    unfolding list_set_rel_def
    apply (erule relcompE)
    apply (simp del: pair_in_Id_conv)
    apply (rule relcompI[rotated])
    apply (rule glist_insert_id_impl[param_fo])
    apply (rule IdI)
    apply assumption
    apply parametricity
    done

  lemma list_set_autoref_delete[autoref_rules]:
    assumes "GEN_OP eq (=) (R\<rightarrow>R\<rightarrow>Id)"
    shows "(glist_delete eq,op_set_delete) 
      \<in> R \<rightarrow> \<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>list_set_rel"
    using assms
    apply (intro fun_relI)
    unfolding list_set_rel_def
    apply (erule relcompE)
    apply (simp del: pair_in_Id_conv)
    apply (rule relcompI[rotated])
    apply (rule glist_delete_id_impl[param_fo])
    apply (rule IdI)
    apply assumption
    apply parametricity
    done
 
  lemma list_set_autoref_to_list[autoref_ga_rules]: 
    shows "is_set_to_sorted_list (\<lambda>_ _. True) R list_set_rel id"
    unfolding is_set_to_list_def is_set_to_sorted_list_def
      it_to_sorted_list_def list_set_rel_def br_def
    by auto

  lemma list_set_it_simp[refine_transfer_post_simp]:
    "foldli (id l) = foldli l" by simp

  lemma glist_insert_dj_id_impl:
    "\<lbrakk> x\<notin>s; (l,s)\<in>br set distinct \<rbrakk> \<Longrightarrow> (x#l,insert x s)\<in>br set distinct"
    by (auto simp: br_def)

context begin interpretation autoref_syn .
  lemma list_set_autoref_insert_dj[autoref_rules]:
    assumes "PRIO_TAG_OPTIMIZATION"
    assumes "SIDE_PRECOND_OPT (x'\<notin>s')"
    assumes "(x,x')\<in>R"
    assumes "(s,s')\<in>\<langle>R\<rangle>list_set_rel"
    shows "(x#s,
      (OP Set.insert ::: R \<rightarrow> \<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>list_set_rel) $ x' $ s') 
      \<in> \<langle>R\<rangle>list_set_rel"
    using assms
    unfolding autoref_tag_defs
    unfolding list_set_rel_def
    apply -
    apply (erule relcompE)
    apply (simp del: pair_in_Id_conv)
    apply (rule relcompI[rotated])
    apply (rule glist_insert_dj_id_impl)
    apply assumption
    apply assumption
    apply parametricity
    done
end

  subsection \<open>More Operations\<close>
  lemma list_set_autoref_isEmpty[autoref_rules]:
    "(is_Nil,op_set_isEmpty) \<in> \<langle>R\<rangle>list_set_rel \<rightarrow> bool_rel"
    by (auto simp: list_set_rel_def br_def split: list.split_asm)

  lemma list_set_autoref_filter[autoref_rules]:
    "(filter,op_set_filter) 
      \<in> (R \<rightarrow> bool_rel) \<rightarrow> \<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>list_set_rel"
  proof -
    have "(filter, op_set_filter) 
      \<in> (Id \<rightarrow> bool_rel) \<rightarrow> \<langle>Id\<rangle>list_set_rel \<rightarrow> \<langle>Id\<rangle>list_set_rel"
      by (auto simp: list_set_rel_def br_def)
    note this[param_fo]
    moreover have "(filter,filter)\<in>(R \<rightarrow> bool_rel) \<rightarrow> \<langle>R\<rangle>list_rel \<rightarrow> \<langle>R\<rangle>list_rel"
      unfolding List.filter_def
      by parametricity
    note this[param_fo]
    ultimately show ?thesis
      unfolding list_set_rel_def
      apply (intro fun_relI)
      apply (erule relcompE, simp)
      apply (rule relcompI)
      apply (rprems, assumption+)
      apply (rprems, simp+)
      done
  qed


  context begin interpretation autoref_syn .
  lemma list_set_autoref_inj_image[autoref_rules]:
    assumes "PRIO_TAG_OPTIMIZATION"
    assumes INJ: "SIDE_PRECOND_OPT (inj_on f s)"
    assumes [param]: "(fi,f)\<in>Ra\<rightarrow>Rb"
    assumes LP: "(l,s)\<in>\<langle>Ra\<rangle>list_set_rel"
    shows "(map fi l, 
      (OP (`) ::: (Ra\<rightarrow>Rb) \<rightarrow> \<langle>Ra\<rangle>list_set_rel \<rightarrow> \<langle>Rb\<rangle>list_set_rel)$f$s) 
      \<in> \<langle>Rb\<rangle>list_set_rel"
  proof -
    from LP obtain l' where 
      [param]: "(l,l')\<in>\<langle>Ra\<rangle>list_rel" and L'S: "(l',s)\<in>br set distinct"
      unfolding list_set_rel_def by auto

    have "(map fi l, map f l')\<in>\<langle>Rb\<rangle>list_rel" by parametricity
    also from INJ L'S have "(map f l',f`s)\<in>br set distinct"
      apply (induction l' arbitrary: s)
      apply (auto simp: br_def dest: injD)
      done
    finally (relcompI) show ?thesis 
      unfolding autoref_tag_defs list_set_rel_def .
  qed

  end


  lemma list_set_cart_autoref[autoref_rules]:
    fixes Rx :: "('xi \<times> 'x) set"
    fixes Ry :: "('yi \<times> 'y) set"
    shows "(\<lambda>xl yl. [ (x,y). x\<leftarrow>xl, y\<leftarrow>yl], op_set_cart) 
    \<in> \<langle>Rx\<rangle>list_set_rel \<rightarrow> \<langle>Ry\<rangle>list_set_rel \<rightarrow> \<langle>Rx \<times>\<^sub>r Ry\<rangle>list_set_rel"
  proof (intro fun_relI)
    fix xl xs yl ys
    assume "(xl, xs) \<in> \<langle>Rx\<rangle>list_set_rel" "(yl, ys) \<in> \<langle>Ry\<rangle>list_set_rel"
    then obtain xl' :: "'x list" and yl' :: "'y list" where 
      [param]: "(xl,xl')\<in>\<langle>Rx\<rangle>list_rel" "(yl,yl')\<in>\<langle>Ry\<rangle>list_rel"
      and XLS: "(xl',xs)\<in>br set distinct" and YLS: "(yl',ys)\<in>br set distinct"
      unfolding list_set_rel_def 
      by auto

    have "([ (x,y). x\<leftarrow>xl, y\<leftarrow>yl ], [ (x,y). x\<leftarrow>xl', y\<leftarrow>yl' ]) 
      \<in> \<langle>Rx \<times>\<^sub>r Ry\<rangle>list_rel"
      by parametricity
    also have "([ (x,y). x\<leftarrow>xl', y\<leftarrow>yl' ], xs \<times> ys) \<in> br set distinct"
      using XLS YLS
      apply (auto simp: br_def)
      apply hypsubst_thin
      apply (induction xl')
      apply simp
      apply (induction yl')
      apply simp
      apply auto []
      apply (metis (lifting) concat_map_maps distinct.simps(2) 
        distinct_singleton maps_simps(2))
      done
    finally (relcompI) 
    show "([ (x,y). x\<leftarrow>xl, y\<leftarrow>yl ], op_set_cart xs ys) \<in> \<langle>Rx \<times>\<^sub>r Ry\<rangle>list_set_rel"
      unfolding list_set_rel_def by simp
  qed


  subsection \<open>Optimizations\<close>
  lemma glist_delete_hd: "eq x y \<Longrightarrow> glist_delete eq x (y#s) = s"
    by (simp add: glist_delete_def)

  text \<open>Hack to ensure specific ordering. Note that ordering has no meaning
    abstractly\<close>
  definition [simp]: "LIST_SET_REV_TAG \<equiv> \<lambda>x. x"
  
  lemma LIST_SET_REV_TAG_autoref[autoref_rules]: 
    "(rev,LIST_SET_REV_TAG) \<in> \<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>list_set_rel"
    unfolding list_set_rel_def
    apply (intro fun_relI)
    apply (elim relcompE)
    apply (clarsimp simp: br_def)
    apply (rule relcompI)
    apply (rule param_rev[param_fo], assumption)
    apply auto
    done
  
  



end
