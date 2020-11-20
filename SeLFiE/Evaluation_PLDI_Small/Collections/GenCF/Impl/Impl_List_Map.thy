section \<open>\isaheader{List Based Maps}\<close>
theory Impl_List_Map
imports
  "../../Iterator/Iterator"
  "../Gen/Gen_Map"
  "../Intf/Intf_Comp"
  "../Intf/Intf_Map"
begin

type_synonym ('k,'v) list_map = "('k\<times>'v) list"

definition "list_map_invar = distinct o map fst"

definition list_map_rel_internal_def: 
    "list_map_rel Rk Rv \<equiv> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel O br map_of list_map_invar"

lemma list_map_rel_def: 
    "\<langle>Rk,Rv\<rangle>list_map_rel = \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel O br map_of list_map_invar"
    unfolding list_map_rel_internal_def[abs_def] by (simp add: relAPP_def)

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

text \<open>All finite maps can be represented\<close>
lemma list_map_rel_range:
  "Range (\<langle>Rk,Rv\<rangle>list_map_rel) = 
       {m. finite (dom m) \<and> dom m \<subseteq> Range Rk \<and> ran m \<subseteq> Range Rv}" 
       (is "?A = ?B")
proof (intro equalityI subsetI)
  fix m' assume "m' \<in> ?A"
  then obtain l l' where A: "(l,l') \<in> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel" and
                         B: "m' = map_of l'" and C: "list_map_invar l'"
       unfolding list_map_rel_def br_def by blast
  {
    fix x' y' assume "m' x' = Some y'"
    with B have "(x',y') \<in> set l'" by (fast dest: map_of_SomeD)
    hence "x' \<in> Range Rk" and "y' \<in> Range Rv" 
      by (induction rule: list_rel_induct[OF A], auto)
  }
  with B show "m' \<in> ?B" by (force dest: map_of_SomeD simp: ran_def)

next
  fix m' assume "m' \<in> ?B"
  hence A: "finite (dom m')" and B: "dom m' \<subseteq> Range Rk" and 
        C: "ran m' \<subseteq> Range Rv" by simp_all
  from A have "finite (map_to_set m')" by (simp add: finite_map_to_set)
  from finite_distinct_list[OF this]
      obtain l' where l'_props: "distinct l'" "set l' = map_to_set m'" by blast
  hence *: "distinct (map fst l')"
      by (force simp: distinct_map inj_on_def map_to_set_def)
  from map_of_map_to_set[OF this] and l'_props 
      have  "map_of l' = m'" by simp
  with * have "(l',m') \<in> br map_of list_map_invar"
      unfolding br_def list_map_invar_def o_def by simp

  moreover from B and C and l'_props 
      have "\<forall>x \<in> set l'. x \<in> Range (\<langle>Rk,Rv\<rangle>prod_rel)"
      unfolding map_to_set_def ran_def prod_rel_def by force
  from list_rel_Range[OF this] obtain l where 
      "(l,l') \<in> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel" by force
  
  ultimately show "m' \<in> ?A" unfolding list_map_rel_def by blast
qed


  lemmas [autoref_rel_intf] = REL_INTFI[of list_map_rel i_map]

  lemma list_map_rel_finite[autoref_ga_rules]:
    "finite_map_rel (\<langle>Rk,Rv\<rangle>list_map_rel)"
    unfolding finite_map_rel_def list_map_rel_def
    by (auto simp: br_def)

  lemma list_map_rel_sv[relator_props]:
    "single_valued Rk \<Longrightarrow> single_valued Rv \<Longrightarrow> 
        single_valued (\<langle>Rk,Rv\<rangle>list_map_rel)"
    unfolding list_map_rel_def
    by tagged_solver
    
  (* TODO: Move to Misc *)


subsection \<open>Implementation\<close>

primrec list_map_lookup :: 
    "('k \<Rightarrow> 'k \<Rightarrow> bool) \<Rightarrow> 'k \<Rightarrow> ('k,'v) list_map \<Rightarrow> 'v option" where
"list_map_lookup eq _ [] = None" |
"list_map_lookup eq k (y#ys) = 
     (if eq (fst y) k then Some (snd y) else list_map_lookup eq k ys)"


primrec list_map_update_aux :: "('k \<Rightarrow> 'k \<Rightarrow> bool) \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 
    ('k,'v) list_map \<Rightarrow> ('k,'v) list_map \<Rightarrow> ('k,'v) list_map"where
"list_map_update_aux eq k v [] accu = (k,v) # accu" |
"list_map_update_aux eq k v (x#xs) accu = 
    (if eq (fst x) k
        then (k,v) # xs @ accu 
        else list_map_update_aux eq k v xs (x#accu))"

definition "list_map_update eq k v m \<equiv> 
    list_map_update_aux eq k v m []"

primrec list_map_delete_aux :: "('k \<Rightarrow> 'k \<Rightarrow> bool) \<Rightarrow> 'k \<Rightarrow> 
    ('k, 'v) list_map \<Rightarrow> ('k, 'v) list_map \<Rightarrow> ('k, 'v) list_map" where
"list_map_delete_aux eq k [] accu = accu" |
"list_map_delete_aux eq k (x#xs) accu =
    (if eq (fst x) k
        then xs @ accu
        else list_map_delete_aux eq k xs (x#accu))"

definition "list_map_delete eq k m \<equiv> list_map_delete_aux eq k m []"

definition list_map_isEmpty :: "('k,'v) list_map \<Rightarrow> bool"
    where "list_map_isEmpty \<equiv> List.null"

definition list_map_isSng :: "('k,'v) list_map \<Rightarrow> bool"
    where "list_map_isSng m = (case m of [x] \<Rightarrow> True | _ \<Rightarrow> False)"

definition list_map_size :: "('k,'v) list_map \<Rightarrow> nat"
    where "list_map_size \<equiv> length"

definition list_map_iteratei :: "('k,'v) list_map \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow>
    (('k\<times>'v) \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'b"
    where "list_map_iteratei \<equiv> foldli"

definition list_map_to_list :: "('k,'v) list_map \<Rightarrow> ('k\<times>'v) list"
    where "list_map_to_list = id"


subsection \<open>Parametricity\<close>

lemma list_map_autoref_empty[autoref_rules]:
  "([], op_map_empty)\<in>\<langle>Rk,Rv\<rangle>list_map_rel"
  by (auto simp: list_map_rel_def br_def list_map_invar_def)

lemma param_list_map_lookup[param]:
  "(list_map_lookup,list_map_lookup) \<in> (Rk \<rightarrow> Rk \<rightarrow> bool_rel) \<rightarrow> 
       Rk \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel \<rightarrow> \<langle>Rv\<rangle>option_rel"
unfolding list_map_lookup_def[abs_def] by parametricity

lemma list_map_autoref_lookup_aux:
  assumes eq: "GEN_OP eq (=) (Rk\<rightarrow>Rk\<rightarrow>Id)"
  assumes K: "(k, k') \<in> Rk"
  assumes M: "(m, m') \<in> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel"
  shows "(list_map_lookup eq k m, op_map_lookup k' (map_of m'))
               \<in> \<langle>Rv\<rangle>option_rel"
unfolding op_map_lookup_def
proof (induction rule: list_rel_induct[OF M, case_names Nil Cons])
  case Nil
    show ?case by simp
next
  case (Cons x x' xs xs')
    from eq have eq': "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> Id" by simp
    with eq'[param_fo] and K  and Cons 
        show ?case by (force simp: prod_rel_def)
qed

lemma list_map_autoref_lookup[autoref_rules]:
  assumes "GEN_OP eq (=) (Rk\<rightarrow>Rk\<rightarrow>Id)"
  shows "(list_map_lookup eq, op_map_lookup) \<in> 
       Rk \<rightarrow> \<langle>Rk,Rv\<rangle>list_map_rel \<rightarrow> \<langle>Rv\<rangle>option_rel"
   by (force simp: list_map_rel_def br_def
             dest: list_map_autoref_lookup_aux[OF assms])



lemma param_list_map_update_aux[param]:
  "(list_map_update_aux,list_map_update_aux) \<in> (Rk \<rightarrow> Rk \<rightarrow> bool_rel) \<rightarrow> 
       Rk \<rightarrow> Rv \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel
        \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
unfolding list_map_update_aux_def[abs_def] by parametricity

lemma param_list_map_update[param]:
  "(list_map_update,list_map_update) \<in> (Rk \<rightarrow> Rk \<rightarrow> bool_rel) \<rightarrow> 
       Rk \<rightarrow> Rv \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
unfolding list_map_update_def[abs_def] by parametricity


lemma list_map_autoref_update_aux1:
  assumes eq: "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> Id"
  assumes K: "(k, k') \<in> Rk"
  assumes V: "(v, v') \<in> Rv"
  assumes A: "(accu, accu') \<in> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel"
  assumes M: "(m, m') \<in> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel"
  shows "(list_map_update_aux eq k v m accu, 
          list_map_update_aux (=) k' v' m' accu')
               \<in> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel"
proof (insert A, induction arbitrary: accu accu' 
           rule: list_rel_induct[OF M, case_names Nil Cons])
  case Nil 
      thus ?case by (simp add: K V)
next
  case (Cons x x' xs xs')
    from eq have eq': "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> Id" by simp
    from eq'[param_fo] Cons(1) K 
        have [simp]: "(eq (fst x) k) \<longleftrightarrow> ((fst x') = k')" 
        by (force simp: prod_rel_def)
    show ?case
    proof (cases "eq (fst x) k")
      case False
        from Cons.prems and Cons.hyps have "(x # accu, x' # accu') \<in> 
            \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel" by parametricity
        from Cons.IH[OF this] and False show ?thesis by simp
    next
      case True
        from Cons.prems and Cons.hyps have "(xs @ accu, xs' @ accu') \<in>
            \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel" by parametricity
        with K and V and True show ?thesis by simp
  qed
qed

lemma list_map_autoref_update1[param]:
  assumes eq: "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> Id"
  shows "(list_map_update eq, list_map_update (=)) \<in> Rk \<rightarrow> Rv \<rightarrow> 
             \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel"
unfolding list_map_update_def[abs_def]
  by (intro fun_relI, erule (1) list_map_autoref_update_aux1[OF eq], 
      simp_all)


(* TODO: Move - Perhaps. *)
lemma map_add_sng_right: "m ++ [k\<mapsto>v] = m(k \<mapsto> v)"
    unfolding map_add_def by force
lemma map_add_sng_right': 
    "m ++ (\<lambda>a. if a = k then Some v else None) = m(k \<mapsto> v)"
    unfolding map_add_def by force

lemma list_map_autoref_update_aux2:
  assumes K: "(k, k') \<in> Id"
  assumes V: "(v, v') \<in> Id"
  assumes A: "(accu, accu') \<in> br map_of list_map_invar"
  assumes A1: "distinct (map fst (m @ accu))"
  assumes A2: "k \<notin> set (map fst accu)"
  assumes M: "(m, m') \<in> br map_of list_map_invar"
  shows "(list_map_update_aux (=) k v m accu, 
          accu' ++ op_map_update k' v' m')
               \<in> br map_of list_map_invar" (is "(?f m accu, _) \<in> _")
using M A A1 A2
proof (induction m arbitrary: accu accu' m')
  case Nil
    with K V show ?case by (auto simp: br_def list_map_invar_def 
        map_add_sng_right')
next
  case (Cons x xs accu accu' m')
    from Cons.prems have A: "m' = map_of (x#xs)" "accu' = map_of accu"
        unfolding br_def by simp_all
    show ?case
    proof (cases "(fst x) =  k")
      case True
        hence "((k, v) # xs @ accu, accu' ++ op_map_update k' v' m')
                   \<in> br map_of list_map_invar"
            using K V Cons.prems(3,4) unfolding br_def
            by (force simp add: A list_map_invar_def)
        also from True have "(k,v) # xs @ accu = ?f (x # xs) accu" by simp
        finally show ?thesis .
    next
      case False
        from Cons.prems(1) have B: "(xs, map_of xs) \<in> br map_of 
            list_map_invar"by (simp add: br_def list_map_invar_def)
        from Cons.prems(2,3) have C: "(x#accu, map_of (x#accu)) \<in> br map_of
            list_map_invar" by (simp add: br_def list_map_invar_def)
        from Cons.prems(3) have D: "distinct (map fst (xs @ x # accu))" 
            by simp
        from Cons.prems(4) and False have E: "k \<notin> set (map fst (x # accu))"
            by simp
        note Cons.IH[OF B C D E]
        also from False have "?f xs (x#accu) = ?f (x#xs) accu" by simp
        also from distinct_map_fstD[OF D] 
            have F: "\<And>z. (fst x, z) \<in> set xs \<Longrightarrow> z = snd x" by force
        have "map_of (x # accu) ++ op_map_update k' v' (map_of xs) = 
                  accu' ++ op_map_update k' v' m'"
            by (intro ext, auto simp: A F map_add_def 
                    dest: map_of_SomeD split: option.split)
        finally show ?thesis .
    qed
qed

lemma list_map_autoref_update2[param]:
  shows "(list_map_update (=), op_map_update) \<in> Id \<rightarrow> Id \<rightarrow> 
             br map_of list_map_invar \<rightarrow> br map_of list_map_invar"
unfolding list_map_update_def[abs_def]
apply (intro fun_relI)
apply (drule list_map_autoref_update_aux2
                 [where accu="[]" and accu'="Map.empty"])
apply (auto simp: br_def list_map_invar_def)
done

lemma list_map_autoref_update[autoref_rules]:
  assumes eq: "GEN_OP eq (=) (Rk\<rightarrow>Rk\<rightarrow>Id)"
  shows "(list_map_update eq, op_map_update) \<in>
      Rk \<rightarrow> Rv \<rightarrow> \<langle>Rk,Rv\<rangle>list_map_rel \<rightarrow> \<langle>Rk,Rv\<rangle>list_map_rel"
unfolding list_map_rel_def
apply (intro fun_relI, elim relcompE, intro relcompI, clarsimp)
apply (erule (2) list_map_autoref_update1[param_fo, OF eq[simplified]])
apply (rule list_map_autoref_update2[param_fo], simp_all)
done

context begin interpretation autoref_syn .
lemma list_map_autoref_update_dj[autoref_rules]:
    assumes "PRIO_TAG_OPTIMIZATION"
    assumes new: "SIDE_PRECOND_OPT (k' \<notin> dom m')"
    assumes K: "(k,k')\<in>Rk" and V: "(v,v')\<in>Rv"
    assumes M: "(l,m')\<in>\<langle>Rk, Rv\<rangle>list_map_rel"
    defines "R_annot \<equiv> Rk \<rightarrow> Rv \<rightarrow> \<langle>Rk,Rv\<rangle>list_map_rel \<rightarrow> \<langle>Rk,Rv\<rangle>list_map_rel"
    shows "
      ((k, v)#l, 
        (OP op_map_update:::R_annot)$k'$v'$m')
      \<in> \<langle>Rk,Rv\<rangle>list_map_rel"
proof -
  from M obtain l' where A: "(l,l') \<in> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel" and
      B: "(l',m') \<in> br map_of list_map_invar"
      unfolding list_map_rel_def by blast
  hence "((k,v)#l, (k',v')#l')\<in>\<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel"
      and "((k',v')#l', m'(k' \<mapsto> v')) \<in> br map_of list_map_invar"
      using assms unfolding br_def list_map_invar_def
          by (simp_all add: dom_map_of_conv_image_fst)
  thus ?thesis 
    unfolding autoref_tag_defs
    by (force simp: list_map_rel_def)
qed
end

lemma param_list_map_delete_aux[param]:
  "(list_map_delete_aux,list_map_delete_aux) \<in> (Rk \<rightarrow> Rk \<rightarrow> bool_rel) \<rightarrow> 
       Rk \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel
        \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
unfolding list_map_delete_aux_def[abs_def] by parametricity

lemma param_list_map_delete[param]:
  "(list_map_delete,list_map_delete) \<in> (Rk \<rightarrow> Rk \<rightarrow> bool_rel) \<rightarrow> 
       Rk \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
unfolding list_map_delete_def[abs_def] by parametricity

lemma list_map_autoref_delete_aux1:
  assumes eq: "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> Id"
  assumes K: "(k, k') \<in> Rk"
  assumes A: "(accu, accu') \<in> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel"
  assumes M: "(m, m') \<in> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel"
  shows "(list_map_delete_aux eq k m accu, 
          list_map_delete_aux (=) k' m' accu')
               \<in> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel"
proof (insert A, induction arbitrary: accu accu' 
           rule: list_rel_induct[OF M, case_names Nil Cons])
  case Nil 
      thus ?case by (simp add: K)
next
  case (Cons x x' xs xs')
    from eq have eq': "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> Id" by simp
    from eq'[param_fo] Cons(1) K 
        have [simp]: "(eq (fst x) k) \<longleftrightarrow> ((fst x') = k')" 
        by (force simp: prod_rel_def)
    show ?case
    proof (cases "eq (fst x) k")
      case False
        from Cons.prems and Cons.hyps have "(x # accu, x' # accu') \<in> 
            \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel" by parametricity
        from Cons.IH[OF this] and False show ?thesis by simp
    next
      case True
        from Cons.prems and Cons.hyps have "(xs @ accu, xs' @ accu') \<in>
            \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel" by parametricity
        with K and True show ?thesis by simp
  qed
qed

lemma list_map_autoref_delete1[param]:
  assumes eq: "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> Id"
  shows "(list_map_delete eq, list_map_delete (=)) \<in> Rk \<rightarrow> 
             \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel"
unfolding list_map_delete_def[abs_def]
  by (intro fun_relI, erule list_map_autoref_delete_aux1[OF eq], 
      simp_all)


lemma list_map_autoref_delete_aux2:
  assumes K: "(k, k') \<in> Id"
  assumes A: "(accu, accu') \<in> br map_of list_map_invar"
  assumes A1: "distinct (map fst (m @ accu))"
  assumes A2: "k \<notin> set (map fst accu)"
  assumes M: "(m, m') \<in> br map_of list_map_invar"
  shows "(list_map_delete_aux (=) k m accu, 
          accu' ++ op_map_delete k' m')
               \<in> br map_of list_map_invar" (is "(?f m accu, _) \<in> _")
using M A A1 A2
proof (induction m arbitrary: accu accu' m')
  case Nil
    with K show ?case by (auto simp: br_def list_map_invar_def 
        map_add_sng_right')
next
  case (Cons x xs accu accu' m')
    from Cons.prems have A: "m' = map_of (x#xs)" "accu' = map_of accu"
        unfolding br_def by simp_all
    show ?case
    proof (cases "(fst x) =  k")
      case True
        with Cons.prems(3) have "map_of xs (fst x) = None" 
          by (induction xs, simp_all)
        with fun_upd_triv[of "map_of xs" "fst x"]
        have "map_of xs |` (- {fst x}) = map_of xs" 
          by (simp add: map_upd_eq_restrict)
        with True have"(xs @ accu, accu' ++ op_map_delete k' m')
                           \<in> br map_of list_map_invar"
            using K Cons.prems unfolding br_def
            by (auto simp add: A list_map_invar_def)
        thus ?thesis using True by simp
    next
      case False
        from False and K have [simp]: "fst x \<noteq> k'" by simp
        from Cons.prems(1) have B: "(xs, map_of xs) \<in> br map_of 
            list_map_invar"by (simp add: br_def list_map_invar_def)
        from Cons.prems(2,3) have C: "(x#accu, map_of (x#accu)) \<in> br map_of
            list_map_invar" by (simp add: br_def list_map_invar_def)
        from Cons.prems(3) have D: "distinct (map fst (xs @ x # accu))" 
            by simp
        from Cons.prems(4) and False have E: "k \<notin> set (map fst (x # accu))"
            by simp
        note Cons.IH[OF B C D E]
        also from False have "?f xs (x#accu) = ?f (x#xs) accu" by simp
        also from distinct_map_fstD[OF D] 
            have F: "\<And>z. (fst x, z) \<in> set xs \<Longrightarrow> z = snd x" by force

        from Cons.prems(3) have "map_of xs (fst x) = None"
            by (induction xs, simp_all)
        hence "map_of (x # accu) ++ op_map_delete k' (map_of xs) = 
               accu' ++ op_map_delete k' m'"
            apply (intro ext, simp add: map_add_def A
                                   split: option.split)
            apply (intro conjI impI allI)
            apply (auto simp: restrict_map_def)
            done
        finally show ?thesis .
    qed
qed

lemma list_map_autoref_delete2[param]:
  shows "(list_map_delete (=), op_map_delete) \<in> Id \<rightarrow> 
             br map_of list_map_invar \<rightarrow> br map_of list_map_invar"
unfolding list_map_delete_def[abs_def]
apply (intro fun_relI)
apply (drule list_map_autoref_delete_aux2
                 [where accu="[]" and accu'="Map.empty"])
apply (auto simp: br_def list_map_invar_def)
done

lemma list_map_autoref_delete[autoref_rules]:
  assumes eq: "GEN_OP eq (=) (Rk\<rightarrow>Rk\<rightarrow>Id)"
  shows "(list_map_delete eq, op_map_delete) \<in>
      Rk \<rightarrow> \<langle>Rk,Rv\<rangle>list_map_rel \<rightarrow> \<langle>Rk,Rv\<rangle>list_map_rel"
unfolding list_map_rel_def
apply (intro fun_relI, elim relcompE, intro relcompI, clarsimp)
apply (erule (1) list_map_autoref_delete1[param_fo, OF eq[simplified]])
apply (rule list_map_autoref_delete2[param_fo], simp_all)
done

lemma list_map_autoref_isEmpty[autoref_rules]:
  shows "(list_map_isEmpty, op_map_isEmpty) \<in>
             \<langle>Rk,Rv\<rangle>list_map_rel \<rightarrow> bool_rel"
unfolding list_map_isEmpty_def op_map_isEmpty_def[abs_def]
    list_map_rel_def br_def List.null_def[abs_def] by force

lemma param_list_map_isSng[param]:
  assumes "(l,l') \<in> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
  shows "(list_map_isSng l, list_map_isSng l') \<in> bool_rel"
unfolding list_map_isSng_def using assms by parametricity

(* TODO: clean up this mess *)
lemma list_map_autoref_isSng_aux:
  assumes "(l',m') \<in> br map_of list_map_invar"
  shows "(list_map_isSng l', op_map_isSng m') \<in> bool_rel"
using assms 
unfolding list_map_isSng_def op_map_isSng_def br_def list_map_invar_def
apply (clarsimp split: list.split)
apply (intro conjI impI allI)
apply (metis map_upd_nonempty)
apply blast
apply (simp, metis fun_upd_apply option.distinct(1))
done

lemma list_map_autoref_isSng[autoref_rules]:
  "(list_map_isSng, op_map_isSng) \<in> \<langle>Rk,Rv\<rangle>list_map_rel \<rightarrow> bool_rel"
  unfolding list_map_rel_def
  by (blast dest!: param_list_map_isSng list_map_autoref_isSng_aux)

lemma list_map_autoref_size_aux:
  assumes "distinct (map fst x)"
  shows "card (dom (map_of x)) = length x"
proof-
  have "card (dom (map_of x)) = card (map_to_set (map_of x))"
      by (simp add: card_map_to_set)
  also from assms have "... = card (set x)" 
      by (simp add: map_to_set_map_of)
  also from assms have "... = length x" 
      by (force simp: distinct_card dest!: distinct_mapI)
  finally show ?thesis .
qed

lemma param_list_map_size[param]:
  "(list_map_size, list_map_size) \<in> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel \<rightarrow> nat_rel"
  unfolding list_map_size_def[abs_def] by parametricity

lemma list_map_autoref_size[autoref_rules]:
  shows "(list_map_size, op_map_size) \<in>
             \<langle>Rk,Rv\<rangle>list_map_rel \<rightarrow> nat_rel"
unfolding list_map_size_def[abs_def] op_map_size_def[abs_def]
    list_map_rel_def br_def list_map_invar_def
    by (force simp: list_map_autoref_size_aux list_rel_imp_same_length)


lemma autoref_list_map_is_iterator[autoref_ga_rules]: 
  shows "is_map_to_list Rk Rv list_map_rel list_map_to_list"
unfolding is_map_to_list_def is_map_to_sorted_list_def
proof (clarify)
  fix l m'
  assume "(l,m') \<in> \<langle>Rk,Rv\<rangle>list_map_rel"
  then obtain l' where *: "(l,l')\<in>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel" "(l',m')\<in>br map_of list_map_invar" 
    unfolding list_map_rel_def by blast
  then have "RETURN l' \<le> it_to_sorted_list (key_rel (\<lambda>_ _. True)) (map_to_set m')"
      unfolding it_to_sorted_list_def
      apply (intro refine_vcg)
      unfolding br_def list_map_invar_def key_rel_def[abs_def]
      apply (auto intro: distinct_mapI simp: map_to_set_map_of)
      done
  with * show
      "\<exists>l'. (list_map_to_list l, l') \<in> \<langle>\<langle>Rk, Rv\<rangle>prod_rel\<rangle>list_rel \<and>
            RETURN l' \<le> it_to_sorted_list (key_rel (\<lambda>_ _. True)) 
                             (map_to_set m')"
    unfolding list_map_to_list_def by force
qed

lemma pi_list_map[icf_proper_iteratorI]: 
  "proper_it (list_map_iteratei m) (list_map_iteratei m)"
unfolding proper_it_def list_map_iteratei_def by blast

lemma pi'_list_map[icf_proper_iteratorI]: 
  "proper_it' list_map_iteratei list_map_iteratei"
  by (rule proper_it'I, rule pi_list_map)


primrec list_map_pick_remove where
  "list_map_pick_remove [] = undefined"
| "list_map_pick_remove (kv#l) = (kv,l)"

context begin interpretation autoref_syn .
  lemma list_map_autoref_pick_remove[autoref_rules]:
    assumes NE: "SIDE_PRECOND (m\<noteq>Map.empty)"
    assumes R: "(l,m)\<in>\<langle>Rk,Rv\<rangle>list_map_rel"
    defines "Rres \<equiv> \<langle>(Rk\<times>\<^sub>rRv) \<times>\<^sub>r \<langle>Rk,Rv\<rangle>list_map_rel\<rangle>nres_rel"
    shows "(
        RETURN (list_map_pick_remove l),
        (OP op_map_pick_remove ::: \<langle>Rk,Rv\<rangle>list_map_rel \<rightarrow> Rres)$m
      ) \<in> Rres"
  proof -
    from NE R obtain k v lr where 
      [simp]: "l=(k,v)#lr"
      by (cases l) (auto simp: list_map_rel_def br_def)
    
    thm list_map_rel_def
    from R obtain l' where 
      LL': "(l,l')\<in>\<langle>Rk\<times>\<^sub>rRv\<rangle>list_rel" and 
      L'M: "(l',m)\<in>br map_of list_map_invar"
      unfolding list_map_rel_def by auto
    from LL' obtain k' v' lr' where
      [simp]: "l' = (k',v')#lr'" and 
        KVR: "(k,k')\<in>Rk" "(v,v')\<in>Rv" and
        LRR: "(lr,lr')\<in>\<langle>Rk\<times>\<^sub>rRv\<rangle>list_rel"
      by (fastforce elim!: list_relE)
    
    from L'M have 
      MKV': "m k' = Some v'" and 
      LRR': "(lr',m|`(-{k'}))\<in>br map_of list_map_invar"
      by (auto 
        simp: restrict_map_def map_of_eq_None_iff br_def list_map_invar_def
        intro!: ext
        intro: sym)
      
    from LRR LRR' have LM: "(lr,m|`(-{k'}))\<in>\<langle>Rk,Rv\<rangle>list_map_rel"
      unfolding list_map_rel_def by auto

    show ?thesis
      apply (simp add: Rres_def)
      apply (refine_rcg SPEC_refine nres_relI refine_vcg)
      using LM KVR MKV'
      by auto
  qed
end

end
