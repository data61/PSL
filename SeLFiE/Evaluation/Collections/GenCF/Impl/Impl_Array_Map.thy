section \<open>\isaheader{Array-Based Maps with Natural Number Keys}\<close>
theory Impl_Array_Map
imports 
  Automatic_Refinement.Automatic_Refinement
  "../../Lib/Diff_Array"
  "../../Iterator/Iterator"
  "../Gen/Gen_Map"
  "../Intf/Intf_Comp"
  "../Intf/Intf_Map"
begin

type_synonym 'v iam = "'v option array"

subsection \<open>Definitions\<close>

definition iam_\<alpha> :: "'v iam \<Rightarrow> nat \<rightharpoonup> 'v" where
  "iam_\<alpha> a i \<equiv> if i < array_length a then array_get a i else None"

lemma [code]: "iam_\<alpha> a i \<equiv> array_get_oo None a i"
  unfolding array_get_oo_def iam_\<alpha>_def .

abbreviation iam_invar :: "'v iam \<Rightarrow> bool" where "iam_invar \<equiv> \<lambda>_. True"

definition iam_empty :: "unit \<Rightarrow> 'v iam" 
  where "iam_empty \<equiv> \<lambda>_::unit. array_of_list []"

definition iam_lookup :: "nat \<Rightarrow> 'v iam \<rightharpoonup> 'v"
  where [code_unfold]: "iam_lookup k a \<equiv> iam_\<alpha> a k"

definition "iam_increment (l::nat) idx \<equiv> 
  max (idx + 1 - l) (2 * l + 3)"

lemma incr_correct: "\<not> idx < l \<Longrightarrow> idx < l + iam_increment l idx"
  unfolding iam_increment_def by auto

definition iam_update :: "nat \<Rightarrow> 'v \<Rightarrow> 'v iam \<Rightarrow> 'v iam"
  where "iam_update k v a \<equiv> let
    l = array_length a;
    a = if k < l then a else array_grow a (iam_increment l k) None
  in
    array_set a k (Some v)"

lemma [code]: "iam_update k v a \<equiv> array_set_oo 
  (\<lambda>_. let l=array_length a in 
         array_set (array_grow a (iam_increment l k) None) k (Some v))
  a k (Some v)"
  unfolding iam_update_def array_set_oo_def
  apply (rule eq_reflection)
  by auto


definition iam_delete :: "nat \<Rightarrow> 'v iam \<Rightarrow> 'v iam"
  where "iam_delete k a \<equiv> 
  if k<array_length a then array_set a k None else a"

lemma [code]: "iam_delete k a \<equiv> array_set_oo (\<lambda>_. a) a k None"
  unfolding iam_delete_def array_set_oo_def by auto

primrec iam_iteratei_aux 
  :: "nat \<Rightarrow> ('v iam) \<Rightarrow> ('\<sigma>\<Rightarrow>bool) \<Rightarrow> (nat \<times> 'v\<Rightarrow>'\<sigma>\<Rightarrow>'\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>" 
  where
    "iam_iteratei_aux 0 a c f \<sigma> = \<sigma>"
  | "iam_iteratei_aux (Suc i) a c f \<sigma> = (
      if c \<sigma> then   
        iam_iteratei_aux i a c f (
          case array_get a i of None \<Rightarrow> \<sigma> | Some x \<Rightarrow> f (i, x) \<sigma>
        )
      else \<sigma>)"

definition iam_iteratei :: "'v iam \<Rightarrow> (nat \<times> 'v,'\<sigma>) set_iterator" where 
  "iam_iteratei a = iam_iteratei_aux (array_length a) a"



subsection \<open>Parametricity\<close>

definition iam_rel_def_internal: 
  "iam_rel R \<equiv> \<langle>\<langle>R\<rangle> option_rel\<rangle> array_rel"
lemma iam_rel_def: "\<langle>R\<rangle> iam_rel = \<langle>\<langle>R\<rangle> option_rel\<rangle> array_rel"
    by (simp add: iam_rel_def_internal relAPP_def)

lemma iam_rel_sv[relator_props]:
  "single_valued Rv \<Longrightarrow> single_valued (\<langle>Rv\<rangle>iam_rel)"
  unfolding iam_rel_def
  by tagged_solver

lemma param_iam_\<alpha>[param]:
  "(iam_\<alpha>, iam_\<alpha>) \<in> \<langle>R\<rangle> iam_rel \<rightarrow> nat_rel \<rightarrow> \<langle>R\<rangle> option_rel"
  unfolding iam_\<alpha>_def[abs_def] iam_rel_def by parametricity

lemma param_iam_invar[param]:
  "(iam_invar, iam_invar) \<in> \<langle>R\<rangle> iam_rel \<rightarrow> bool_rel"
  unfolding iam_rel_def by parametricity

lemma param_iam_empty[param]: 
  "(iam_empty, iam_empty) \<in> unit_rel \<rightarrow> \<langle>R\<rangle>iam_rel"
    unfolding iam_empty_def[abs_def] iam_rel_def by parametricity

lemma param_iam_lookup[param]: 
  "(iam_lookup, iam_lookup) \<in> nat_rel \<rightarrow> \<langle>R\<rangle>iam_rel \<rightarrow> \<langle>R\<rangle>option_rel"
  unfolding iam_lookup_def[abs_def] 
  by parametricity

(* TODO: why does parametricity fail here? *)
lemma param_iam_increment[param]:
  "(iam_increment, iam_increment) \<in> nat_rel \<rightarrow> nat_rel \<rightarrow> nat_rel"
  unfolding iam_increment_def[abs_def] 
  by simp

(* TODO: The builtin "Let" rule for parametricity does some unpleasant things
         here, leading to an unprovable subgoal. Investigate this. *)
lemma param_iam_update[param]:
  "(iam_update, iam_update) \<in> nat_rel \<rightarrow> R \<rightarrow> \<langle>R\<rangle>iam_rel \<rightarrow> \<langle>R\<rangle>iam_rel"
unfolding iam_update_def[abs_def] iam_rel_def Let_def
apply parametricity
done

lemma param_iam_delete[param]:
  "(iam_delete, iam_delete) \<in> nat_rel \<rightarrow> \<langle>R\<rangle>iam_rel \<rightarrow> \<langle>R\<rangle>iam_rel"
  unfolding iam_delete_def[abs_def] iam_rel_def by parametricity 

lemma param_iam_iteratei_aux[param]:
  assumes I: "i \<le> array_length a"
  assumes IR: "(i,i') \<in> nat_rel"
  assumes AR: "(a,a') \<in> \<langle>Ra\<rangle>iam_rel"
  assumes CR: "(c,c') \<in> Rb \<rightarrow> bool_rel"
  assumes FR: "(f,f') \<in> \<langle>nat_rel,Ra\<rangle>prod_rel \<rightarrow> Rb \<rightarrow> Rb"
  assumes \<sigma>R: "(\<sigma>,\<sigma>') \<in> Rb"
  shows "(iam_iteratei_aux i a c f \<sigma>, iam_iteratei_aux i' a' c' f' \<sigma>') \<in> Rb"
  using assms
  unfolding iam_rel_def
  apply (induct i' arbitrary: i \<sigma> \<sigma>')
  apply (simp_all only: pair_in_Id_conv iam_iteratei_aux.simps)
  apply parametricity
  apply simp_all
  done

lemma param_iam_iteratei[param]:
  "(iam_iteratei,iam_iteratei) \<in> \<langle>Ra\<rangle>iam_rel \<rightarrow> (Rb \<rightarrow> bool_rel) \<rightarrow> 
      (\<langle>nat_rel,Ra\<rangle>prod_rel \<rightarrow> Rb \<rightarrow> Rb) \<rightarrow> Rb \<rightarrow> Rb"
  unfolding iam_iteratei_def[abs_def] 
  by parametricity (simp_all add: iam_rel_def)



subsection \<open>Correctness\<close>

definition "iam_rel' \<equiv> br iam_\<alpha> iam_invar"

lemma iam_empty_correct:
  "(iam_empty (), Map.empty) \<in>  iam_rel'" 
   by (simp add: iam_rel'_def br_def iam_\<alpha>_def[abs_def] iam_empty_def)

lemma iam_update_correct:
  "(iam_update,op_map_update) \<in> nat_rel \<rightarrow> Id \<rightarrow> iam_rel'  \<rightarrow> iam_rel'"
   by (auto simp: iam_rel'_def br_def Let_def array_get_array_set_other 
                  incr_correct iam_\<alpha>_def[abs_def] iam_update_def)

lemma iam_lookup_correct:
  "(iam_lookup,op_map_lookup) \<in> Id \<rightarrow> iam_rel' \<rightarrow> \<langle>Id\<rangle>option_rel"
   by (auto simp: iam_rel'_def br_def iam_lookup_def[abs_def])


lemma array_get_set_iff: "i<array_length a \<Longrightarrow> 
  array_get (array_set a i x) j = (if i=j then x else array_get a j)"
  by (auto simp: array_get_array_set_other)

lemma iam_delete_correct:
  "(iam_delete,op_map_delete) \<in> Id \<rightarrow> iam_rel' \<rightarrow> iam_rel'"
  unfolding iam_\<alpha>_def[abs_def] iam_delete_def[abs_def] iam_rel'_def br_def
  by (auto simp: Let_def array_get_set_iff)

definition iam_map_rel_def_internal: 
  "iam_map_rel Rk Rv \<equiv> 
    if Rk=nat_rel then \<langle>Rv\<rangle>iam_rel O iam_rel' else {}"
lemma iam_map_rel_def: 
  "\<langle>nat_rel,Rv\<rangle>iam_map_rel \<equiv> \<langle>Rv\<rangle>iam_rel O iam_rel'" 
  unfolding iam_map_rel_def_internal relAPP_def by simp


lemmas [autoref_rel_intf] = REL_INTFI[of "iam_map_rel" i_map]

lemma iam_map_rel_sv[relator_props]:
  "single_valued Rv \<Longrightarrow> single_valued (\<langle>nat_rel,Rv\<rangle>iam_map_rel)"
  unfolding iam_map_rel_def iam_rel'_def by tagged_solver

lemma iam_empty_impl: 
    "(iam_empty (), op_map_empty) \<in> \<langle>nat_rel,R\<rangle>iam_map_rel"
  unfolding iam_map_rel_def op_map_empty_def
  apply (intro relcompI)
  apply (rule param_iam_empty[THEN fun_relD], simp)
  apply (rule iam_empty_correct)
  done


lemma iam_lookup_impl: 
    "(iam_lookup, op_map_lookup) 
  \<in> nat_rel \<rightarrow> \<langle>nat_rel,R\<rangle>iam_map_rel \<rightarrow> \<langle>R\<rangle>option_rel"
unfolding iam_map_rel_def
apply (intro fun_relI)
apply (elim relcompE)
apply (frule iam_lookup_correct[param_fo], assumption)
apply (frule param_iam_lookup[param_fo], assumption)
apply simp
done

lemma iam_update_impl:
   "(iam_update, op_map_update) \<in> 
     nat_rel \<rightarrow> R \<rightarrow> \<langle>nat_rel,R\<rangle>iam_map_rel \<rightarrow> \<langle>nat_rel,R\<rangle>iam_map_rel"
  unfolding iam_map_rel_def
  apply (intro fun_relI, elim relcompEpair, intro relcompI)
  apply (erule (2) param_iam_update[param_fo])
  apply (rule iam_update_correct[param_fo])
  apply simp_all
  done

lemma iam_delete_impl: 
    "(iam_delete, op_map_delete) \<in>
        nat_rel \<rightarrow> \<langle>nat_rel,R\<rangle>iam_map_rel \<rightarrow> \<langle>nat_rel,R\<rangle>iam_map_rel"
  unfolding iam_map_rel_def
  apply (intro fun_relI, elim relcompEpair, intro relcompI)
  apply (erule (1) param_iam_delete[param_fo])
  apply (rule iam_delete_correct[param_fo])
  by simp_all

lemmas iam_map_impl =
  iam_empty_impl
  iam_lookup_impl
  iam_update_impl
  iam_delete_impl

declare iam_map_impl[autoref_rules]



subsection \<open>Iterator proofs\<close>

abbreviation "iam_to_list a \<equiv> it_to_list iam_iteratei a"

lemma distinct_iam_to_list_aux:
  shows "\<lbrakk>distinct xs; \<forall>(i,_)\<in>set xs. i \<ge> n\<rbrakk> \<Longrightarrow> 
        distinct (iam_iteratei_aux n a 
            (\<lambda>_.True) (\<lambda>x y. y @ [x]) xs)" 
   (is "\<lbrakk>_;_\<rbrakk> \<Longrightarrow> distinct (?iam_to_list_aux n xs)")
proof (induction n arbitrary: xs)
  case (0 xs) thus ?case by simp
next
  case (Suc i xs)
    show ?case 
    proof (cases "array_get a i")
      case None
        with Suc.IH[OF Suc.prems(1)] Suc.prems(2)
            show ?thesis by force
    next
      case (Some x)
        let ?xs' = "xs @ [(i,x)]"
        from Suc.prems have "distinct ?xs'" and 
            "\<forall>(i',x)\<in>set ?xs'. i' \<ge> i" by force+
        from Some and Suc.IH[OF this] show ?thesis by simp
  qed
qed

lemma distinct_iam_to_list:
  "distinct (iam_to_list a)"
unfolding it_to_list_def iam_iteratei_def
  by (force intro: distinct_iam_to_list_aux)

lemma iam_to_list_set_correct_aux:
  assumes "(a, m) \<in> iam_rel'"
  shows "\<lbrakk>n \<le> array_length a; map_to_set m - {(k,v). k < n} = set xs\<rbrakk>
         \<Longrightarrow> map_to_set m = 
             set (iam_iteratei_aux n a (\<lambda>_.True) (\<lambda>x y. y @ [x]) xs)"
proof (induction n arbitrary: xs)
  case (0 xs)
    thus ?case by simp
next
  case (Suc n xs)
    with assms have [simp]: "array_get a n = m n" 
        unfolding iam_rel'_def br_def iam_\<alpha>_def[abs_def] by simp
    show ?case 
    proof (cases "m n")
      case None
        with Suc.prems(2) have "map_to_set m - {(k,v). k < n} = set xs"
        unfolding map_to_set_def by (fastforce simp: less_Suc_eq)
        from None and Suc.IH[OF _ this] and Suc.prems(1) 
            show ?thesis by simp
    next
      case (Some x)
        let ?xs' = "xs @ [(n,x)]"
        from Some and Suc.prems(2)
            have "map_to_set m - {(k,v). k < n} = set ?xs'"
            unfolding map_to_set_def by (fastforce simp: less_Suc_eq)
        from Some and Suc.IH[OF _ this] and Suc.prems(1)
            show ?thesis by simp
    qed
qed

lemma iam_to_list_set_correct:
  assumes "(a, m) \<in> iam_rel'"
  shows "map_to_set m = set (iam_to_list a)"
proof-
  from assms 
      have A: "map_to_set m - {(k, v). k < array_length a} = set []"
      unfolding map_to_set_def iam_rel'_def br_def iam_\<alpha>_def[abs_def]
      by (force split: if_split_asm)
  with iam_to_list_set_correct_aux[OF assms _ A] show ?thesis
    unfolding it_to_list_def iam_iteratei_def by simp
qed

lemma iam_iteratei_aux_append:
  "n \<le> length xs \<Longrightarrow> iam_iteratei_aux n (Array (xs @ ys)) = 
             iam_iteratei_aux n (Array xs)"
apply (induction n)
apply force
apply (intro ext, auto split: option.split simp: nth_append)
done

lemma iam_iteratei_append: 
  "iam_iteratei (Array (xs @ [None])) c f \<sigma> =
       iam_iteratei (Array xs) c f \<sigma>"
  "iam_iteratei (Array (xs @ [Some x])) c f \<sigma> = 
       iam_iteratei (Array xs) c f 
       (if c \<sigma> then (f (length xs, x) \<sigma>) else \<sigma>)"
unfolding  iam_iteratei_def 
apply (cases "length xs")
apply (simp add: iam_iteratei_aux_append)
apply (force simp: nth_append iam_iteratei_aux_append) []
apply (cases "length xs")
apply (simp add: iam_iteratei_aux_append)
apply (force split: option.split 
             simp: nth_append iam_iteratei_aux_append) []
done


lemma iam_iteratei_aux_Cons:
  "n < array_length a \<Longrightarrow>
      iam_iteratei_aux n a (\<lambda>_. True) (\<lambda>x l. l @ [x]) (x#xs) =
      x # iam_iteratei_aux n a (\<lambda>_. True) (\<lambda>x l. l @ [x]) xs"
    by (induction n arbitrary: xs, auto split: option.split)

lemma iam_to_list_append: 
  "iam_to_list (Array (xs @ [None])) = iam_to_list (Array xs)"
  "iam_to_list (Array (xs @ [Some x])) = 
       (length xs, x) # iam_to_list (Array xs)"
unfolding  it_to_list_def iam_iteratei_def
apply (simp add: iam_iteratei_aux_append)
apply (simp add: iam_iteratei_aux_Cons)
apply (simp add: iam_iteratei_aux_append)
done
    
lemma autoref_iam_is_iterator[autoref_ga_rules]: 
  shows "is_map_to_list nat_rel Rv iam_map_rel iam_to_list"
  unfolding is_map_to_list_def is_map_to_sorted_list_def
proof (clarify)
  fix a m'
  assume "(a,m') \<in> \<langle>nat_rel,Rv\<rangle>iam_map_rel"
  then obtain a' where [param]: "(a,a')\<in>\<langle>Rv\<rangle>iam_rel" 
    and "(a',m')\<in>iam_rel'" unfolding iam_map_rel_def by blast
  
  have "(iam_to_list a, iam_to_list a') 
            \<in> \<langle>\<langle>nat_rel, Rv\<rangle>prod_rel\<rangle>list_rel" by parametricity

  moreover from distinct_iam_to_list and 
                iam_to_list_set_correct[OF \<open>(a',m')\<in>iam_rel'\<close>]
      have "RETURN (iam_to_list a') \<le> it_to_sorted_list
               (key_rel (\<lambda>_ _. True)) (map_to_set m')" 
      unfolding it_to_sorted_list_def key_rel_def[abs_def]
          by (force intro: refine_vcg)

  ultimately show "\<exists>l'. (iam_to_list a, l') \<in> 
                            \<langle>\<langle>nat_rel, Rv\<rangle>prod_rel\<rangle>list_rel
                    \<and> RETURN l' \<le> it_to_sorted_list (
                        key_rel (\<lambda>_ _. True)) (map_to_set m')" by blast
qed

(* We provide a ,,sorted'' iterator to simplify derivations of the
    generic algorithm library *)
lemmas [autoref_ga_rules] = 
  autoref_iam_is_iterator[unfolded is_map_to_list_def]

lemma iam_iteratei_altdef:
    "iam_iteratei a = foldli (iam_to_list a)" 
     (is "?f a = ?g (iam_to_list a)")
proof-
  obtain l where "a = Array l" by (cases a)
  have "?f (Array l) = ?g (iam_to_list (Array l))"
  proof (induction "length l" arbitrary: l)
    case (0 l)
      thus ?case by (intro ext, 
          simp add: iam_iteratei_def it_to_list_def)
  next
    case (Suc n l)
      hence "l \<noteq> []" and [simp]: "length l = Suc n" by force+
      with append_butlast_last_id have [simp]: 
          "butlast l @ [last l] = l" by simp
      with Suc have [simp]: "length (butlast l) = n" by simp
      note IH = Suc(1)[OF this[symmetric]]
      let ?l' = "iam_to_list (Array l)"

      show ?case
      proof (cases "last l")
        case None
          have "?f (Array l) = 
              ?f (Array (butlast l @ [last l]))" by simp
          also have "... = ?g (iam_to_list (Array (butlast l)))"
              by (force simp: None iam_iteratei_append IH)
          also have "iam_to_list (Array (butlast l)) = 
              iam_to_list (Array (butlast l @ [last l]))"
              using None by (simp add: iam_to_list_append)
          finally show "?f (Array l) = ?g ?l'" by simp
      next
        case (Some x)
          have "?f (Array l) = 
              ?f (Array (butlast l @ [last l]))" by simp
          also have "... = ?g (iam_to_list 
              (Array (butlast l @ [last l])))" 
              by (force simp: IH iam_iteratei_append 
                      iam_to_list_append Some)
          finally show ?thesis by simp
      qed
  qed
  thus ?thesis by (simp add: \<open>a = Array l\<close>)
qed


lemma pi_iam[icf_proper_iteratorI]: 
  "proper_it (iam_iteratei a) (iam_iteratei a)"
unfolding proper_it_def by (force simp: iam_iteratei_altdef)

lemma pi'_iam[icf_proper_iteratorI]: 
  "proper_it' iam_iteratei iam_iteratei"
  by (rule proper_it'I, rule pi_iam)

end
