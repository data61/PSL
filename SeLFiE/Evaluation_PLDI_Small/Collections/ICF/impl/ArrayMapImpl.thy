section \<open>\isaheader{Maps from Naturals by Arrays}\<close>
theory ArrayMapImpl
imports 
  "../spec/MapSpec"
  "../gen_algo/MapGA"
  "../../Lib/Diff_Array"
begin
  text_raw \<open>\label{thy:ArrayMapImpl}\<close>

(*@impl Map
  @type 'v iam
  @abbrv iam,im
  Maps of natural numbers implemented by arrays.
*)

  type_synonym 'v iam = "'v option array"

  subsection \<open>Definitions\<close>
  definition iam_\<alpha> :: "'v iam \<Rightarrow> nat \<rightharpoonup> 'v" where
    "iam_\<alpha> a i \<equiv> if i < array_length a then array_get a i else None"

  lemma [code]: "iam_\<alpha> a i \<equiv> array_get_oo None a i"
    unfolding iam_\<alpha>_def array_get_oo_def .

  abbreviation (input) iam_invar :: "'v iam \<Rightarrow> bool" 
    where "iam_invar \<equiv> \<lambda>_. True"

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
    array_set a k (Some v)
    "

  lemma [code]: "iam_update k v a \<equiv> array_set_oo 
    (\<lambda>_. array_set 
           (array_grow a (iam_increment (array_length a) k) None) k (Some v))
    a k (Some v)
    "
    unfolding iam_update_def array_set_oo_def
    apply (rule eq_reflection)
    apply (auto simp add: Let_def)
    done

  definition "iam_update_dj \<equiv> iam_update"

  definition iam_delete :: "nat \<Rightarrow> 'v iam \<Rightarrow> 'v iam"
    where "iam_delete k a \<equiv> 
    if k<array_length a then array_set a k None else a"

  lemma [code]: "iam_delete k a \<equiv> array_set_oo (\<lambda>_. a) a k None"
    unfolding iam_delete_def array_set_oo_def by auto

  fun iam_rev_iterateoi_aux 
    :: "nat \<Rightarrow> ('v iam) \<Rightarrow> ('\<sigma>\<Rightarrow>bool) \<Rightarrow> (nat \<times> 'v\<Rightarrow>'\<sigma>\<Rightarrow>'\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>" 
    where
      "iam_rev_iterateoi_aux 0 a c f \<sigma> = \<sigma>"
    | "iam_rev_iterateoi_aux i a c f \<sigma> = (
        if c \<sigma> then   
          iam_rev_iterateoi_aux (i - 1) a c f (
            case array_get a (i - 1) of None \<Rightarrow> \<sigma> | Some x \<Rightarrow> f (i - 1, x) \<sigma>
          )
        else \<sigma>)"

  definition iam_rev_iterateoi :: "'v iam \<Rightarrow> (nat \<times> 'v,'\<sigma>) set_iterator" where 
    "iam_rev_iterateoi a \<equiv> iam_rev_iterateoi_aux (array_length a) a"

  function iam_iterateoi_aux 
    :: "nat \<Rightarrow> nat \<Rightarrow> ('v iam) \<Rightarrow> ('\<sigma>\<Rightarrow>bool) \<Rightarrow> (nat \<times> 'v\<Rightarrow>'\<sigma>\<Rightarrow>'\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>" 
    where
      "iam_iterateoi_aux i len a c f \<sigma> =
        (if i \<ge> len \<or> \<not> c \<sigma> then \<sigma> else let
            \<sigma>' = (case array_get a i of 
              None \<Rightarrow> \<sigma> 
            | Some x \<Rightarrow> f (i,x) \<sigma>)
          in iam_iterateoi_aux (i + 1) len a c f \<sigma>')"
    by pat_completeness auto
  termination 
    by (relation "measure (\<lambda>(i,l,_). l - i)") auto

  declare iam_iterateoi_aux.simps[simp del]

  lemma iam_iterateoi_aux_csimps:
    "i \<ge> len \<Longrightarrow> iam_iterateoi_aux i len a c f \<sigma> = \<sigma>"
    "\<not> c \<sigma> \<Longrightarrow> iam_iterateoi_aux i len a c f \<sigma> = \<sigma>"
    "\<lbrakk> i< len; c \<sigma> \<rbrakk> \<Longrightarrow> iam_iterateoi_aux i len a c f \<sigma> = 
      (case array_get a i of
        None \<Rightarrow> iam_iterateoi_aux (i + 1) len a c f \<sigma>
      | Some x \<Rightarrow> iam_iterateoi_aux (i + 1) len a c f (f (i,x) \<sigma>))"
    apply (subst iam_iterateoi_aux.simps, simp)
    apply (subst iam_iterateoi_aux.simps, simp)
    apply (subst iam_iterateoi_aux.simps)
    apply (auto split: option.split_asm option.split)
    done

  definition iam_iterateoi :: "'v iam \<Rightarrow> (nat \<times> 'v,'\<sigma>) set_iterator" where 
    "iam_iterateoi a = iam_iterateoi_aux 0 (array_length a) a"

  lemma iam_empty_impl: "map_empty iam_\<alpha> iam_invar iam_empty"
    apply unfold_locales
    unfolding iam_\<alpha>_def[abs_def] iam_empty_def
    by auto

  lemma iam_lookup_impl: "map_lookup iam_\<alpha> iam_invar iam_lookup"
    apply unfold_locales
    unfolding iam_\<alpha>_def[abs_def] iam_lookup_def
    by auto
  
  lemma array_get_set_iff: "i<array_length a \<Longrightarrow> 
    array_get (array_set a i x) j = (if i=j then x else array_get a j)"
    by (auto simp: array_get_array_set_other)

  lemma iam_update_impl: "map_update iam_\<alpha> iam_invar iam_update"
    apply unfold_locales
    unfolding iam_\<alpha>_def[abs_def] iam_update_def
    apply (rule ext)
    apply (auto simp: Let_def array_get_set_iff incr_correct)
    done

  lemma iam_update_dj_impl: "map_update_dj iam_\<alpha> iam_invar iam_update_dj"
    apply (unfold iam_update_dj_def)
    apply (rule update_dj_by_update)
    apply (rule iam_update_impl)
    done

  lemma iam_delete_impl: "map_delete iam_\<alpha> iam_invar iam_delete"
    apply unfold_locales
    unfolding iam_\<alpha>_def[abs_def] iam_delete_def
    apply (rule ext)
    apply (auto simp: Let_def array_get_set_iff)
    done
  
  lemma iam_rev_iterateoi_aux_foldli_conv :
    "iam_rev_iterateoi_aux n a =
     foldli (List.map_filter (\<lambda>n. map_option (\<lambda>v. (n, v)) (array_get a n)) (rev [0..<n]))"
  by (induct n) (auto simp add: List.map_filter_def fun_eq_iff)

  lemma iam_rev_iterateoi_foldli_conv :
    "iam_rev_iterateoi a =
     foldli (List.map_filter 
       (\<lambda>n. map_option (\<lambda>v. (n, v)) (array_get a n)) 
       (rev [0..<(array_length a)]))"
    unfolding iam_rev_iterateoi_def iam_rev_iterateoi_aux_foldli_conv by simp

  lemma iam_rev_iterateoi_correct : 
  fixes m::"'a option array"
  defines "kvs \<equiv> List.map_filter 
    (\<lambda>n. map_option (\<lambda>v. (n, v)) (array_get m n)) (rev [0..<(array_length m)])"
  shows "map_iterator_rev_linord (iam_rev_iterateoi m) (iam_\<alpha> m)" 
  proof (rule map_iterator_rev_linord_I [of kvs])
    show "iam_rev_iterateoi m = foldli kvs"
      unfolding iam_rev_iterateoi_foldli_conv kvs_def by simp
  next
    define al where "al = array_length m"
    show dist_kvs: "distinct (map fst kvs)" and "sorted (rev (map fst kvs))"
      unfolding kvs_def al_def[symmetric]
      apply (induct al)
      apply (simp_all 
        add: List.map_filter_simps set_map_filter image_iff sorted_append
        split: option.split)
    done

    from dist_kvs
    have "\<And>i. map_of kvs i = iam_\<alpha> m i"
      unfolding kvs_def 
      apply (case_tac "array_get m i")
      apply (simp_all 
        add: iam_\<alpha>_def map_of_eq_None_iff set_map_filter image_iff)
    done
    thus "iam_\<alpha> m = map_of kvs" by auto 
  qed
 
  lemma iam_rev_iterateoi_impl: 
    "poly_map_rev_iterateoi iam_\<alpha> iam_invar iam_rev_iterateoi"
    apply unfold_locales
    apply (simp add: iam_\<alpha>_def[abs_def] dom_def)
    apply (simp add: iam_rev_iterateoi_correct)
    done

  lemma iam_iteratei_impl: 
    "poly_map_iteratei iam_\<alpha> iam_invar iam_rev_iterateoi"
  proof -
    interpret aux: poly_map_rev_iterateoi iam_\<alpha> iam_invar iam_rev_iterateoi 
      by (rule iam_rev_iterateoi_impl) 

    show ?thesis
      apply unfold_locales
      apply (rule map_rev_iterator_linord_is_it)
      by (rule aux.list_rev_it_correct)
  qed

  lemma iam_iterateoi_aux_foldli_conv :
    "iam_iterateoi_aux n (array_length a) a c f \<sigma> =
     foldli (List.map_filter (\<lambda>n. map_option (\<lambda>v. (n, v)) (array_get a n)) 
       ([n..<array_length a])) c f \<sigma>"
    thm iam_iterateoi_aux.induct
    apply (induct n "array_length a" a c f \<sigma> rule: iam_iterateoi_aux.induct)
    apply (subst iam_iterateoi_aux.simps)
    apply (auto split: option.split simp: map_filter_simps)
    apply (subst (2) upt_conv_Cons)
    apply simp
    apply (simp add: map_filter_simps)
    apply (subst (2) upt_conv_Cons)
    apply simp
    apply (simp add: map_filter_simps)
    done

  lemma iam_iterateoi_foldli_conv :
    "iam_iterateoi a =
     foldli (List.map_filter 
       (\<lambda>n. map_option (\<lambda>v. (n, v)) (array_get a n)) 
       ([0..<(array_length a)]))"
    apply (intro ext)
    unfolding iam_iterateoi_def iam_iterateoi_aux_foldli_conv
    by simp

  (* TODO: Move to Misc *)
  lemmas [simp] = map_filter_simps
  lemma map_filter_append[simp]: "List.map_filter f (la@lb) 
    = List.map_filter f la @ List.map_filter f lb"
    by (induct la) (auto split: option.split)

  lemma iam_iterateoi_correct: 
  fixes m::"'a option array"
  defines "kvs \<equiv> List.map_filter 
    (\<lambda>n. map_option (\<lambda>v. (n, v)) (array_get m n)) ([0..<(array_length m)])"
  shows "map_iterator_linord (iam_iterateoi m) (iam_\<alpha> m)" 
  proof (rule map_iterator_linord_I [of kvs])
    show "iam_iterateoi m = foldli kvs"
      unfolding iam_iterateoi_foldli_conv kvs_def by simp
  next
    define al where "al = array_length m"
    show dist_kvs: "distinct (map fst kvs)" and "sorted (map fst kvs)"
      unfolding kvs_def al_def[symmetric]
      apply (induct al)
      apply (simp_all 
        add: set_map_filter image_iff sorted_append
        split: option.split)
    done

    from dist_kvs
    have "\<And>i. map_of kvs i = iam_\<alpha> m i"
      unfolding kvs_def 
      apply (case_tac "array_get m i")
      apply (simp_all 
        add: iam_\<alpha>_def map_of_eq_None_iff set_map_filter image_iff)
    done
    thus "iam_\<alpha> m = map_of kvs" by auto 
  qed
 
  lemma iam_iterateoi_impl: 
    "poly_map_iterateoi iam_\<alpha> iam_invar iam_iterateoi"
    apply unfold_locales
    apply (simp add: iam_\<alpha>_def[abs_def] dom_def)
    apply (simp add: iam_iterateoi_correct)
    done

  definition iam_basic_ops :: "(nat,'a,'a iam) omap_basic_ops"
    where [icf_rec_def]: "iam_basic_ops \<equiv> \<lparr>
    bmap_op_\<alpha> = iam_\<alpha>,
    bmap_op_invar = \<lambda>_. True,
    bmap_op_empty = iam_empty,
    bmap_op_lookup = iam_lookup,
    bmap_op_update = iam_update,
    bmap_op_update_dj = iam_update_dj,
    bmap_op_delete = iam_delete,
    bmap_op_list_it = iam_rev_iterateoi,
    bmap_op_ordered_list_it = iam_iterateoi,
    bmap_op_rev_list_it = iam_rev_iterateoi
    \<rparr>"

  setup Locale_Code.open_block
  interpretation iam_basic: StdBasicOMap iam_basic_ops
    apply (rule StdBasicOMap.intro)
    apply (rule StdBasicMap.intro)
    apply (simp_all add: icf_rec_unf)
    apply (rule iam_empty_impl iam_lookup_impl iam_update_impl
      iam_update_dj_impl iam_delete_impl iam_iteratei_impl
      iam_iterateoi_impl iam_rev_iterateoi_impl)+
    done
  setup Locale_Code.close_block

  definition [icf_rec_def]: "iam_ops \<equiv> iam_basic.dflt_oops"

  setup Locale_Code.open_block
  interpretation iam: StdOMap iam_ops
    unfolding iam_ops_def
    by (rule iam_basic.dflt_oops_impl)
  interpretation iam: StdMap_no_invar iam_ops
    by unfold_locales (simp add: icf_rec_unf)
  setup Locale_Code.close_block
  setup \<open>ICF_Tools.revert_abbrevs "iam"\<close>

  lemma pi_iam[proper_it]: 
    "proper_it' iam_iterateoi iam_iterateoi"
    apply (rule proper_it'I)
    unfolding iam_iterateoi_foldli_conv
    by (rule icf_proper_iteratorI)

  lemma pi_iam_rev[proper_it]: 
    "proper_it' iam_rev_iterateoi iam_rev_iterateoi"
    apply (rule proper_it'I)
    unfolding iam_rev_iterateoi_foldli_conv
    by (rule icf_proper_iteratorI)

  interpretation pi_iam: proper_it_loc iam_iterateoi iam_iterateoi
    apply unfold_locales by (rule pi_iam)

  interpretation pi_iam_rev: proper_it_loc iam_rev_iterateoi iam_rev_iterateoi
    apply unfold_locales by (rule pi_iam_rev)

text \<open>Code generator test\<close>
definition "test_codegen \<equiv> (
  iam.add ,
  iam.add_dj ,
  iam.ball ,
  iam.bex ,
  iam.delete ,
  iam.empty ,
  iam.isEmpty ,
  iam.isSng ,
  iam.iterate ,
  iam.iteratei ,
  iam.iterateo ,
  iam.iterateoi ,
  iam.list_it ,
  iam.lookup ,
  iam.max ,
  iam.min ,
  iam.restrict ,
  iam.rev_iterateo ,
  iam.rev_iterateoi ,
  iam.rev_list_it ,
  iam.reverse_iterateo ,
  iam.reverse_iterateoi ,
  iam.sel ,
  iam.size ,
  iam.size_abort ,
  iam.sng ,
  iam.to_list ,
  iam.to_map ,
  iam.to_rev_list ,
  iam.to_sorted_list ,
  iam.update ,
  iam.update_dj)"

export_code test_codegen checking SML
    
end
