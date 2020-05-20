(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
(*
  Changes since submission on 2009-11-26:

  2009-12-10: OrderedMap, algorithms for iterators, min, max, to_sorted_list

*)

section \<open>\isaheader{Generic Algorithms for Maps}\<close>
theory MapGA
imports SetIteratorCollectionsGA
begin

text_raw \<open>\label{thy:MapGA}\<close>

record ('k,'v,'s) map_basic_ops =
  bmap_op_\<alpha> :: "('k,'v,'s) map_\<alpha>"
  bmap_op_invar :: "('k,'v,'s) map_invar"
  bmap_op_empty :: "('k,'v,'s) map_empty"
  bmap_op_lookup :: "('k,'v,'s) map_lookup"
  bmap_op_update :: "('k,'v,'s) map_update"
  bmap_op_update_dj :: "('k,'v,'s) map_update_dj"
  bmap_op_delete :: "('k,'v,'s) map_delete"
  bmap_op_list_it :: "('k,'v,'s) map_list_it"
  
record ('k,'v,'s) omap_basic_ops = "('k,'v,'s) map_basic_ops" +
  bmap_op_ordered_list_it :: "'s \<Rightarrow> ('k,'v,('k\<times>'v) list) map_iterator"
  bmap_op_rev_list_it :: "'s \<Rightarrow> ('k,'v,('k\<times>'v) list) map_iterator"

locale StdBasicMapDefs = 
  poly_map_iteratei_defs "bmap_op_list_it ops" 
  for ops :: "('k,'v,'s,'more) map_basic_ops_scheme"
begin
  abbreviation \<alpha> where "\<alpha> == bmap_op_\<alpha> ops" 
  abbreviation invar where "invar == bmap_op_invar ops" 
  abbreviation empty where "empty == bmap_op_empty ops" 
  abbreviation lookup where "lookup == bmap_op_lookup ops" 
  abbreviation update where "update == bmap_op_update ops" 
  abbreviation update_dj where "update_dj == bmap_op_update_dj ops" 
  abbreviation delete where "delete == bmap_op_delete ops" 
  abbreviation list_it where "list_it == bmap_op_list_it ops" 
end

locale StdBasicOMapDefs = StdBasicMapDefs ops
  + poly_map_iterateoi_defs "bmap_op_ordered_list_it ops"
  + poly_map_rev_iterateoi_defs "bmap_op_rev_list_it ops"
  for ops :: "('k::linorder,'v,'s,'more) omap_basic_ops_scheme"
begin
  abbreviation ordered_list_it where "ordered_list_it 
    \<equiv> bmap_op_ordered_list_it ops"
  abbreviation rev_list_it where "rev_list_it 
    \<equiv> bmap_op_rev_list_it ops"
end

locale StdBasicMap = StdBasicMapDefs ops +
  map \<alpha> invar +
  map_empty \<alpha> invar empty +
  map_lookup \<alpha> invar lookup  +
  map_update \<alpha> invar update  +
  map_update_dj \<alpha> invar update_dj +
  map_delete \<alpha> invar delete  +
  poly_map_iteratei \<alpha> invar list_it
  for ops :: "('k,'v,'s,'more) map_basic_ops_scheme"
begin
  lemmas correct[simp] = empty_correct lookup_correct update_correct 
    update_dj_correct delete_correct
end


locale StdBasicOMap = 
  StdBasicOMapDefs ops +
  StdBasicMap ops +
  poly_map_iterateoi \<alpha> invar ordered_list_it +
  poly_map_rev_iterateoi \<alpha> invar rev_list_it
  for ops :: "('k::linorder,'v,'s,'more) omap_basic_ops_scheme"
begin
end

context StdBasicMapDefs begin
  definition "g_sng k v \<equiv> update k v (empty ())"
  definition "g_add m1 m2 \<equiv> iterate m2 (\<lambda>(k,v) \<sigma>. update k v \<sigma>) m1"

  definition 
    "g_sel m P \<equiv> 
      iteratei m (\<lambda>\<sigma>. \<sigma> = None) (\<lambda>x \<sigma>. if P x then Some x else None) None"

  definition "g_bex m P \<equiv> iteratei m (\<lambda>x. \<not>x) (\<lambda>kv \<sigma>. P kv) False"
  definition "g_ball m P \<equiv> iteratei m id (\<lambda>kv \<sigma>. P kv) True"

  definition "g_size m \<equiv> iterate m (\<lambda>_. Suc) (0::nat)"
  definition "g_size_abort b m \<equiv> iteratei m (\<lambda>s. s<b) (\<lambda>_. Suc) (0::nat)"

  definition "g_isEmpty m \<equiv> g_size_abort 1 m = 0"
  definition "g_isSng m \<equiv> g_size_abort 2 m = 1"

  definition "g_to_list m \<equiv> iterate m (#) []"

  definition "g_list_to_map l \<equiv> foldl (\<lambda>m (k,v). update k v m) (empty ()) 
    (rev l)"

  definition "g_add_dj m1 m2 \<equiv> iterate m2 (\<lambda>(k,v) \<sigma>. update_dj k v \<sigma>) m1"

  definition "g_restrict P m \<equiv> iterate m 
    (\<lambda>(k,v) \<sigma>. if P (k,v) then update_dj k v \<sigma> else \<sigma>) (empty ())"

  definition dflt_ops :: "('k,'v,'s) map_ops" 
    where [icf_rec_def]:
    "dflt_ops \<equiv> 
      \<lparr> 
        map_op_\<alpha> = \<alpha>,
        map_op_invar = invar,
        map_op_empty = empty,
        map_op_lookup = lookup,
        map_op_update = update,
        map_op_update_dj = update_dj,
        map_op_delete = delete,
        map_op_list_it = list_it,
        map_op_sng = g_sng,
        map_op_restrict = g_restrict, 
        map_op_add = g_add, 
        map_op_add_dj = g_add_dj, 
        map_op_isEmpty = g_isEmpty, 
        map_op_isSng = g_isSng, 
        map_op_ball = g_ball, 
        map_op_bex = g_bex, 
        map_op_size = g_size, 
        map_op_size_abort = g_size_abort, 
        map_op_sel = g_sel, 
        map_op_to_list = g_to_list, 
        map_op_to_map = g_list_to_map
      \<rparr>"

  local_setup \<open>Locale_Code.lc_decl_del @{term dflt_ops}\<close>

end

lemma update_dj_by_update: 
  assumes "map_update \<alpha> invar update"
  shows "map_update_dj \<alpha> invar update"
proof -
  interpret map_update \<alpha> invar update by fact
  show ?thesis 
    apply (unfold_locales)
    apply (auto simp add: update_correct)
    done
qed

lemma map_iterator_linord_is_it: 
  "map_iterator_linord m it \<Longrightarrow> map_iterator m it"
  unfolding set_iterator_def set_iterator_map_linord_def
  apply (erule set_iterator_genord.set_iterator_weaken_R)
  ..

lemma map_rev_iterator_linord_is_it: 
  "map_iterator_rev_linord m it \<Longrightarrow> map_iterator m it"
  unfolding set_iterator_def set_iterator_map_rev_linord_def
  apply (erule set_iterator_genord.set_iterator_weaken_R)
  ..

context StdBasicMap 
begin
  lemma g_sng_impl: "map_sng \<alpha> invar g_sng" 
    apply unfold_locales 
    apply (simp_all add: update_correct empty_correct g_sng_def)
    done

  lemma g_add_impl: "map_add \<alpha> invar g_add"
  proof
    fix m1 m2
    assume "invar m1" "invar m2"

    have A: "g_add m1 m2 = iterate_add_to_map m1 update (iteratei m2)"
      unfolding g_add_def iterate_add_to_map_def by simp
    have "\<alpha> (g_add m1 m2) = \<alpha> m1 ++ \<alpha> m2 \<and> invar (g_add m1 m2)"
      unfolding A
      apply (rule 
        iterate_add_to_map_correct[of \<alpha> invar update m1 "iteratei m2" "\<alpha> m2"])
      apply unfold_locales []
      apply fact
      apply (rule iteratei_correct, fact)
      done
    thus "\<alpha> (g_add m1 m2) = \<alpha> m1 ++ \<alpha> m2" "invar (g_add m1 m2)" by auto
  qed

  lemma g_sel_impl: "map_sel' \<alpha> invar g_sel"
  proof -
    have A: "\<And>m P. g_sel m P = iterate_sel_no_map (iteratei m) P"
      unfolding g_sel_def iterate_sel_no_map_def iterate_sel_def by simp

    { fix m P
      assume I: "invar m"
      note iterate_sel_no_map_correct[OF iteratei_correct[OF I], of P]
    }
    thus ?thesis
      apply unfold_locales
      unfolding A
      apply (simp add: Bex_def Ball_def image_iff map_to_set_def)
      apply clarify
      apply (metis option.exhaust prod.exhaust)
      apply (simp add: Bex_def Ball_def image_iff map_to_set_def)
      done
  qed
  
  lemma g_bex_impl: "map_bex \<alpha> invar g_bex"
    apply unfold_locales
    unfolding g_bex_def
    apply (rule_tac I="\<lambda>it \<sigma>. \<sigma> \<longleftrightarrow> (\<exists>kv\<in>it. P kv)" 
      in iteratei_rule_insert_P)
    by (auto simp: map_to_set_def)

  lemma g_ball_impl: "map_ball \<alpha> invar g_ball"
    apply unfold_locales
    unfolding g_ball_def
    apply (rule_tac I="\<lambda>it \<sigma>. \<sigma> \<longleftrightarrow> (\<forall>kv\<in>it. P kv)" 
      in iteratei_rule_insert_P)
    apply (auto simp: map_to_set_def)
    done

  lemma g_size_impl: "map_size \<alpha> invar g_size"
  proof 
    fix m
    assume I: "invar m"
    have A: "g_size m \<equiv> iterate_size (iteratei m)"
      unfolding g_size_def iterate_size_def by simp
  
    from iterate_size_correct [OF iteratei_correct[OF I]]
    show "g_size m = card (dom (\<alpha> m))"
      unfolding A
      by (simp_all add: card_map_to_set) 
  qed 

  lemma g_size_abort_impl: "map_size_abort \<alpha> invar g_size_abort"
  proof 
    fix s m
    assume I: "invar m"
    have A: "g_size_abort s m \<equiv> iterate_size_abort (iteratei m) s"
      unfolding g_size_abort_def iterate_size_abort_def by simp
  
    from iterate_size_abort_correct [OF iteratei_correct[OF I]]
    show "g_size_abort s m = min s (card (dom (\<alpha> m)))"
      unfolding A
      by (simp_all add: card_map_to_set) 
  qed 

  lemma g_isEmpty_impl: "map_isEmpty \<alpha> invar g_isEmpty"
  proof 
    fix m
    assume I: "invar m"
    interpret map_size_abort \<alpha> invar g_size_abort by (rule g_size_abort_impl)
    from size_abort_correct[OF I] have 
      "g_size_abort 1 m = min 1 (card (dom (\<alpha> m)))" .
    thus "g_isEmpty m = (\<alpha> m = Map.empty)" unfolding g_isEmpty_def
      by (auto simp: min_def card_0_eq[OF finite] I)
  qed

  lemma g_isSng_impl: "map_isSng \<alpha> invar g_isSng"
  proof 
    fix m
    assume I: "invar m"
    interpret map_size_abort \<alpha> invar g_size_abort by (rule g_size_abort_impl)
    from size_abort_correct[OF I] have 
      "g_size_abort 2 m = min 2 (card (dom (\<alpha> m)))" .
    thus "g_isSng m = (\<exists>k v. \<alpha> m = [k \<mapsto> v])" unfolding g_isSng_def
      by (auto simp: min_def I card_Suc_eq dom_eq_singleton_conv)
  qed
  
  lemma g_to_list_impl: "map_to_list \<alpha> invar g_to_list"
  proof 
    fix m 
    assume I: "invar m"

    have A: "g_to_list m = iterate_to_list (iteratei m)"
      unfolding g_to_list_def iterate_to_list_def by simp

    from iterate_to_list_correct [OF iteratei_correct[OF I]]
    have set_l_eq: "set (g_to_list m) = map_to_set (\<alpha> m)" and 
      dist_l: "distinct (g_to_list m)" unfolding A by simp_all

    from dist_l show dist_fst_l: "distinct (map fst (g_to_list m))"
      by (simp add: distinct_map set_l_eq map_to_set_def inj_on_def)
    
    from map_of_map_to_set[of "(g_to_list m)" "\<alpha> m", OF dist_fst_l] set_l_eq
    show "map_of (g_to_list m) = \<alpha> m" by simp
  qed

  lemma g_list_to_map_impl: "list_to_map \<alpha> invar g_list_to_map"
  proof -
    {
      fix m0 l
      assume "invar m0"
      hence "invar (foldl (\<lambda>s (k,v). update k v s) m0 l) \<and> 
        \<alpha> (foldl (\<lambda>s (k,v). update k v s) m0 l) = \<alpha> m0 ++ map_of (rev l)"
      proof (induction l arbitrary: m0)
        case Nil thus ?case by simp
      next
        case (Cons kv l)
        obtain k v where [simp]: "kv=(k,v)" by (cases kv) auto
        have "invar (foldl (\<lambda>s (k, v). update k v s) m0 (kv # l))"
          apply simp
          apply (rule conjunct1[OF Cons.IH])
          apply (simp add: update_correct Cons.prems)
          done
        moreover have "\<alpha> (foldl (\<lambda>s (k, v). update k v s) m0 (kv # l)) =
          \<alpha> m0 ++ map_of (rev (kv # l))"
          apply simp
          apply (rule trans[OF conjunct2[OF Cons.IH]])
          apply (auto 
            simp: update_correct Cons.prems Map.map_add_def[abs_def]
            split: option.split
          )
          done
        ultimately show ?case
          by simp
      qed
    } thus ?thesis
      apply unfold_locales
      unfolding g_list_to_map_def
      apply (auto simp: empty_correct)
      done
  qed

  lemma g_add_dj_impl: "map_add_dj \<alpha> invar g_add_dj"
  proof
    fix m1 m2
    assume "invar m1" "invar m2" and DJ: "dom (\<alpha> m1) \<inter> dom (\<alpha> m2) = {}"

    have A: "g_add_dj m1 m2 = iterate_add_to_map m1 update_dj (iteratei m2)"
      unfolding g_add_dj_def iterate_add_to_map_def by simp
    have "\<alpha> (g_add_dj m1 m2) = \<alpha> m1 ++ \<alpha> m2 \<and> invar (g_add_dj m1 m2)"
      unfolding A
      apply (rule 
        iterate_add_to_map_dj_correct[
        of \<alpha> invar update_dj m1 "iteratei m2" "\<alpha> m2"])
      apply unfold_locales []
      apply fact
      apply (rule iteratei_correct, fact)
      using DJ apply (simp add: Int_ac)
      done
    thus "\<alpha> (g_add_dj m1 m2) = \<alpha> m1 ++ \<alpha> m2" "invar (g_add_dj m1 m2)" by auto
  qed
  
  lemma g_restrict_impl: "map_restrict \<alpha> invar \<alpha> invar g_restrict"
  proof 
    fix m P
    assume I: "invar m"

    have AUX: "\<And>k v it \<sigma>.
       \<lbrakk>it \<subseteq> {(k, v). \<alpha> m k = Some v}; \<alpha> m k = Some v; (k, v) \<notin> it;
        {(k, v). \<alpha> \<sigma> k = Some v} = it \<inter> Collect P\<rbrakk>
       \<Longrightarrow> k \<notin> dom (\<alpha> \<sigma>)"
    proof (rule ccontr, simp)
      fix k v it \<sigma>
      assume "k\<in>dom (\<alpha> \<sigma>)" 
      then obtain v' where "\<alpha> \<sigma> k = Some v'" by auto
      moreover assume "{(k, v). \<alpha> \<sigma> k = Some v} = it \<inter> Collect P"
      ultimately have MEM: "(k,v')\<in>it" by auto
      moreover assume "it \<subseteq> {(k, v). \<alpha> m k = Some v}" and "\<alpha> m k = Some v"
      ultimately have "v'=v" by auto
      moreover assume "(k,v)\<notin>it"
      moreover note MEM 
      ultimately show False by simp
    qed

    have "\<alpha> (g_restrict P m) = \<alpha> m |` {k. \<exists>v. \<alpha> m k = Some v \<and> P (k, v)} \<and>
      invar (g_restrict P m)"
      unfolding g_restrict_def
      apply (rule_tac I="\<lambda>it \<sigma>. invar \<sigma> 
        \<and> map_to_set (\<alpha> \<sigma>) = it \<inter> Collect P"
        in iterate_rule_insert_P)
      apply (auto simp: I empty_correct update_dj_correct map_to_set_def AUX)
      apply (auto split: if_split_asm)
      apply (rule ext)
      apply (auto simp: Map.restrict_map_def)
      apply force
      apply (rule ccontr)
      apply force
      done
    thus "\<alpha> (g_restrict P m) = \<alpha> m |` {k. \<exists>v. \<alpha> m k = Some v \<and> P (k, v)}"
      "invar (g_restrict P m)" by auto
  qed

  lemma dflt_ops_impl: "StdMap dflt_ops"
    apply (rule StdMap_intro)
    apply icf_locales
    apply (simp_all add: icf_rec_unf)
    apply (rule g_sng_impl g_restrict_impl g_add_impl g_add_dj_impl 
      g_isEmpty_impl g_isSng_impl g_ball_impl g_bex_impl g_size_impl
      g_size_abort_impl g_sel_impl g_to_list_impl g_list_to_map_impl)+
    done
end


context StdBasicOMapDefs 
begin
  definition 
    "g_min m P \<equiv> 
      iterateoi m (\<lambda>\<sigma>. \<sigma> = None) (\<lambda>x \<sigma>. if P x then Some x else None) None"

  definition 
    "g_max m P \<equiv> 
      rev_iterateoi m (\<lambda>\<sigma>. \<sigma> = None) (\<lambda>x \<sigma>. if P x then Some x else None) None"

  definition "g_to_sorted_list m \<equiv> rev_iterateo m (#) []"
  definition "g_to_rev_list m \<equiv> iterateo m (#) []"

  definition dflt_oops :: "('k,'v,'s) omap_ops" 
    where [icf_rec_def]:
    "dflt_oops \<equiv> map_ops.extend dflt_ops
      \<lparr> 
        map_op_ordered_list_it = ordered_list_it,
        map_op_rev_list_it = rev_list_it,
        map_op_min = g_min,
        map_op_max = g_max,
        map_op_to_sorted_list = g_to_sorted_list,
        map_op_to_rev_list = g_to_rev_list
      \<rparr>"
  local_setup \<open>Locale_Code.lc_decl_del @{term dflt_oops}\<close>

end

context StdBasicOMap 
begin
  lemma g_min_impl: "map_min \<alpha> invar g_min"
  proof 
    fix m P

    assume I: "invar m"
  
    from iterateoi_correct[OF I]
    have iti': "map_iterator_linord (iterateoi m) (\<alpha> m)" by simp
    note sel_correct = iterate_sel_no_map_map_linord_correct[OF iti', of P]

    have A: "g_min m P = iterate_sel_no_map (iterateoi m) P"
      unfolding g_min_def iterate_sel_no_map_def iterate_sel_def by simp
  
    { assume "rel_of (\<alpha> m) P \<noteq> {}"
      with sel_correct 
      show "g_min m P \<in> Some ` rel_of (\<alpha> m) P"
        unfolding A
        by (auto simp add: image_iff rel_of_def)
    }

    { assume "rel_of (\<alpha> m) P = {}"        
       with sel_correct show "g_min m P = None"
        unfolding A
        by (auto simp add: image_iff rel_of_def)
    }

    { fix k v
      assume "(k, v) \<in> rel_of (\<alpha> m) P"
      with sel_correct show "fst (the (g_min m P)) \<le> k"
        unfolding A
        by (auto simp add: image_iff rel_of_def)
    }
  qed

  lemma g_max_impl: "map_max \<alpha> invar g_max"
  proof 
    fix m P

    assume I: "invar m"
  
    from rev_iterateoi_correct[OF I]
    have iti': "map_iterator_rev_linord (rev_iterateoi m) (\<alpha> m)" by simp
    note sel_correct = iterate_sel_no_map_map_rev_linord_correct[OF iti', of P]

    have A: "g_max m P = iterate_sel_no_map (rev_iterateoi m) P"
      unfolding g_max_def iterate_sel_no_map_def iterate_sel_def by simp
  
    { assume "rel_of (\<alpha> m) P \<noteq> {}"
      with sel_correct 
      show "g_max m P \<in> Some ` rel_of (\<alpha> m) P"
        unfolding A
        by (auto simp add: image_iff rel_of_def)
    }

    { assume "rel_of (\<alpha> m) P = {}"        
       with sel_correct show "g_max m P = None"
        unfolding A
        by (auto simp add: image_iff rel_of_def)
    }

    { fix k v
      assume "(k, v) \<in> rel_of (\<alpha> m) P"
      with sel_correct show "fst (the (g_max m P)) \<ge> k"
        unfolding A
        by (auto simp add: image_iff rel_of_def)
    }
  qed

  lemma g_to_sorted_list_impl: "map_to_sorted_list \<alpha> invar g_to_sorted_list"
  proof 
    fix m
    assume I: "invar m"
    note iti = rev_iterateoi_correct[OF I]
    from iterate_to_list_map_rev_linord_correct[OF iti]
    show "sorted (map fst (g_to_sorted_list m))" 
         "distinct (map fst (g_to_sorted_list m))"
         "map_of (g_to_sorted_list m) = \<alpha> m" 
      unfolding g_to_sorted_list_def iterate_to_list_def by simp_all
  qed

  lemma g_to_rev_list_impl: "map_to_rev_list \<alpha> invar g_to_rev_list"
  proof 
    fix m
    assume I: "invar m"
    note iti = iterateoi_correct[OF I]
    from iterate_to_list_map_linord_correct[OF iti]
    show "sorted (rev (map fst (g_to_rev_list m)))" 
         "distinct (map fst (g_to_rev_list m))"
         "map_of (g_to_rev_list m) = \<alpha> m" 
      unfolding g_to_rev_list_def iterate_to_list_def 
      by (simp_all add: rev_map)
  qed
  
  lemma dflt_oops_impl: "StdOMap dflt_oops"
  proof -
    interpret aux: StdMap dflt_ops by (rule dflt_ops_impl)

    show ?thesis
      apply (rule StdOMap_intro)
      apply icf_locales
      apply (simp_all add: icf_rec_unf)
      apply (rule g_min_impl)
      apply (rule g_max_impl)
      apply (rule g_to_sorted_list_impl)
      apply (rule g_to_rev_list_impl)
      done
  qed

end

locale g_image_filter_defs_loc = 
  m1: StdMapDefs ops1 + 
  m2: StdMapDefs ops2
  for ops1 :: "('k1,'v1,'s1,'m1) map_ops_scheme"
  and ops2 :: "('k2,'v2,'s2,'m2) map_ops_scheme"
begin
  definition "g_image_filter f m1 \<equiv> m1.iterate m1 (\<lambda>kv \<sigma>. case f kv of 
      None => \<sigma>
    | Some (k',v') => m2.update_dj k' v' \<sigma>
    ) (m2.empty ())"
end

locale g_image_filter_loc = g_image_filter_defs_loc ops1 ops2 + 
  m1: StdMap ops1 + 
  m2: StdMap ops2
  for ops1 :: "('k1,'v1,'s1,'m1) map_ops_scheme"
  and ops2 :: "('k2,'v2,'s2,'m2) map_ops_scheme"
begin
  lemma g_image_filter_impl: 
    "map_image_filter m1.\<alpha> m1.invar m2.\<alpha> m2.invar g_image_filter"
  proof 
    fix m k' v' and f :: "('k1 \<times> 'v1) \<Rightarrow> ('k2 \<times> 'v2) option"
    assume invar_m: "m1.invar m" and
           unique_f: "transforms_to_unique_keys (m1.\<alpha> m) f"
    
    have A: "g_image_filter f m = 
      iterate_to_map m2.empty m2.update_dj (
        set_iterator_image_filter f (m1.iteratei m))" 
      unfolding g_image_filter_def iterate_to_map_alt_def 
        set_iterator_image_filter_def case_prod_beta
      by simp
  
    from m1.iteratei_correct[OF invar_m] 
    have iti_m: "map_iterator (m1.iteratei m) (m1.\<alpha> m)" by simp

    from unique_f have inj_on_f: "inj_on f (map_to_set (m1.\<alpha> m) \<inter> dom f)"
      unfolding transforms_to_unique_keys_def inj_on_def Ball_def map_to_set_def
      by auto (metis option.inject)

    define vP where "vP k v \<longleftrightarrow> (\<exists>k' v'. m1.\<alpha> m k' = Some v' \<and> f (k', v') = Some (k, v))" for k v
    have vP_intro: "\<And>k v. (\<exists>k' v'. m1.\<alpha> m k' = Some v' 
        \<and> f (k', v') = Some (k, v)) \<longleftrightarrow> vP k v"
      unfolding vP_def by simp
    { fix k v
      have "Eps_Opt (vP k) = Some v \<longleftrightarrow> vP k v"
        using unique_f unfolding vP_def transforms_to_unique_keys_def 
        apply (rule_tac Eps_Opt_eq_Some)
        apply (metis prod.inject option.inject)
      done
    } note Eps_vP_elim[simp] = this
    have map_intro: "{y. \<exists>x. x \<in> map_to_set (m1.\<alpha> m) \<and> f x = Some y} 
      = map_to_set (\<lambda>k. Eps_Opt (vP k))"
      by (simp add: map_to_set_def vP_intro set_eq_iff split: prod.splits)

    from set_iterator_image_filter_correct [OF iti_m, OF inj_on_f, 
      unfolded map_intro] 
    have iti_filter: "map_iterator (set_iterator_image_filter f (m1.iteratei m))
          (\<lambda>k. Eps_Opt (vP k))" by auto

    have upd: "map_update_dj m2.\<alpha> m2.invar m2.update_dj" by unfold_locales
    have emp: "map_empty m2.\<alpha> m2.invar m2.empty" by unfold_locales
  
    from iterate_to_map_correct[OF upd emp iti_filter] show
      "map_op_invar ops2 (g_image_filter f m) \<and>
          (map_op_\<alpha> ops2 (g_image_filter f m) k' = Some v') =
          (\<exists>k v. map_op_\<alpha> ops1 m k = Some v \<and> f (k, v) = Some (k', v'))"
      unfolding A vP_def[symmetric]
      by (simp add: vP_intro)
  
  qed
end

sublocale g_image_filter_loc 
  < map_image_filter m1.\<alpha> m1.invar m2.\<alpha> m2.invar g_image_filter
  by (rule g_image_filter_impl)


locale g_value_image_filter_defs_loc = 
  m1: StdMapDefs ops1 + 
  m2: StdMapDefs ops2
  for ops1 :: "('k,'v1,'s1,'m1) map_ops_scheme"
  and ops2 :: "('k,'v2,'s2,'m2) map_ops_scheme"
begin
  definition "g_value_image_filter f m1 \<equiv> m1.iterate m1 (\<lambda>(k,v) \<sigma>. 
    case f k v of 
      None => \<sigma>
    | Some v' => m2.update_dj k v' \<sigma>
    ) (m2.empty ())"
  
end

(* TODO: Move to Misc *)
lemma restrict_map_dom_subset: "\<lbrakk> dom m \<subseteq> R\<rbrakk> \<Longrightarrow> m|`R = m"
  apply (rule ext)
  apply (auto simp: restrict_map_def)
  apply (case_tac "m x")
  apply auto
  done


locale g_value_image_filter_loc = g_value_image_filter_defs_loc ops1 ops2 + 
  m1: StdMap ops1 + 
  m2: StdMap ops2
  for ops1 :: "('k,'v1,'s1,'m1) map_ops_scheme"
  and ops2 :: "('k,'v2,'s2,'m2) map_ops_scheme"
begin
  lemma g_value_image_filter_impl: 
    "map_value_image_filter m1.\<alpha> m1.invar m2.\<alpha> m2.invar g_value_image_filter"
    apply unfold_locales
    unfolding g_value_image_filter_def
    apply (rule_tac I="\<lambda>it \<sigma>. m2.invar \<sigma> 
      \<and> m2.\<alpha> \<sigma> = (\<lambda>k. Option.bind (map_op_\<alpha> ops1 m k) (f k)) |` it"
      in m1.old_iterate_rule_insert_P)

    apply auto []
    apply (auto simp: m2.empty_correct) []
    defer
    apply simp []
    apply (rule restrict_map_dom_subset)
    apply (auto) []
    apply (case_tac "m1.\<alpha> m x")
    apply (auto) [2]

    apply (auto split: option.split simp: m2.update_dj_correct intro!: ext)
    apply (auto simp: restrict_map_def)
    done
end

sublocale g_value_image_filter_loc 
  < map_value_image_filter m1.\<alpha> m1.invar m2.\<alpha> m2.invar g_value_image_filter
  by (rule g_value_image_filter_impl)


end
