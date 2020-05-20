(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
section \<open>\isaheader{Implementation of a trie with explicit invariants}\<close>
theory Trie_Impl imports
  "../../Lib/Assoc_List"
  Trie.Trie
begin

subsection \<open>Interuptible iterator\<close>

fun iteratei_postfixed :: "'key list \<Rightarrow> ('key, 'val) trie \<Rightarrow> 
    ('key list \<times> 'val, '\<sigma>) set_iterator"
where
  "iteratei_postfixed ks (Trie vo ts) c f \<sigma> =
   (if c \<sigma> 
    then foldli ts c (\<lambda>(k, t) \<sigma>. iteratei_postfixed (k # ks) t c f \<sigma>)
           (case vo of None \<Rightarrow> \<sigma> | Some v \<Rightarrow> f (ks, v) \<sigma>) 
    else \<sigma>)"

definition iteratei :: "('key, 'val) trie \<Rightarrow> ('key list \<times> 'val, '\<sigma>) set_iterator"
where "iteratei t c f \<sigma> = iteratei_postfixed [] t c f \<sigma>"

lemma iteratei_postfixed_interrupt:
  "\<not> c \<sigma> \<Longrightarrow> iteratei_postfixed ks t c f \<sigma> = \<sigma>"
by(cases t) simp

lemma iteratei_interrupt:
  "\<not> c \<sigma> \<Longrightarrow> iteratei t c f \<sigma> = \<sigma>"
unfolding iteratei_def by (simp add: iteratei_postfixed_interrupt)

lemma iteratei_postfixed_alt_def :
  "iteratei_postfixed ks ((Trie vo ts)::('key, 'val) trie) =
   (set_iterator_union 
     (case_option set_iterator_emp (\<lambda>v. set_iterator_sng (ks, v)) vo) 
     (set_iterator_image snd
     (set_iterator_product (foldli ts) 
        (\<lambda>(k, t'). iteratei_postfixed (k # ks) t'))
     ))"
proof -
  have aux: "\<And>c f. (\<lambda>(k, t). iteratei_postfixed (k # ks) t c f) =
              (\<lambda>a. iteratei_postfixed (fst a # ks) (snd a) c f)"
    by auto

  show ?thesis
    apply (rule ext)+ apply (rename_tac c f \<sigma>)
    apply (simp add: set_iterator_product_def set_iterator_image_filter_def
                     set_iterator_union_def set_iterator_sng_def set_iterator_image_alt_def
                     case_prod_beta set_iterator_emp_def 
            split: option.splits)
    apply (simp add: aux)
  done
qed

lemma iteratei_postfixed_correct :
  assumes invar: "invar_trie (t :: ('key, 'val) trie)"
  shows "set_iterator ((iteratei_postfixed ks0 t)::('key list \<times> 'val, '\<sigma>) set_iterator)
           ((\<lambda>ksv. (rev (fst ksv) @ ks0, (snd ksv))) ` (map_to_set (lookup_trie t)))"
using invar
proof (induct t arbitrary: ks0)
  case (Trie vo kvs)
  note ind_hyp = Trie(1)
  note invar = Trie(2)

  from invar 
  have dist_fst_kvs : "distinct (map fst kvs)"
   and dist_kvs: "distinct kvs"
   and invar_child: "\<And>k t. (k, t) \<in> set kvs \<Longrightarrow> invar_trie t"
  by (simp_all add: Ball_def distinct_map)

  \<comment> \<open>root iterator\<close>
  define it_vo :: "('key list \<times> 'val, '\<sigma>) set_iterator"
    where "it_vo =
      (case vo of None \<Rightarrow> set_iterator_emp 
       | Some v \<Rightarrow> set_iterator_sng (ks0, v))"
  define vo_S where "vo_S = (case vo of None \<Rightarrow> {} | Some v \<Rightarrow> {(ks0, v)})"
  have it_vo_OK: "set_iterator it_vo vo_S"
    unfolding it_vo_def vo_S_def
    by (simp split: option.split 
             add: set_iterator_emp_correct set_iterator_sng_correct)

  \<comment> \<open>children iterator\<close>
  define it_prod :: "(('key \<times> ('key, 'val) trie) \<times> 'key list \<times> 'val, '\<sigma>) set_iterator"
    where "it_prod = set_iterator_product (foldli kvs) (\<lambda>(k, y). iteratei_postfixed (k # ks0) y)"

  define it_prod_S where "it_prod_S = (SIGMA kt:set kvs.
       (\<lambda>ksv. (rev (fst ksv) @ ((fst kt) # ks0), snd ksv)) `
       map_to_set (lookup_trie (snd kt)))"

  have it_prod_OK: "set_iterator it_prod it_prod_S"
  proof -
    from set_iterator_foldli_correct[OF dist_kvs]
    have it_foldli: "set_iterator (foldli kvs) (set kvs)" .

    { fix kt 
      assume kt_in: "kt \<in> set kvs"
      hence k_t_in: "(fst kt, snd kt) \<in> set kvs" by simp

      note ind_hyp [OF k_t_in, OF invar_child[OF k_t_in], of "fst kt # ks0"]
    } note it_child = this
       
    show ?thesis
      unfolding it_prod_def it_prod_S_def
      apply (rule set_iterator_product_correct [OF it_foldli])
      apply (insert it_child)
      apply (simp add: case_prod_beta)
    done
  qed

  have it_image_OK : "set_iterator (set_iterator_image snd it_prod) (snd ` it_prod_S)"
  proof (rule set_iterator_image_correct[OF it_prod_OK])
    from dist_fst_kvs
    have "\<And>k v1 v2. (k, v1) \<in> set kvs \<Longrightarrow> (k, v2) \<in> set kvs \<Longrightarrow> v1 = v2"
       by (induct kvs) (auto simp add: image_iff)
    thus "inj_on snd it_prod_S" 
      unfolding inj_on_def it_prod_S_def
      apply (simp add: image_iff Ball_def map_to_set_def)
      apply auto
    done
  qed auto

  \<comment> \<open>overall iterator\<close>
  have it_all_OK: "set_iterator 
      ((iteratei_postfixed ks0 (Trie vo kvs)):: ('key list \<times> 'val, '\<sigma>) set_iterator)
     (vo_S \<union> snd ` it_prod_S)"
    unfolding iteratei_postfixed_alt_def 
       it_vo_def[symmetric]
       it_prod_def[symmetric]
  proof (rule set_iterator_union_correct [OF it_vo_OK it_image_OK])
    show "vo_S \<inter> snd ` it_prod_S = {}"
      unfolding vo_S_def it_prod_S_def
      by (simp split: option.split add: set_eq_iff image_iff)
  qed

  \<comment> \<open>rewrite result set\<close>
  have it_set_rewr: "((\<lambda>ksv. (rev (fst ksv) @ ks0, snd ksv)) `
      map_to_set (lookup_trie (Trie vo kvs))) = (vo_S \<union> snd ` it_prod_S)"
    (is "?ls = ?rs")
    apply (simp add: map_to_set_def lookup_eq_Some_iff[OF invar]
                     set_eq_iff image_iff vo_S_def it_prod_S_def Ball_def Bex_def)
    apply (simp split: option.split del: ex_simps add: ex_simps[symmetric])
    apply (intro allI impI iffI)
    apply auto[]
    apply (metis append_Cons append_Nil append_assoc rev.simps)
  done
    
  \<comment> \<open>done\<close>
  show ?case
    unfolding it_set_rewr using it_all_OK by fast
qed

definition trie_reverse_key where
  "trie_reverse_key ksv = (rev (fst ksv), (snd ksv))"

lemma trie_reverse_key_alt_def[code] :
  "trie_reverse_key (ks, v) = (rev ks, v)"
unfolding trie_reverse_key_def by auto

lemma trie_reverse_key_reverse[simp] :
  "trie_reverse_key (trie_reverse_key ksv) = ksv"
by (simp add: trie_reverse_key_def)

lemma trie_iteratei_correct:
  assumes invar: "invar_trie (t :: ('key, 'val) trie)"
  shows "set_iterator ((iteratei t)::('key list \<times> 'val, '\<sigma>) set_iterator)
           (trie_reverse_key ` (map_to_set (lookup_trie t)))"
unfolding trie_reverse_key_def[abs_def] iteratei_def[abs_def]
using iteratei_postfixed_correct [OF invar, of "[]"]
by simp

hide_const (open) iteratei
hide_type (open) trie

end
