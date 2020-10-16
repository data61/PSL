(*  Title:       Isabelle Collections Library
    Author:      Andreas Lochbihler <andreas dot lochbihler at kit.edu>
    Maintainer:  Andreas Lochbihler <andreas dot lochbihler at kit.edu>
*)
section \<open>\isaheader{Map implementation via tries}\<close>
theory TrieMapImpl imports
  Trie2
  "../gen_algo/MapGA"
begin
(*@impl Map
  @type ('k,'v) tm
  @abbrv tm,t
  Maps over keys of type @{typ "'k list"} implemented by tries.
*)

subsection \<open>Operations\<close>

type_synonym ('k, 'v) tm = "('k, 'v) trie"

definition [icf_rec_def]: "tm_basic_ops \<equiv> \<lparr>
  bmap_op_\<alpha> = Trie2.lookup,
  bmap_op_invar = \<lambda>_. True,
  bmap_op_empty = (\<lambda>_::unit. Trie2.empty),
  bmap_op_lookup = (\<lambda>k m. Trie2.lookup m k),
  bmap_op_update = Trie2.update,
  bmap_op_update_dj = Trie2.update,
  bmap_op_delete = Trie2.delete,
  bmap_op_list_it = Trie2.iteratei
\<rparr>"


setup Locale_Code.open_block
interpretation tm_basic: StdBasicMap tm_basic_ops
  apply unfold_locales
  apply (simp_all 
      add: icf_rec_unf Trie2.finite_dom_lookup Trie2.iteratei_correct 
      add: map_upd_eq_restrict)
  done
setup Locale_Code.close_block

definition [icf_rec_def]: "tm_ops \<equiv> tm_basic.dflt_ops"

setup Locale_Code.open_block
interpretation tm: StdMap tm_ops 
  unfolding tm_ops_def
  by (rule tm_basic.dflt_ops_impl)
interpretation tm: StdMap_no_invar tm_ops 
  by unfold_locales (simp add: icf_rec_unf)
setup Locale_Code.close_block

setup \<open>ICF_Tools.revert_abbrevs "tm"\<close>

lemma pi_trie_impl[proper_it]: 
  shows "proper_it'
    ((Trie_Impl.iteratei) :: _ \<Rightarrow> (_,'\<sigma>a) set_iterator)
    ((Trie_Impl.iteratei) :: _ \<Rightarrow> (_,'\<sigma>b) set_iterator)"
  unfolding Trie_Impl.iteratei_def[abs_def]
proof (rule proper_it'I)
  (*note [[show_types, show_consts]]*)
  fix t :: "('k,'v) Trie.trie"
  {
    fix l and t :: "('k,'v) Trie.trie"
    have "proper_it ((Trie_Impl.iteratei_postfixed l t)
       :: (_,'\<sigma>a) set_iterator)
      ((Trie_Impl.iteratei_postfixed l t)
       :: (_,'\<sigma>b) set_iterator)"
    proof (induct t arbitrary: l)
      case (Trie vo kvs l)

      let ?ITA = "\<lambda>l t. (Trie_Impl.iteratei_postfixed l t)
        :: (_,'\<sigma>a) set_iterator"
      let ?ITB = "\<lambda>l t. (Trie_Impl.iteratei_postfixed l t)
        :: (_,'\<sigma>b) set_iterator"

      show ?case
        unfolding Trie_Impl.iteratei_postfixed_alt_def
        apply (rule pi_union)
        apply (auto split: option.split intro: icf_proper_iteratorI) []
      proof (rule pi_image)
        define bs where "bs = (\<lambda>(k,t). SOME l'::('k list \<times> 'v) list. 
          ?ITA (k#l) t = foldli l' \<and> ?ITB (k#l) t = foldli l')"

        have EQ1: "\<forall>(k,t)\<in>set kvs. ?ITA (k#l) t = foldli (bs (k,t))" and
          EQ2: "\<forall>(k,t)\<in>set kvs. ?ITB (k#l) t = foldli (bs (k,t))"
        proof (safe)
          fix k t
          assume A: "(k,t) \<in> set kvs"
          from Trie.hyps[OF A, of "k#l"] have 
            PI: "proper_it (?ITA (k#l) t) (?ITB (k#l) t)" 
            by assumption
          obtain l' where 
            "?ITA (k#l) t = foldli l'
          \<and> (?ITB (k#l) t) = foldli l'"
            by (blast intro: proper_itE[OF PI])
          thus "?ITA (k#l) t = foldli (bs (k,t))"
            "?ITB (k#l) t = foldli (bs (k,t))"
            unfolding bs_def
            apply auto
            apply (metis (lifting, full_types) someI_ex) 
            apply (metis (lifting, full_types) someI_ex) 
            done
        qed

        have PEQ1: "set_iterator_product (foldli kvs) (\<lambda>(k,t). ?ITA (k#l) t) 
          = set_iterator_product (foldli kvs) (\<lambda>kt. foldli (bs kt))"
          apply (rule set_iterator_product_eq2)
          using EQ1 by auto
        have PEQ2: "set_iterator_product (foldli kvs) (\<lambda>(k,t). ?ITB (k#l) t)
          = set_iterator_product (foldli kvs) (\<lambda>kt. foldli (bs kt))"
          apply (rule set_iterator_product_eq2)
          using EQ2 by auto
        show "proper_it
          (set_iterator_product (foldli kvs) (\<lambda>(k,t). ?ITA (k#l) t))
          (set_iterator_product (foldli kvs) (\<lambda>(k,t). ?ITB (k#l) t))"
          apply (subst PEQ1)
          apply (subst PEQ2)
          apply (auto simp: set_iterator_product_foldli_conv)
          by (blast intro: proper_itI)
      qed
    qed
  } thus "proper_it
      (iteratei_postfixed [] t :: (_,'\<sigma>a) set_iterator) 
      (iteratei_postfixed [] t :: (_,'\<sigma>b) set_iterator)" .
qed

lemma pi_trie[proper_it]: 
  "proper_it' Trie2.iteratei Trie2.iteratei"
  unfolding Trie2.iteratei_def[abs_def]
  apply (rule proper_it'I)
  apply (intro icf_proper_iteratorI)
  apply (rule proper_it'D)
  by (rule pi_trie_impl)

interpretation pi_trie: proper_it_loc Trie2.iteratei Trie2.iteratei
  apply unfold_locales
  apply (rule pi_trie)
  done

text \<open>Code generator test\<close>
definition "test_codegen \<equiv> (
  tm.add ,
  tm.add_dj ,
  tm.ball ,
  tm.bex ,
  tm.delete ,
  tm.empty ,
  tm.isEmpty ,
  tm.isSng ,
  tm.iterate ,
  tm.iteratei ,
  tm.list_it ,
  tm.lookup ,
  tm.restrict ,
  tm.sel ,
  tm.size ,
  tm.size_abort ,
  tm.sng ,
  tm.to_list ,
  tm.to_map ,
  tm.update ,
  tm.update_dj)"

export_code test_codegen checking SML

end

