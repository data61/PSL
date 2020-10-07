(*  Title:       Tree Automata
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section "Executable Implementation of Tree Automata"
theory Ta_impl
imports 
  Main
  Collections.CollectionsV1 
  Ta AbsAlgo
  "HOL-Library.Code_Target_Numeral" 
begin




text_raw \<open>\label{sec:taimpl}\<close>

text \<open>
  In this theory, an effcient executable implementation of non-deterministic 
  tree automata and basic algorithms is defined.

  The algorithms use red-black trees to represent sets of states or rules 
  where appropriate.
\<close>

subsection "Prelude"

  \<comment> \<open>Make rules hashable\<close>
instantiation ta_rule :: (hashable,hashable) hashable
begin
fun hashcode_of_ta_rule 
  :: "('Q1::hashable,'Q2::hashable) ta_rule \<Rightarrow> hashcode" 
  where
  "hashcode_of_ta_rule (q \<rightarrow> f qs) = hashcode q + hashcode f + hashcode qs"

definition [simp]: "hashcode = hashcode_of_ta_rule"

definition "def_hashmap_size::(('a,'b) ta_rule itself \<Rightarrow> nat) == (\<lambda>_. 32)"

instance 
  by (intro_classes)(auto simp add: def_hashmap_size_ta_rule_def)
end


  \<comment> \<open>Make wrapped states hashable\<close>
instantiation ustate_wrapper :: (hashable,hashable) hashable
begin
  definition "hashcode x == (case x of USW1 a \<Rightarrow> 2 * hashcode a | USW2 b \<Rightarrow> 2 * hashcode b + 1)"
  definition "def_hashmap_size = (\<lambda>_ :: (('a,'b) ustate_wrapper) itself. def_hashmap_size TYPE('a) + def_hashmap_size TYPE('b))"

  instance using def_hashmap_size[where ?'a="'a"] def_hashmap_size[where ?'a="'b"]
    by(intro_classes)(simp_all add: bounded_hashcode_bounds def_hashmap_size_ustate_wrapper_def split: ustate_wrapper.split)

end

subsubsection \<open>Ad-Hoc instantiations of generic Algorithms\<close>
setup Locale_Code.open_block
interpretation hll_idx: build_index_loc hm_ops ls_ops ls_ops by unfold_locales
interpretation ll_set_xy: g_set_xy_loc ls_ops ls_ops 
  by unfold_locales

interpretation lh_set_xx: g_set_xx_loc ls_ops hs_ops
  by unfold_locales
interpretation lll_iflt_cp: inj_image_filter_cp_loc ls_ops ls_ops ls_ops
  by unfold_locales
interpretation hhh_cart: cart_loc hs_ops hs_ops hs_ops by unfold_locales
interpretation hh_set_xy: g_set_xy_loc hs_ops hs_ops 
  by unfold_locales

interpretation llh_set_xyy: g_set_xyy_loc ls_ops ls_ops hs_ops
  by unfold_locales

interpretation hh_map_to_nat: map_to_nat_loc hs_ops hm_ops by unfold_locales
interpretation hh_set_xy: g_set_xy_loc hs_ops hs_ops by unfold_locales
interpretation lh_set_xy: g_set_xy_loc ls_ops hs_ops by unfold_locales
interpretation hh_set_xx: g_set_xx_loc hs_ops hs_ops by unfold_locales
interpretation hs_to_fifo: set_to_list_loc hs_ops fifo_ops by unfold_locales

setup Locale_Code.close_block

subsection "Generating Indices of Rules"
text \<open>
  Rule indices are pieces of extra information that may be attached to a 
  tree automaton.
  There are three possible rule indices
    \begin{description}
      \item[f]   index of rules by function symbol
      \item[s]   index of rules by lhs
      \item[sf]  index of rules
    \end{description}
\<close>

definition build_rule_index 
  :: "(('q,'l) ta_rule \<Rightarrow> 'i::hashable) \<Rightarrow> ('q,'l) ta_rule ls 
      \<Rightarrow> ('i,('q,'l) ta_rule ls) hm"
  where "build_rule_index == hll_idx.idx_build"

definition "build_rule_index_f \<delta> == build_rule_index (\<lambda>r. rhsl r) \<delta>"
definition "build_rule_index_s \<delta> == build_rule_index (\<lambda>r. lhs r) \<delta>"
definition "build_rule_index_sf \<delta> == build_rule_index (\<lambda>r. (lhs r, rhsl r)) \<delta>"

lemma build_rule_index_f_correct[simp]: 
  assumes I[simp, intro!]: "ls_invar \<delta>"
  shows "hll_idx.is_index rhsl (ls_\<alpha> \<delta>) (build_rule_index_f \<delta>)"
  apply (unfold build_rule_index_f_def build_rule_index_def)
  apply (simp add: hll_idx.idx_build_is_index)
  done

lemma build_rule_index_s_correct[simp]: 
  assumes I[simp, intro!]: "ls_invar \<delta>"
  shows
  "hll_idx.is_index lhs (ls_\<alpha> \<delta>) (build_rule_index_s \<delta>)"
  by (unfold build_rule_index_s_def build_rule_index_def)
     (simp add: hll_idx.idx_build_is_index)

lemma build_rule_index_sf_correct[simp]: 
  assumes I[simp, intro!]: "ls_invar \<delta>"
  shows
  "hll_idx.is_index (\<lambda>r. (lhs r, rhsl r)) (ls_\<alpha> \<delta>) (build_rule_index_sf \<delta>)"
  by (unfold build_rule_index_sf_def build_rule_index_def)
     (simp add: hll_idx.idx_build_is_index)

subsection "Tree Automaton with Optional Indices"

text \<open>
  A tree automaton contains a hashset of initial states, a list-set of rules and
  several (optional) rule indices.
\<close>

record (overloaded) ('q,'l) hashedTa =
    \<comment> \<open>Initial states\<close>
  hta_Qi :: "'q hs"           
    \<comment> \<open>Rules\<close>
  hta_\<delta> :: "('q,'l) ta_rule ls"    
    \<comment> \<open>Rules by function symbol\<close>
  hta_idx_f :: "('l,('q,'l) ta_rule ls) hm option" 
    \<comment> \<open>Rules by lhs state\<close>
  hta_idx_s :: "('q,('q,'l) ta_rule ls) hm option" 
    \<comment> \<open>Rules by lhs state and function symbol\<close>
  hta_idx_sf :: "('q\<times>'l,('q,'l) ta_rule ls) hm option" 

  \<comment> \<open>Abstraction of a concrete tree automaton to an abstract one\<close>
definition hta_\<alpha> 
  where "hta_\<alpha> H = \<lparr> ta_initial = hs_\<alpha> (hta_Qi H), ta_rules = ls_\<alpha> (hta_\<delta> H) \<rparr>"

  \<comment> \<open>Builds the f-index if not present\<close>
definition "hta_ensure_idx_f H ==
  case hta_idx_f H of 
    None \<Rightarrow> H\<lparr> hta_idx_f := Some (build_rule_index_f (hta_\<delta> H)) \<rparr> |
    Some _ \<Rightarrow> H
  "

  \<comment> \<open>Builds the s-index if not present\<close>
definition "hta_ensure_idx_s H ==
  case hta_idx_s H of 
    None \<Rightarrow> H\<lparr> hta_idx_s := Some (build_rule_index_s (hta_\<delta> H)) \<rparr> |
    Some _ \<Rightarrow> H
  "

  \<comment> \<open>Builds the sf-index if not present\<close>
definition "hta_ensure_idx_sf H ==
  case hta_idx_sf H of 
    None \<Rightarrow> H\<lparr> hta_idx_sf := Some (build_rule_index_sf (hta_\<delta> H)) \<rparr> |
    Some _ \<Rightarrow> H
  "

lemma hta_ensure_idx_f_correct_\<alpha>[simp]: 
  "hta_\<alpha> (hta_ensure_idx_f H) = hta_\<alpha> H" 
  by (simp add: hta_ensure_idx_f_def hta_\<alpha>_def split: option.split)
lemma hta_ensure_idx_s_correct_\<alpha>[simp]: 
  "hta_\<alpha> (hta_ensure_idx_s H) = hta_\<alpha> H" 
  by (simp add: hta_ensure_idx_s_def hta_\<alpha>_def split: option.split)
lemma hta_ensure_idx_sf_correct_\<alpha>[simp]: 
  "hta_\<alpha> (hta_ensure_idx_sf H) = hta_\<alpha> H" 
  by (simp add: hta_ensure_idx_sf_def hta_\<alpha>_def split: option.split)

lemma hta_ensure_idx_other[simp]:
  "hta_Qi (hta_ensure_idx_f H) = hta_Qi H"  
  "hta_\<delta> (hta_ensure_idx_f H) = hta_\<delta> H"
  
  "hta_Qi (hta_ensure_idx_s H) = hta_Qi H"  
  "hta_\<delta> (hta_ensure_idx_s H) = hta_\<delta> H"
  
  "hta_Qi (hta_ensure_idx_sf H) = hta_Qi H" 
  "hta_\<delta> (hta_ensure_idx_sf H) = hta_\<delta> H"
  by (auto 
    simp add: hta_ensure_idx_f_def hta_ensure_idx_s_def hta_ensure_idx_sf_def 
    split: option.split)

  \<comment> \<open>Check whether the f-index is present\<close>
definition "hta_has_idx_f H == hta_idx_f H \<noteq> None"
  \<comment> \<open>Check whether the s-index is present\<close>
definition "hta_has_idx_s H == hta_idx_s H \<noteq> None"
  \<comment> \<open>Check whether the sf-index is present\<close>
definition "hta_has_idx_sf H == hta_idx_sf H \<noteq> None"

lemma hta_idx_f_pres
  [simp, intro!]: "hta_has_idx_f (hta_ensure_idx_f H)" and
  [simp, intro]: "hta_has_idx_s H \<Longrightarrow> hta_has_idx_s (hta_ensure_idx_f H)" and
  [simp, intro]: "hta_has_idx_sf H \<Longrightarrow> hta_has_idx_sf (hta_ensure_idx_f H)"
  by (simp_all 
    add: hta_has_idx_f_def hta_has_idx_s_def hta_has_idx_sf_def 
         hta_ensure_idx_f_def 
    split: option.split)

lemma hta_idx_s_pres
  [simp, intro!]: "hta_has_idx_s (hta_ensure_idx_s H)" and
  [simp, intro]: "hta_has_idx_f H \<Longrightarrow> hta_has_idx_f (hta_ensure_idx_s H)" and
  [simp, intro]: "hta_has_idx_sf H \<Longrightarrow> hta_has_idx_sf (hta_ensure_idx_s H)"
  by (simp_all 
    add: hta_has_idx_f_def hta_has_idx_s_def hta_has_idx_sf_def 
         hta_ensure_idx_s_def 
    split: option.split)

lemma hta_idx_sf_pres
  [simp, intro!]: "hta_has_idx_sf (hta_ensure_idx_sf H)" and
  [simp, intro]: "hta_has_idx_f H \<Longrightarrow> hta_has_idx_f (hta_ensure_idx_sf H)" and
  [simp, intro]: "hta_has_idx_s H \<Longrightarrow> hta_has_idx_s (hta_ensure_idx_sf H)"
  by (simp_all 
    add: hta_has_idx_f_def hta_has_idx_s_def hta_has_idx_sf_def 
         hta_ensure_idx_sf_def 
    split: option.split)

text \<open>
  The lookup functions are only defined if the required index is present. 
  This enforces generation of the index before applying lookup functions.
\<close>
  \<comment> \<open>Lookup rules by function symbol\<close>
definition "hta_lookup_f f H == hll_idx.lookup f (the (hta_idx_f H))"
  \<comment> \<open>Lookup rules by lhs-state\<close>
definition "hta_lookup_s q H == hll_idx.lookup q (the (hta_idx_s H))"
  \<comment> \<open>Lookup rules by function symbol and lhs-state\<close>
definition "hta_lookup_sf q f H == hll_idx.lookup (q,f) (the (hta_idx_sf H))"


  \<comment> \<open>This locale defines the invariants of a tree automaton\<close>
locale hashedTa =
  fixes H :: "('Q::hashable,'L::hashable) hashedTa"

  \<comment> \<open>The involved sets satisfy their invariants\<close>
  assumes invar[simp, intro!]: 
    "hs_invar (hta_Qi H)"
    "ls_invar (hta_\<delta> H)"

  \<comment> \<open>The indices are correct, if present\<close>
  assumes index_correct:
    "hta_idx_f H = Some idx_f 
      \<Longrightarrow> hll_idx.is_index rhsl (ls_\<alpha> (hta_\<delta> H)) idx_f"
    "hta_idx_s H = Some idx_s 
      \<Longrightarrow> hll_idx.is_index lhs (ls_\<alpha> (hta_\<delta> H)) idx_s"
    "hta_idx_sf H = Some idx_sf 
      \<Longrightarrow> hll_idx.is_index (\<lambda>r. (lhs r, rhsl r)) (ls_\<alpha> (hta_\<delta> H)) idx_sf"

begin
  \<comment> \<open>Inside this locale, some shorthand notations for the sets of 
      rules and initial states are used\<close>
  abbreviation "\<delta> == hta_\<delta> H"
  abbreviation "Qi == hta_Qi H"

  \<comment> \<open>The lookup-xxx operations are correct\<close>
  lemma hta_lookup_f_correct: 
    "hta_has_idx_f H \<Longrightarrow> ls_\<alpha> (hta_lookup_f f H) = {r\<in>ls_\<alpha> \<delta> . rhsl r = f}"
    "hta_has_idx_f H \<Longrightarrow> ls_invar (hta_lookup_f f H)"
    apply (cases "hta_has_idx_f H")
    apply (unfold hta_has_idx_f_def hta_lookup_f_def)
    apply (auto 
      simp add: hll_idx.lookup_correct[OF index_correct(1)] 
                index_def)
    done

  lemma hta_lookup_s_correct: 
    "hta_has_idx_s H \<Longrightarrow> ls_\<alpha> (hta_lookup_s q H) = {r\<in>ls_\<alpha> \<delta> . lhs r = q}"
    "hta_has_idx_s H \<Longrightarrow> ls_invar (hta_lookup_s q H)"
    apply (cases "hta_has_idx_s H")
    apply (unfold hta_has_idx_s_def hta_lookup_s_def)
    apply (auto 
      simp add: hll_idx.lookup_correct[OF index_correct(2)] 
                index_def)
    done

  lemma hta_lookup_sf_correct: 
    "hta_has_idx_sf H 
      \<Longrightarrow> ls_\<alpha> (hta_lookup_sf q f H) = {r\<in>ls_\<alpha> \<delta> . lhs r = q \<and> rhsl r = f}"
    "hta_has_idx_sf H \<Longrightarrow> ls_invar (hta_lookup_sf q f H)"
    apply (cases "hta_has_idx_sf H")
    apply (unfold hta_has_idx_sf_def hta_lookup_sf_def)
    apply (auto 
      simp add: hll_idx.lookup_correct[OF index_correct(3)] 
                index_def)
    done

  \<comment> \<open>The ensure-index operations preserve the invariants\<close>
  lemma hta_ensure_idx_f_correct[simp, intro!]: "hashedTa (hta_ensure_idx_f H)"
    apply (unfold_locales)
    apply (auto)
    apply (auto 
      simp add: hta_ensure_idx_f_def hta_ensure_idx_s_def hta_ensure_idx_sf_def 
               index_correct 
      split: option.split_asm)
    done

  lemma hta_ensure_idx_s_correct[simp, intro!]: "hashedTa (hta_ensure_idx_s H)"
    apply (unfold_locales)
    apply (auto)
    apply (auto 
      simp add: hta_ensure_idx_f_def hta_ensure_idx_s_def hta_ensure_idx_sf_def 
                index_correct 
      split: option.split_asm)
    done

  lemma hta_ensure_idx_sf_correct[simp, intro!]: "hashedTa (hta_ensure_idx_sf H)"
    apply (unfold_locales)
    apply (auto)
    apply (auto 
      simp add: hta_ensure_idx_f_def hta_ensure_idx_s_def hta_ensure_idx_sf_def 
                index_correct 
      split: option.split_asm)
    done

  text \<open>The abstract tree automaton satisfies the invariants for an abstract
          tree automaton\<close>
  lemma hta_\<alpha>_is_ta[simp, intro!]: "tree_automaton (hta_\<alpha> H)"
    apply unfold_locales
    apply (unfold hta_\<alpha>_def)
    apply auto
    done

end

\<comment> \<open>Add some lemmas to simpset -- also outside the locale\<close>
lemmas [simp, intro] = 
  hashedTa.hta_ensure_idx_f_correct
  hashedTa.hta_ensure_idx_s_correct
  hashedTa.hta_ensure_idx_sf_correct

  \<comment> \<open>Build a tree automaton from a set of initial states and a set of rules\<close>
definition "init_hta Qi \<delta> == 
  \<lparr> hta_Qi= Qi, 
    hta_\<delta> = \<delta>, 
    hta_idx_f = None, 
    hta_idx_s = None, 
    hta_idx_sf = None 
  \<rparr>"

  \<comment> \<open>Building a tree automaton from a valid tree automaton yields again a 
      valid tree automaton. This operation has the only effect of removing 
      the indices.\<close>
lemma (in hashedTa) init_hta_is_hta: 
  "hashedTa (init_hta (hta_Qi H) (hta_\<delta> H))"
  apply (unfold_locales)
  apply (unfold init_hta_def)
  apply (auto)
  done

subsection "Algorithm for the Word Problem"

lemma r_match_by_laz: "r_match L l = list_all_zip (\<lambda>Q q. q\<in>Q) L l"
  by (unfold r_match_alt list_all_zip_alt)
      auto


text "Executable function that computes the set of accepting states for 
    a given tree"
fun faccs' where
  "faccs' H (NODE f ts) = (
    let Qs = List.map (faccs' H) ts in
      ll_set_xy.g_image_filter (\<lambda>r. case r of (q \<rightarrow> f' qs) \<Rightarrow> 
           if list_all_zip (\<lambda>Q q. ls_memb q Q) Qs qs then Some (lhs r) else None
                          ) 
                      (hta_lookup_f f H)
  )"

  \<comment> \<open>Executable algorithm to decide the word-problem. The first version 
      depends on the f-index to be present, the second version computes the 
      index if not present.\<close>
definition "hta_mem' t H == \<not>lh_set_xx.g_disjoint (faccs' H t) (hta_Qi H)"
definition "hta_mem t H == hta_mem' t (hta_ensure_idx_f H)"

context hashedTa
begin

  lemma faccs'_invar:
    assumes HI[simp, intro!]: "hta_has_idx_f H"
    shows "ls_invar (faccs' H t)" (is ?T1) 
          "list_all ls_invar (List.map (faccs' H) ts)" (is ?T2)
  proof -
    have "?T1 \<and> ?T2"
      apply (induct rule: compat_tree_tree_list.induct)
      apply (auto simp add: ll_set_xy.image_filter_correct hta_lookup_f_correct)
      done
    thus ?T1 ?T2 by auto
  qed

  declare faccs'_invar(1)[simp, intro]

  lemma faccs'_correct:
    assumes HI[simp, intro!]: "hta_has_idx_f H"
    shows 
      "ls_\<alpha> (faccs' H t) = faccs (ls_\<alpha> (hta_\<delta> H)) t" (is ?T1)
      "List.map ls_\<alpha> (List.map (faccs' H) ts) 
       = List.map (faccs (ls_\<alpha> (hta_\<delta> H))) ts" (is ?T2)
  proof -
    have "?T1 \<and> ?T2"
    proof (induct rule: compat_tree_tree_list.induct)
      case (NODE f ts)
      let ?\<delta> = "(ls_\<alpha> (hta_\<delta> H))"
      have "faccs ?\<delta> (NODE f ts) = (
        let Qs = List.map (faccs ?\<delta>) ts in
          {q. \<exists>r\<in>?\<delta>. r_matchc q f Qs r })"
        by (rule faccs.simps)
      also note NODE.hyps[symmetric]
      finally have 
        1: "faccs ?\<delta> (NODE f ts) 
            = ( let Qs = List.map ls_\<alpha> (List.map (faccs' H) ts) in
                 {q. \<exists>r\<in>?\<delta>. r_matchc q f Qs r })" .
      {
        fix Qsc:: "'Q ls list"
        assume QI: "list_all ls_invar Qsc"
        let ?Qs = "List.map ls_\<alpha> Qsc"
        have "{ q. \<exists>r\<in>?\<delta>. r_matchc q f ?Qs r } 
              = { q. \<exists>qs. (q \<rightarrow> f qs)\<in>?\<delta> \<and> r_match ?Qs qs }"
          apply (safe)
          apply (case_tac r)
          apply auto [1]
          apply force
          done
        also have "\<dots> = lhs ` { r\<in>{r\<in>?\<delta>. rhsl r = f}. 
                                 case r of (q \<rightarrow> f' qs) \<Rightarrow> r_match ?Qs qs}"
          apply auto
          apply force
          apply (case_tac xa)
          apply auto
          done
        finally have 
          1: "{ q. \<exists>r\<in>?\<delta>. r_matchc q f ?Qs r } 
              = lhs ` { r\<in>{r\<in>?\<delta>. rhsl r = f}. 
                         case r of (q \<rightarrow> f' qs) \<Rightarrow> r_match ?Qs qs}" 
          by auto
        from QI have 
          [simp]: "!!qs. list_all_zip (\<lambda>Q q. q\<in>ls_\<alpha> Q) Qsc qs 
                         \<longleftrightarrow> list_all_zip (\<lambda>Q q. ls_memb q Q) Qsc qs"
          apply (induct Qsc)
          apply (case_tac qs)
          apply auto [2]
          apply (case_tac qs)
          apply (auto simp add: ls.correct) [2]
          done
        have 2: "!!qs. r_match ?Qs qs = list_all_zip (\<lambda>a b. ls_memb b a) Qsc qs"
          apply (unfold r_match_by_laz)
          apply (simp add: list_all_zip_map1)
          done
        from 1 have 
          "{ q. \<exists>r\<in>?\<delta>. r_matchc q f ?Qs r } 
           = lhs ` { r\<in>{r\<in>?\<delta>. rhsl r = f}. 
                     case r of (q \<rightarrow> f' qs) \<Rightarrow> 
                       list_all_zip (\<lambda>a b. ls_memb b a) Qsc qs}" 
          by (simp only: 2)
        also have 
          "\<dots> = lhs ` { r\<in>ls_\<alpha> (hta_lookup_f f H). 
                         case r of (q \<rightarrow> f' qs) \<Rightarrow> 
                           list_all_zip (\<lambda>a b. ls_memb b a) Qsc qs}" 
          by (simp add: hta_lookup_f_correct)
        also have 
          "\<dots> = ls_\<alpha> ( ll_set_xy.g_image_filter 
                         ( \<lambda>r. case r of (q \<rightarrow> f' qs) \<Rightarrow> 
                             (if (list_all_zip (\<lambda>Q q. ls_memb q Q) Qsc qs) then Some (lhs r) else None))
                         (hta_lookup_f f H)
                     )"
          apply (simp add: ll_set_xy.image_filter_correct hta_lookup_f_correct)
          apply (auto split: ta_rule.split)
          apply (rule_tac x=xa in exI)
          apply auto
          apply (case_tac a)
          apply (simp add: image_iff)
          apply (rule_tac x=a in exI)
          apply auto
          done
        finally have 
          "{ q. \<exists>r\<in>?\<delta>. r_matchc q f ?Qs r } 
           = ls_\<alpha> ( ll_set_xy.g_image_filter 
                      (\<lambda>r. case r of (q \<rightarrow> f' qs) \<Rightarrow> 
                        (if (list_all_zip (\<lambda>Q q. ls_memb q Q) Qsc qs) then Some (lhs r) else None))
                      (hta_lookup_f f H))" .
      } note 2=this
      
      from 
        1 
        2[ where Qsc2 = "(List.map (faccs' H) ts)", 
           simplified faccs'_invar[OF HI]] 
      show ?case by simp
    qed simp_all
    thus ?T1 ?T2 by auto
  qed

    \<comment> \<open>Correctness of the algorithms for the word problem\<close>
  lemma hta_mem'_correct: 
    "hta_has_idx_f H \<Longrightarrow> hta_mem' t H \<longleftrightarrow> t\<in>ta_lang (hta_\<alpha> H)"
    apply (unfold ta_lang_def hta_\<alpha>_def hta_mem'_def)
    apply (auto simp add: lh_set_xx.disjoint_correct faccs'_correct faccs_alt)
    done

  theorem hta_mem_correct: "hta_mem t H \<longleftrightarrow> t\<in>ta_lang (hta_\<alpha> H)"
    using hashedTa.hta_mem'_correct[OF hta_ensure_idx_f_correct, simplified]
    apply (unfold hta_mem_def)
    apply simp
    done

end


subsection "Product Automaton and Intersection"

subsubsection "Brute Force Product Automaton"
text \<open>
  In this section, an algorithm that computes the product 
  automaton without reduction is implemented. While the runtime is always
  quadratic, this algorithm is very simple and the constant factors are 
  smaller than that of the version with integrated reduction.
  Moreover, lazy languages like Haskell seem to profit from this algorithm.
\<close>

definition \<delta>_prod_h 
  :: "('q1::hashable,'l::hashable) ta_rule ls 
      \<Rightarrow> ('q2::hashable,'l) ta_rule ls \<Rightarrow> ('q1\<times>'q2,'l) ta_rule ls" 
  where "\<delta>_prod_h \<delta>1 \<delta>2 == 
    lll_iflt_cp.inj_image_filter_cp (\<lambda>(r1,r2). r_prod r1 r2) 
                (\<lambda>(r1,r2). rhsl r1 = rhsl r2 
                         \<and> length (rhsq r1) = length (rhsq r2)) 
                \<delta>1 \<delta>2"

lemma r_prod_inj: 
  "\<lbrakk> rhsl r1 = rhsl r2; length (rhsq r1) = length (rhsq r2); 
     rhsl r1' = rhsl r2'; length (rhsq r1') = length (rhsq r2'); 
     r_prod r1 r2 = r_prod r1' r2' \<rbrakk> \<Longrightarrow> r1=r1' \<and> r2=r2'"
  apply (cases r1, cases r2, cases r1', cases r2')
  apply (auto dest: zip_inj)
  done

lemma \<delta>_prod_h_correct:
  assumes INV[simp]: "ls_invar \<delta>1" "ls_invar \<delta>2"
  shows 
    "ls_\<alpha> (\<delta>_prod_h \<delta>1 \<delta>2) = \<delta>_prod (ls_\<alpha> \<delta>1) (ls_\<alpha> \<delta>2)"
    "ls_invar (\<delta>_prod_h \<delta>1 \<delta>2)"
  apply (unfold \<delta>_prod_def \<delta>_prod_h_def)
  apply (subst lll_iflt_cp.inj_image_filter_cp_correct)
  apply simp_all [2]
  using r_prod_inj
  apply (auto intro!: inj_onI) []
  apply auto []
  apply (case_tac xa, case_tac y, simp, blast)
  apply force
  apply simp
  done

definition "hta_prodWR H1 H2 == 
  init_hta (hhh_cart.cart (hta_Qi H1) (hta_Qi H2)) (\<delta>_prod_h (hta_\<delta> H1) (hta_\<delta> H2))"

lemma hta_prodWR_correct_aux: 
  assumes A: "hashedTa H1" "hashedTa H2"
  shows 
    "hta_\<alpha> (hta_prodWR H1 H2) = ta_prod (hta_\<alpha> H1) (hta_\<alpha> H2)" (is ?T1)
    "hashedTa (hta_prodWR H1 H2)" (is ?T2)
proof -
  interpret a1: hashedTa H1 + a2: hashedTa H2 using A .
  show ?T1 ?T2
    apply (unfold hta_prodWR_def init_hta_def hta_\<alpha>_def ta_prod_def)
    apply (simp add: hhh_cart.cart_correct \<delta>_prod_h_correct)
    apply (unfold_locales)
    apply (simp_all add: hhh_cart.cart_correct \<delta>_prod_h_correct)
    done
qed
  
lemma hta_prodWR_correct:
  assumes TA: "hashedTa H1" "hashedTa H2"
  shows 
    "ta_lang (hta_\<alpha> (hta_prodWR H1 H2)) 
     = ta_lang (hta_\<alpha> H1) \<inter> ta_lang (hta_\<alpha> H2)"
    "hashedTa (hta_prodWR H1 H2)"
  by (simp_all add: hta_prodWR_correct_aux[OF TA] ta_prod_correct_aux1)

subsubsection "Product Automaton with Forward-Reduction"
text \<open>
  A more elaborated algorithm combines forward-reduction and the product 
  construction, i.e. product rules are only created ,,by need''.
\<close>

  \<comment> \<open>State of the product-automaton DFS-algorithm\<close>
type_synonym ('q1,'q2,'l) pa_state 
  = "('q1\<times>'q2) hs \<times> ('q1\<times>'q2) list \<times> ('q1\<times>'q2,'l) ta_rule ls"

  \<comment> \<open>Abstraction mapping to algorithm specified in 
  Section~\ref{sec:absalgo}.\<close>
definition pa_\<alpha> 
  :: "('q1::hashable,'q2::hashable,'l::hashable) pa_state 
      \<Rightarrow> ('q1,'q2,'l) frp_state"
  where "pa_\<alpha> S == let (Q,W,\<delta>d)=S in (hs_\<alpha> Q,W,ls_\<alpha> \<delta>d)"

definition pa_cond 
  :: "('q1::hashable,'q2::hashable,'l::hashable) pa_state \<Rightarrow> bool" 
  where "pa_cond S == let (Q,W,\<delta>d) = S in W\<noteq>[]"

  \<comment> \<open>Adds all successor states to the set of discovered states and to the 
  worklist\<close>
fun pa_upd_rule 
  :: "('q1\<times>'q2) hs \<Rightarrow> ('q1\<times>'q2) list 
      \<Rightarrow> (('q1::hashable)\<times>('q2::hashable)) list 
      \<Rightarrow> (('q1\<times>'q2) hs \<times> ('q1\<times>'q2) list)" 
  where
  "pa_upd_rule Q W [] = (Q,W)" |
  "pa_upd_rule Q W (qp#qs) = (
    if \<not> hs_memb qp Q then
      pa_upd_rule (hs_ins qp Q) (qp#W) qs
    else pa_upd_rule Q W qs
  )"


definition pa_step 
  :: "('q1::hashable,'l::hashable) hashedTa 
      \<Rightarrow> ('q2::hashable,'l) hashedTa 
      \<Rightarrow> ('q1,'q2,'l) pa_state \<Rightarrow> ('q1,'q2,'l) pa_state"
  where "pa_step H1 H2 S == let 
    (Q,W,\<delta>d)=S;
    (q1,q2)=hd W
  in  
    ls_iteratei (hta_lookup_s q1 H1) (\<lambda>_. True) (\<lambda>r1 res. 
      ls_iteratei (hta_lookup_sf q2 (rhsl r1) H2) (\<lambda>_. True) (\<lambda>r2 res.
        if (length (rhsq r1) = length (rhsq r2)) then
          let 
            rp=r_prod r1 r2;
            (Q,W,\<delta>d) = res;
            (Q',W') = pa_upd_rule Q W (rhsq rp)
          in
            (Q',W',ls_ins_dj rp \<delta>d)
        else
          res
      ) res
    ) (Q,tl W,\<delta>d)
  "

definition pa_initial 
  :: "('q1::hashable,'l::hashable) hashedTa 
      \<Rightarrow> ('q2::hashable,'l) hashedTa 
      \<Rightarrow> ('q1,'q2,'l) pa_state"
where "pa_initial H1 H2 == 
  let Qip = hhh_cart.cart (hta_Qi H1) (hta_Qi H2) in (
    Qip,
    hs_to_list Qip,
    ls_empty ()
  )"

definition pa_invar_add:: 
  "('q1::hashable,'q2::hashable,'l::hashable) pa_state set" 
  where "pa_invar_add == { (Q,W,\<delta>d). hs_invar Q \<and> ls_invar \<delta>d }"

definition "pa_invar H1 H2 == 
  pa_invar_add \<inter> {s. (pa_\<alpha> s) \<in> frp_invar (hta_\<alpha> H1) (hta_\<alpha> H2)}"

definition "pa_det_algo H1 H2 
  == \<lparr> dwa_cond=pa_cond, 
       dwa_step = pa_step H1 H2, 
       dwa_initial = pa_initial H1 H2, 
       dwa_invar = pa_invar H1 H2 \<rparr>"

lemma pa_upd_rule_correct:
  assumes INV[simp, intro!]: "hs_invar Q"
  assumes FMT: "pa_upd_rule Q W qs = (Q',W')"
  shows
    "hs_invar Q'" (is ?T1)
    "hs_\<alpha> Q' = hs_\<alpha> Q \<union> set qs" (is ?T2)
    "\<exists>Wn. distinct Wn \<and> set Wn = set qs - hs_\<alpha> Q \<and> W'=Wn@W" (is ?T3)
proof -
  from INV FMT have "?T1 \<and> ?T2 \<and> ?T3"
  proof (induct qs arbitrary: Q W Q' W')
    case Nil thus ?case by simp
  next
    case (Cons q qs Q W Q' W')
    show ?case 
    proof (cases "q\<in>hs_\<alpha> Q")
      case True 
      obtain Qh Wh where RF: "pa_upd_rule Q W qs = (Qh,Wh)" by force
      with True Cons.prems have [simp]: "Q'=Qh" "W'=Wh"
        by (auto simp add: hs.correct)
      from Cons.hyps[OF Cons.prems(1) RF] have
        "hs_invar Qh" 
        "hs_\<alpha> Qh = hs_\<alpha> Q \<union> set qs" 
        "(\<exists>Wn. distinct Wn \<and> set Wn = set qs - hs_\<alpha> Q \<and> Wh = Wn @ W)"
        by auto
      thus ?thesis using True by auto
    next
      case False
      with Cons.prems have RF: "pa_upd_rule (hs_ins q Q) (q#W) qs = (Q',W')"
        by (auto simp add: hs.correct)

      from Cons.hyps[OF _ RF] Cons.prems(1) have
        "hs_invar Q'" 
        "hs_\<alpha> Q' = insert q (hs_\<alpha> Q) \<union> set (qs)"
        "\<exists>Wn. distinct Wn 
              \<and> set Wn = set qs - insert q (hs_\<alpha> Q) 
              \<and> W' = Wn @ q # W"
        by (auto simp add: hs.correct)
      thus ?thesis using False by auto
    qed
  qed
  thus ?T1 ?T2 ?T3 by auto
qed


lemma pa_step_correct:
  assumes TA: "hashedTa H1" "hashedTa H2"
  assumes idx[simp]: "hta_has_idx_s H1" "hta_has_idx_sf H2"
  assumes INV: "(Q,W,\<delta>d)\<in>pa_invar H1 H2"
  assumes COND: "pa_cond (Q,W,\<delta>d)"
  shows 
    "(pa_step H1 H2 (Q,W,\<delta>d))\<in>pa_invar_add" (is ?T1)
    "(pa_\<alpha> (Q,W,\<delta>d), pa_\<alpha> (pa_step H1 H2 (Q,W,\<delta>d))) 
     \<in> frp_step (ls_\<alpha> (hta_\<delta> H1)) (ls_\<alpha> (hta_\<delta> H2))" (is ?T2)
proof -
  interpret h1: hashedTa H1 by fact
  interpret h2: hashedTa H2 by fact

  from COND obtain q1 q2 Wtl where 
    [simp]: "W=(q1,q2)#Wtl" 
    by (cases W) (auto simp add: pa_cond_def)

  from INV have [simp]: "hs_invar Q" "ls_invar \<delta>d" 
    by (auto simp add: pa_invar_add_def pa_invar_def)

  define inv where "inv = (\<lambda>\<delta>p (Q', W', \<delta>d'). 
    hs_invar Q' 
    \<and> ls_invar \<delta>d' 
    \<and> (\<exists>Wn. distinct Wn 
            \<and> set Wn = (f_succ \<delta>p `` {(q1,q2)}) - hs_\<alpha> Q 
            \<and> W'=Wn@Wtl 
            \<and> hs_\<alpha> Q'=hs_\<alpha> Q \<union> (f_succ \<delta>p `` {(q1,q2)}))
    \<and> (ls_\<alpha> \<delta>d' = ls_\<alpha> \<delta>d \<union> {r\<in>\<delta>p. lhs r = (q1,q2) }))"

  have G: "inv (\<delta>_prod (ls_\<alpha> (hta_\<delta> H1)) (ls_\<alpha> (hta_\<delta> H2))) 
               (pa_step H1 H2 (Q,W,\<delta>d))"
    apply (unfold pa_step_def)
    apply simp
    apply (rule_tac 
      I="\<lambda>it1 res. inv (\<delta>_prod (ls_\<alpha> (hta_\<delta> H1) - it1) (ls_\<alpha> (hta_\<delta> H2))) res"
      in ls.iterate_rule_P)
    \<comment> \<open>Invar\<close>
    apply (simp add: h1.hta_lookup_s_correct)
    \<comment> \<open>Initial\<close>
    apply (fastforce simp add: inv_def \<delta>_prod_def h1.hta_lookup_s_correct 
                              f_succ_alt)
    \<comment> \<open>Step\<close>
    apply (rule_tac 
      I="\<lambda>it2 res. inv ( \<delta>_prod (ls_\<alpha> (hta_\<delta> H1) - it) (ls_\<alpha> (hta_\<delta> H2)) 
                         \<union> \<delta>_prod {x} (ls_\<alpha> (hta_\<delta> H2) - it2)) 
                        res" 
      in ls.iterate_rule_P)
      \<comment> \<open>Invar\<close>
      apply (simp add: h2.hta_lookup_sf_correct)
      \<comment> \<open>Init\<close>
      apply (case_tac \<sigma>)
      apply (simp add: inv_def h1.hta_lookup_s_correct h2.hta_lookup_sf_correct)
      apply (force simp add: f_succ_alt elim: \<delta>_prodE intro: \<delta>_prodI) [1]
      \<comment> \<open>Step\<close>
      defer \<comment> \<open>Requires considerably more work: Deferred to Isar proof below\<close>
      \<comment> \<open>Final\<close>
      apply (simp add: h1.hta_lookup_s_correct h2.hta_lookup_sf_correct)
      apply (auto) [1]
      apply (subgoal_tac 
        "ls_\<alpha> (hta_\<delta> H1) - (it - {x}) = (ls_\<alpha> (hta_\<delta> H1) - it) \<union> {x}")
      apply (simp add: \<delta>_prod_insert)
      apply (subst Un_commute)
      apply simp
      apply blast
    \<comment> \<open>Final\<close>
    apply force
  proof goal_cases
    case prems: (1 r1 it1 resxh r2 it2 resh)
    \<comment> \<open>Resolve lookup-operations\<close>
    hence G': 
      "it1 \<subseteq> {r \<in> ls_\<alpha> (hta_\<delta> H1). lhs r = q1}" 
      "it2 \<subseteq> {r \<in> ls_\<alpha> (hta_\<delta> H2). lhs r = q2 \<and> rhsl r = rhsl r1}"
      by (simp_all add: h1.hta_lookup_s_correct h2.hta_lookup_sf_correct)

    \<comment> \<open>Basic reasoning setup\<close>
    from prems(1,4) G' have 
      [simp]: "ls_\<alpha> (hta_\<delta> H2) - (it2 - {r2}) = (ls_\<alpha> (hta_\<delta> H2) - it2) \<union> {r2}"
      by auto
    obtain Qh Wh \<delta>dh Q' W' \<delta>d' where [simp]: "resh=(Qh,Wh,\<delta>dh)" 
      by (cases resh) fastforce
    from prems(6) have INVAH[simp]: "hs_invar Qh" "ls_invar \<delta>dh" 
      by (auto simp add: inv_def)

    \<comment> \<open>The involved rules have the same label, and their lhs is determined\<close>
    from prems(1,4) G' obtain l qs1 qs2 where 
      RULE_FMT: "r1 = (q1 \<rightarrow> l qs1)" "r2=(q2 \<rightarrow> l qs2)"
      apply (cases r1, cases r2)
      apply force
      done

    {
      \<comment> \<open>If the rhs have different lengths, the algorithm ignores the rule:\<close>
      assume LEN: "length (rhsq r1) \<noteq> length (rhsq r2)"
      
      hence [simp]: "\<delta>_prod_sng2 {r1} r2 = {}"
        by (auto simp add: \<delta>_prod_sng2_def split: ta_rule.split)

      have ?case using prems 
        by (simp add: LEN \<delta>_prod_insert)
    } moreover {
      \<comment> \<open>If the rhs have the same length, the rule is inserted\<close>
      assume LEN: "length (rhsq r1) = length (rhsq r2)"
      hence [simp]: "length qs1 = length qs2" by (simp add: RULE_FMT)

      hence [simp]: "\<delta>_prod_sng2 {r1} r2 = {(q1,q2) \<rightarrow> l (zip qs1 qs2)}"
        using prems(1,4) G'
        by (auto simp add: \<delta>_prod_sng2_def RULE_FMT)

      \<comment> \<open>Obtain invariant of previous state\<close>
      from prems(6)[unfolded inv_def, simplified] obtain Wn where INVH:
        "distinct Wn"
        "set Wn = f_succ (\<delta>_prod (ls_\<alpha> (hta_\<delta> H1) - it1) (ls_\<alpha> (hta_\<delta> H2)) 
                          \<union> \<delta>_prod {r1} (ls_\<alpha> (hta_\<delta> H2) - it2)) 
                  `` {(q1, q2)} - hs_\<alpha> Q"
        "Wh = Wn @ Wtl" 
        "hs_\<alpha> Qh = hs_\<alpha> Q 
                   \<union> f_succ (\<delta>_prod (ls_\<alpha> (hta_\<delta> H1) - it1) (ls_\<alpha> (hta_\<delta> H2))
                              \<union> \<delta>_prod {r1} (ls_\<alpha> (hta_\<delta> H2) - it2)) 
                      `` {(q1, q2)}" 
        "ls_\<alpha> \<delta>dh = ls_\<alpha> \<delta>d 
          \<union> {r. ( r \<in> \<delta>_prod (ls_\<alpha> (hta_\<delta> H1) - it1) (ls_\<alpha> (hta_\<delta> H2)) 
                  \<or> r \<in> \<delta>_prod {r1} (ls_\<alpha> (hta_\<delta> H2) - it2)
                 ) \<and> lhs r = (q1, q2)
             }"
        by blast

      \<comment> \<open>Required to justify disjoint insert\<close>
      have RPD: "r_prod r1 r2 \<notin> ls_\<alpha> \<delta>dh" 
      proof -
        from INV[unfolded pa_invar_def frp_invar_def frp_invar_add_def]
        have LSDD: 
          "ls_\<alpha> \<delta>d = {r \<in> \<delta>_prod (ls_\<alpha> (hta_\<delta> H1)) (ls_\<alpha> (hta_\<delta> H2)). 
                        lhs r \<in> hs_\<alpha> Q - set W}"
          by (auto simp add: pa_\<alpha>_def hta_\<alpha>_def)
        have "r_prod r1 r2 \<notin> ls_\<alpha> \<delta>d"
        proof
          assume "r_prod r1 r2 \<in> ls_\<alpha> \<delta>d"
          with LSDD have "lhs (r_prod r1 r2) \<notin> set W" by auto
          moreover from prems(1,4) G' have "lhs (r_prod r1 r2) = (q1,q2)" 
            by (cases r1, cases r2) auto
          ultimately show False by simp
        qed
        moreover from prems(6) have "ls_\<alpha> \<delta>dh = 
          ls_\<alpha> \<delta>d \<union> 
          {r. ( r \<in> \<delta>_prod (ls_\<alpha> (hta_\<delta> H1) - it1) (ls_\<alpha> (hta_\<delta> H2)) 
                \<or> r \<in> \<delta>_prod {r1} (ls_\<alpha> (hta_\<delta> H2) - it2)
              ) \<and> lhs r = (q1, q2)}" (is "_= _ \<union> ?s")
          by (simp add: inv_def)
        moreover have "r_prod r1 r2 \<notin> ?s" using prems(1,4) G'(2) LEN
          apply (cases r1, cases r2)
          apply (auto simp add: \<delta>_prod_def)
          done
        ultimately show ?thesis by blast
      qed

      \<comment> \<open>Correctness of result of @{text pa_upd_rule}\<close>
      obtain Q' W' where 
        PAUF: "(pa_upd_rule Qh Wh (rhsq (r_prod r1 r2))) = (Q',W')" 
        by force
      from pa_upd_rule_correct[OF INVAH(1) PAUF] obtain Wnn where UC:
        "hs_invar Q'"
        "hs_\<alpha> Q' = hs_\<alpha> Qh \<union> set (rhsq (r_prod r1 r2))"
        "distinct Wnn" 
        "set Wnn = set (rhsq (r_prod r1 r2)) - hs_\<alpha> Qh" 
        "W' = Wnn @ Wh"
        by blast

      \<comment> \<open>Put it all together\<close>
      have ?case
        apply (simp add: LEN Let_def ls.ins_dj_correct[OF INVAH(2) RPD] 
                         PAUF inv_def UC(1))
        apply (intro conjI)
        apply (rule_tac x="Wnn@Wn" in exI)
        apply (auto simp add: f_succ_alt \<delta>_prod_insert RULE_FMT UC INVH 
                              \<delta>_prod_sng2_def \<delta>_prod_sng1_def)
        done
    } ultimately show ?case by blast
  qed
  from G show ?T1
    by (cases "pa_step H1 H2 (Q,W,\<delta>d)")
       (simp add: pa_invar_add_def inv_def)
  from G show ?T2
    by (cases "pa_step H1 H2 (Q,W,\<delta>d)")
       (auto simp add: inv_def pa_\<alpha>_def Let_def intro: frp_step.intros)

qed
    
  

  \<comment> \<open>The product-automaton algorithm is a precise implementation of its
      specification\<close>
lemma pa_pref_frp: 
  assumes TA: "hashedTa H1" "hashedTa H2"
  assumes idx[simp]: "hta_has_idx_s H1" "hta_has_idx_sf H2"

  shows "wa_precise_refine (det_wa_wa (pa_det_algo H1 H2)) 
                           (frp_algo (hta_\<alpha> H1) (hta_\<alpha> H2)) 
                           pa_\<alpha>"
proof -
  interpret h1: hashedTa H1 by fact
  interpret h2: hashedTa H2 by fact
  
  show ?thesis
    apply (unfold_locales)
    apply (auto simp add: det_wa_wa_def pa_det_algo_def pa_\<alpha>_def 
                          pa_cond_def frp_algo_def frp_cond_def) [1]
    apply (auto simp add: det_wa_wa_def pa_det_algo_def pa_cond_def
                          hta_\<alpha>_def frp_algo_def frp_cond_def 
                intro!: pa_step_correct(2)[OF TA]) [1]
    apply (auto simp add: det_wa_wa_def pa_det_algo_def pa_\<alpha>_def 
                          hta_\<alpha>_def pa_cond_def frp_algo_def frp_cond_def
                          pa_invar_def pa_step_def pa_initial_def 
                          hs.correct ls.correct Let_def hhh_cart.cart_correct 
                intro: frp_initial.intros
    ) [3]
    done
qed


  \<comment> \<open>The product automaton algorithm is a correct while-algorithm\<close>
lemma pa_while_algo: 
  assumes TA: "hashedTa H1" "hashedTa H2"
  assumes idx[simp]: "hta_has_idx_s H1" "hta_has_idx_sf H2"

  shows "while_algo (det_wa_wa (pa_det_algo H1 H2))"
proof -
  interpret h1: hashedTa H1 by fact
  interpret h2: hashedTa H2 by fact

  interpret ref: wa_precise_refine "(det_wa_wa (pa_det_algo H1 H2))" 
                                   "(frp_algo (hta_\<alpha> H1) (hta_\<alpha> H2))" 
                                   "pa_\<alpha>" 
    using pa_pref_frp[OF TA idx] .
  show ?thesis
    apply (rule ref.wa_intro)
    apply (simp add: frp_while_algo)
    apply (simp add: det_wa_wa_def pa_det_algo_def pa_invar_def frp_algo_def)

    apply (auto simp add: det_wa_wa_def pa_det_algo_def) [1]
    apply (rule pa_step_correct(1)[OF TA idx])
    apply (auto simp add: pa_invar_def frp_algo_def) [2]
    
    apply (simp add: det_wa_wa_def pa_det_algo_def pa_initial_def 
                     pa_invar_add_def Let_def hhh_cart.cart_correct ls.correct)
    done
qed
    
\<comment> \<open>By definition, the product automaton algorithm is deterministic\<close>
lemmas pa_det_while_algo = det_while_algo_intro[OF pa_while_algo]

\<comment> \<open>Transferred correctness lemma\<close>
lemmas pa_inv_final = 
  wa_precise_refine.transfer_correctness[OF pa_pref_frp frp_inv_final]


\<comment> \<open>The next two definitions specify the product-automata algorithm. The first
    version requires the s-index of the first and the sf-index of the second
    automaton to be present, while the second version computes the required 
    indices, if necessary\<close>
definition "hta_prod' H1 H2 ==
  let (Q,W,\<delta>d) = while pa_cond (pa_step H1 H2) (pa_initial H1 H2) in
    init_hta (hhh_cart.cart (hta_Qi H1) (hta_Qi H2)) \<delta>d
  "

definition "hta_prod H1 H2 == 
  hta_prod' (hta_ensure_idx_s H1) (hta_ensure_idx_sf H2)"


lemma hta_prod'_correct_aux:
  assumes TA: "hashedTa H1" "hashedTa H2"
  assumes idx: "hta_has_idx_s H1" "hta_has_idx_sf H2"
  shows "hta_\<alpha> (hta_prod' H1 H2) 
         = ta_fwd_reduce (ta_prod (hta_\<alpha> H1) (hta_\<alpha> H2))" (is ?T1)
        "hashedTa (hta_prod' H1 H2)" (is ?T2)
proof -
  interpret h1: hashedTa H1 by fact
  interpret h2: hashedTa H2 by fact

  interpret dwa: det_while_algo "pa_det_algo H1 H2" 
    using pa_det_while_algo[OF TA idx] .

  have LC: "while pa_cond (pa_step H1 H2) (pa_initial H1 H2) = dwa.loop"
    by (unfold dwa.loop_def)
       (simp add: pa_det_algo_def)

  from dwa.while_proof'[OF pa_inv_final[OF TA idx]]
  show ?T1
    apply (unfold dwa.loop_def)
    apply (simp add: hta_prod'_def init_hta_def hta_\<alpha>_def pa_det_algo_def)
    apply (cases "(while pa_cond (pa_step H1 H2) (pa_initial H1 H2))")
    apply (simp add: pa_\<alpha>_def hhh_cart.cart_correct hta_\<alpha>_def)
    done

  show ?T2
    apply (simp add: hta_prod'_def LC)
    apply (rule dwa.while_proof)
    apply (case_tac s)
    apply (simp add: pa_det_algo_def pa_invar_add_def pa_invar_def init_hta_def)
    apply unfold_locales
    apply (simp_all add: hhh_cart.cart_correct)
    done
qed

theorem hta_prod'_correct:
  assumes TA: "hashedTa H1" "hashedTa H2"
  assumes HI: "hta_has_idx_s H1" "hta_has_idx_sf H2"
  shows 
    "ta_lang (hta_\<alpha> (hta_prod' H1 H2)) 
     = ta_lang (hta_\<alpha> H1) \<inter> ta_lang (hta_\<alpha> H2)"

    "hashedTa (hta_prod' H1 H2)"
  by (simp_all add: hta_prod'_correct_aux[OF TA HI] ta_prod_correct_aux1)

lemma hta_prod_correct_aux:
  assumes TA[simp]: "hashedTa H1" "hashedTa H2"
  shows 
    "hta_\<alpha> (hta_prod H1 H2) = ta_fwd_reduce (ta_prod (hta_\<alpha> H1) (hta_\<alpha> H2))"
    "hashedTa (hta_prod H1 H2)"
  by (unfold hta_prod_def)
     (simp_all add: hta_prod'_correct_aux)
  
theorem hta_prod_correct:
  assumes TA: "hashedTa H1" "hashedTa H2"
  shows 
    "ta_lang (hta_\<alpha> (hta_prod H1 H2)) 
     = ta_lang (hta_\<alpha> H1) \<inter> ta_lang (hta_\<alpha> H2)"
    "hashedTa (hta_prod H1 H2)"
  by (simp_all add: hta_prod_correct_aux[OF TA] ta_prod_correct_aux1)


subsection "Remap States"

\<comment> \<open>Mapping the states of an automaton\<close>
definition hta_remap 
  :: "('q::hashable \<Rightarrow> 'qn::hashable) \<Rightarrow> ('q,'l::hashable) hashedTa 
      \<Rightarrow> ('qn,'l) hashedTa" 
  where "hta_remap f H == 
    init_hta (hh_set_xy.g_image f (hta_Qi H)) 
      (ll_set_xy.g_image (remap_rule f) (hta_\<delta> H))"
  
lemma (in hashedTa) hta_remap_correct:
  shows "hta_\<alpha> (hta_remap f H) = ta_remap f (hta_\<alpha> H)"
        "hashedTa (hta_remap f H)"
  apply (auto 
    simp add: hta_remap_def init_hta_def hta_\<alpha>_def 
              hh_set_xy.image_correct ll_set_xy.image_correct ta_remap_def)
  apply (unfold_locales)
  apply (auto simp add: hh_set_xy.image_correct ll_set_xy.image_correct)
  done


subsubsection "Reindex Automaton"
text \<open>
  In this section, an algorithm for re-indexing the states of the automaton to
  an initial segment of the naturals is implemented. The language of the 
  automaton is not changed by the reindexing operation.
\<close>

  \<comment> \<open>Set of states of a rule\<close>
fun rule_states_l where
  "rule_states_l (q \<rightarrow> f qs) = ls_ins q (ls.from_list qs)"

lemma rule_states_l_correct[simp]: 
  "ls_\<alpha> (rule_states_l r) = rule_states r"
  "ls_invar (rule_states_l r)"
  by (cases r, simp add: ls.correct)+

definition "hta_\<delta>_states H 
  == (llh_set_xyy.g_Union_image id (ll_set_xy.g_image_filter 
       (\<lambda>r. Some (rule_states_l r)) (hta_\<delta> H)))"

definition "hta_states H ==
  hs_union (hta_Qi H) (hta_\<delta>_states H)"

lemma (in hashedTa) hta_\<delta>_states_correct:
  "hs_\<alpha> (hta_\<delta>_states H) = \<delta>_states (ta_rules (hta_\<alpha> H))"
  "hs_invar (hta_\<delta>_states H)"
proof (simp_all add: hta_\<alpha>_def hta_\<delta>_states_def, goal_cases)
  case 1
  have 
    [simp]: "ls_\<alpha> (ll_set_xy.g_image_filter (\<lambda>x. Some (rule_states_l x)) \<delta>) 
             = rule_states_l ` ls_\<alpha> \<delta>"
    by (auto simp add: ll_set_xy.image_filter_correct)
  show ?case
    apply (simp add: \<delta>_states_def)
    apply (subst
      llh_set_xyy.Union_image_correct[
        of "(ll_set_xy.g_image_filter (\<lambda>x. Some (rule_states_l x)) \<delta>)", 
        simplified])
    apply (auto simp add: ll_set_xy.image_filter_correct)
    done
(*next
  case goal2 thus ?case
    apply (rule llh.Union_image_correct)
    apply (auto simp add: ls.image_filter_correct)
    done*)
qed

lemma (in hashedTa) hta_states_correct:
  "hs_\<alpha> (hta_states H) = ta_rstates (hta_\<alpha> H)"
  "hs_invar (hta_states H)"
  by (simp_all 
    add: hta_states_def ta_rstates_def hs.correct hta_\<delta>_states_correct 
         hta_\<alpha>_def)

definition "reindex_map H == 
  \<lambda>q. the (hm_lookup q (hh_map_to_nat.map_to_nat (hta_states H)))"

definition hta_reindex 
  :: "('Q::hashable,'L::hashable) hashedTa \<Rightarrow> (nat,'L) hashedTa" where
  "hta_reindex H == hta_remap (reindex_map H) H"

declare hta_reindex_def [code del]

  \<comment> \<open>This version is more efficient, as the map is only computed once\<close>
lemma [code]: "hta_reindex H = (
  let mp = (hh_map_to_nat.map_to_nat (hta_states H)) in
    hta_remap (\<lambda>q. the (hm_lookup q mp)) H)
  "
  by (simp add: Let_def hta_reindex_def reindex_map_def)


lemma (in hashedTa) reindex_map_correct:
  "inj_on (reindex_map H) (ta_rstates (hta_\<alpha> H))"
proof -
  have [simp]: 
    "reindex_map H = the \<circ> hm_\<alpha> (hh_map_to_nat.map_to_nat (hta_states H))"
    by (rule ext)
       (simp add: reindex_map_def hm.correct 
         hh_map_to_nat.map_to_nat_correct(4) 
         hta_states_correct)

  show ?thesis
    apply (simp add: hta_states_correct(1)[symmetric])
    apply (rule inj_on_map_the)
    apply (simp_all add: hh_map_to_nat.map_to_nat_correct hta_states_correct(2))
    done
qed

theorem (in hashedTa) hta_reindex_correct:
  "ta_lang (hta_\<alpha> (hta_reindex H)) = ta_lang (hta_\<alpha> H)"
  "hashedTa (hta_reindex H)"
  apply (unfold hta_reindex_def)
  apply (simp_all 
    add: hta_remap_correct tree_automaton.remap_lang[OF hta_\<alpha>_is_ta] 
         reindex_map_correct)
  done

subsection "Union"

text "Computes the union of two automata"
definition hta_union 
  :: "('q1::hashable,'l::hashable) hashedTa 
      \<Rightarrow> ('q2::hashable,'l) hashedTa 
      \<Rightarrow> (('q1,'q2) ustate_wrapper,'l) hashedTa" 
  where "hta_union H1 H2 == 
    init_hta (hs_union (hh_set_xy.g_image USW1 (hta_Qi H1)) 
                       (hh_set_xy.g_image USW2 (hta_Qi H2))) 
             (ls_union_dj (ll_set_xy.g_image (remap_rule USW1) (hta_\<delta> H1)) 
                          (ll_set_xy.g_image (remap_rule USW2) (hta_\<delta> H2)))"

lemma hta_union_correct': 
  assumes TA: "hashedTa H1" "hashedTa H2"
  shows "hta_\<alpha> (hta_union H1 H2) 
         = ta_union_wrap (hta_\<alpha> H1) (hta_\<alpha> H2)" (is ?T1)
        "hashedTa (hta_union H1 H2)" (is ?T2)
proof -
  interpret a1: hashedTa H1 + a2: hashedTa H2 using TA .
  show ?T1 ?T2 
    apply (auto 
      simp add: hta_union_def init_hta_def hta_\<alpha>_def 
                hs.correct ls.correct 
                ll_set_xy.image_correct hh_set_xy.image_correct
                ta_remap_def ta_union_def ta_union_wrap_def)
    apply (unfold_locales)
    apply (auto 
      simp add: hs.correct ls.correct)
    done
qed

theorem hta_union_correct: 
  assumes TA: "hashedTa H1" "hashedTa H2"
  shows 
    "ta_lang (hta_\<alpha> (hta_union H1 H2)) 
     = ta_lang (hta_\<alpha> H1) \<union> ta_lang (hta_\<alpha> H2)" (is ?T1)
    "hashedTa (hta_union H1 H2)" (is ?T2)
proof -
  interpret a1: hashedTa H1 + a2: hashedTa H2 using TA .
  show ?T1 ?T2
    by (simp_all add: hta_union_correct'[OF TA] ta_union_wrap_correct)
qed

subsection "Operators to Construct Tree Automata"
text \<open>
  This section defines operators that add initial states and rules to a tree 
  automaton, and thus incrementally construct a tree automaton from the empty
  automaton.
\<close>

\<comment> \<open>The empty automaton\<close>
definition hta_empty :: "unit \<Rightarrow> ('q::hashable,'l::hashable) hashedTa" 
  where "hta_empty u == init_hta (hs_empty ()) (ls_empty ())"
lemma hta_empty_correct [simp, intro!]: 
  shows "(hta_\<alpha> (hta_empty ())) = ta_empty"
        "hashedTa (hta_empty ())"
  apply (auto
    simp add: init_hta_def hta_empty_def hta_\<alpha>_def \<delta>_states_def ta_empty_def
              hs.correct ls.correct)
  apply (unfold_locales)
  apply (auto simp add: hs.correct ls.correct)
  done

\<comment> \<open>Add an initial state to the automaton\<close>
definition hta_add_qi 
  :: "'q \<Rightarrow> ('q::hashable,'l::hashable) hashedTa \<Rightarrow> ('q,'l) hashedTa" 
  where "hta_add_qi qi H == init_hta (hs_ins qi (hta_Qi H)) (hta_\<delta> H)"

lemma (in hashedTa) hta_add_qi_correct[simp, intro!]:
  shows "hta_\<alpha> (hta_add_qi qi H) 
         = \<lparr> ta_initial = insert qi (ta_initial (hta_\<alpha> H)), 
             ta_rules = ta_rules (hta_\<alpha> H) 
           \<rparr>"
        "hashedTa (hta_add_qi qi H)"
  apply (auto 
    simp add: init_hta_def hta_add_qi_def hta_\<alpha>_def \<delta>_states_def 
              hs.correct)
  apply (unfold_locales)
  apply (auto simp add: hs.correct)
  done

lemmas [simp, intro] = hashedTa.hta_add_qi_correct

\<comment> \<open>Add a rule to the automaton\<close>
definition hta_add_rule 
  :: "('q,'l) ta_rule \<Rightarrow> ('q::hashable,'l::hashable) hashedTa 
      \<Rightarrow> ('q,'l) hashedTa" 
  where "hta_add_rule r H == init_hta (hta_Qi H) (ls_ins r (hta_\<delta> H))"

lemma (in hashedTa) hta_add_rule_correct[simp, intro!]:
  shows "hta_\<alpha> (hta_add_rule r H) 
         = \<lparr> ta_initial = ta_initial (hta_\<alpha> H), 
             ta_rules = insert r (ta_rules (hta_\<alpha> H)) 
           \<rparr>"
        "hashedTa (hta_add_rule r H)"
  apply (auto 
    simp add: init_hta_def hta_add_rule_def hta_\<alpha>_def 
              \<delta>_states_def ls.correct)
  apply (unfold_locales)
  apply (auto simp add: ls.correct)
  done

lemmas [simp, intro] = hashedTa.hta_add_rule_correct


  \<comment> \<open>Reduces an automaton to the given set of states\<close>
definition "hta_reduce H Q ==
  init_hta (hs_inter Q (hta_Qi H)) 
           (ll_set_xy.g_image_filter 
              (\<lambda>r. if hs_memb (lhs r) Q \<and> list_all (\<lambda>q. hs_memb q Q) (rhsq r) then Some r else None) 
              (hta_\<delta> H))
"

theorem (in hashedTa) hta_reduce_correct:
  assumes INV[simp]: "hs_invar Q"
  shows
  "hta_\<alpha> (hta_reduce H Q) = ta_reduce (hta_\<alpha> H) (hs_\<alpha> Q)" (is ?T1)
  "hashedTa (hta_reduce H Q)" (is ?T2)
  apply (auto 
    simp add: 
      hta_reduce_def ta_reduce_def hta_\<alpha>_def init_hta_def 
      hs.correct ls.correct
    (*hs_correct ls_correct *)
      list_all_iff 
      reduce_rules_def rule_states_simp 
      ll_set_xy.image_filter_correct
    split: 
      ta_rule.split_asm
  ) [1]
  apply (unfold_locales)
  apply (unfold hta_reduce_def init_hta_def)
  apply (auto simp add: hs.correct ls.correct)
  done



subsection "Backwards Reduction and Emptiness Check"

text \<open>
  The algorithm uses a map from states to the set of rules that contain 
  the state on their rhs.
\<close>

  \<comment> \<open>Add an entry to the index\<close>
definition "rqrm_add q r res ==
  case hm_lookup q res of
    None \<Rightarrow> hm_update q (ls_ins r (ls_empty ())) res |
    Some s \<Rightarrow> hm_update q (ls_ins r s) res
  "

  \<comment> \<open>Lookup the set of rules with given state on rhs\<close>
definition "rqrm_lookup rqrm q == case hm_lookup q rqrm of
  None \<Rightarrow> ls_empty () |
  Some s \<Rightarrow> s
  "

  \<comment> \<open>Build the index from a set of rules\<close>
definition build_rqrm 
  :: "('q::hashable,'l::hashable) ta_rule ls 
      \<Rightarrow> ('q,('q,'l) ta_rule ls) hm" 
  where
  "build_rqrm \<delta> ==
    ls_iteratei \<delta> (\<lambda>_. True)
      (\<lambda>r res. 
        foldl (\<lambda>res q. rqrm_add q r res) res (rhsq r)
      )
      (hm_empty ())
  "

\<comment> \<open>Whether the index satisfies the map and set invariants\<close>
definition "rqrm_invar rqrm == 
  hm_invar rqrm \<and> (\<forall>q. ls_invar (rqrm_lookup rqrm q))"
\<comment> \<open>Whether the index really maps a state to the set of rules with this 
    state on their rhs\<close>
definition "rqrm_prop \<delta> rqrm == 
  \<forall>q. ls_\<alpha> (rqrm_lookup rqrm q) = {r\<in>\<delta>. q\<in>set (rhsq r)}"

lemma rqrm_\<alpha>_lookup_update[simp]: 
  "rqrm_invar rqrm \<Longrightarrow> 
    ls_\<alpha> (rqrm_lookup (rqrm_add q r rqrm) q') 
    = ( if q=q' then 
          insert r (ls_\<alpha> (rqrm_lookup rqrm q')) 
        else 
          ls_\<alpha> (rqrm_lookup rqrm q')
      )"
  by (simp 
    add: rqrm_lookup_def rqrm_add_def rqrm_invar_def hm.correct 
         ls.correct 
    split: option.split_asm option.split)

lemma rqrm_propD: 
  "rqrm_prop \<delta> rqrm \<Longrightarrow> ls_\<alpha> (rqrm_lookup rqrm q) = {r\<in>\<delta>. q\<in>set (rhsq r)}"
  by (simp add: rqrm_prop_def)

lemma build_rqrm_correct:
  fixes \<delta>
  assumes [simp]: "ls_invar \<delta>"
  shows "rqrm_invar (build_rqrm \<delta>)" (is ?T1) and
        "rqrm_prop (ls_\<alpha> \<delta>) (build_rqrm \<delta>)" (is ?T2)
proof -
  have "rqrm_invar (build_rqrm \<delta>) \<and> 
    (\<forall>q. ls_\<alpha> (rqrm_lookup (build_rqrm \<delta>) q) = {r\<in>ls_\<alpha> \<delta>. q\<in>set (rhsq r)})"
    apply (unfold build_rqrm_def)
    apply (rule_tac 
      I="\<lambda>it res. (rqrm_invar res) 
                  \<and> (\<forall>q. ls_\<alpha> (rqrm_lookup res q) 
                     = {r\<in>ls_\<alpha> \<delta> - it. q\<in>set (rhsq r)})" 
      in ls.iterate_rule_P)
      \<comment> \<open>Invar\<close>
    apply simp
      \<comment> \<open>Initial\<close>
    apply (simp add: hm_correct ls_correct rqrm_lookup_def rqrm_invar_def)
      \<comment> \<open>Step\<close>
    apply (rule_tac 
      I="\<lambda>res itl itr. 
        (rqrm_invar res) 
        \<and> (\<forall>q. ls_\<alpha> (rqrm_lookup res q) 
           = {r\<in>ls_\<alpha> \<delta> - it. q\<in>set (rhsq r)} 
             \<union> {r. r=x \<and> q\<in>set itl})" 
      in Misc.foldl_rule_P)
        \<comment> \<open>Initial\<close>
      apply simp
        \<comment> \<open>Step\<close>
      apply (intro conjI)
      apply (simp 
        add: rqrm_invar_def rqrm_add_def rqrm_lookup_def hm_correct 
             ls_correct 
        split: option.split option.split_asm)
      apply simp
      apply (simp 
        add: rqrm_add_def rqrm_lookup_def hm_correct ls_correct 
        split: option.split option.split_asm)
      apply (auto) [1]
        \<comment> \<open>Final\<close>
      apply auto [1]
      \<comment> \<open>Final\<close>
    apply simp
    done
  thus ?T1 ?T2 by (simp_all add: rqrm_prop_def)
qed

\<comment> \<open>A state of the basic algorithm contains a set of discovered states, 
    a worklist and a map from rules to the number of distinct states on 
    its RHS that have not yet been discovered or are still on the worklist\<close>
type_synonym ('Q,'L) brc_state 
  = "'Q hs \<times> 'Q list \<times> (('Q,'L) ta_rule, nat) hm"

\<comment> \<open>Abstraction to @{text \<alpha>'}-level:\<close>
definition brc_\<alpha> 
  :: "('Q::hashable,'L::hashable) brc_state \<Rightarrow> ('Q,'L) br'_state"
  where "brc_\<alpha> == \<lambda>(Q,W,rcm). (hs_\<alpha> Q, set W, hm_\<alpha> rcm)"

definition brc_invar_add :: "('Q::hashable,'L::hashable) brc_state set" 
  where
  "brc_invar_add == {(Q,W,rcm). 
    hs_invar Q \<and> 
    distinct W \<and> 
    hm_invar rcm
    \<^cancel>\<open>\<and> set W \<subseteq> hs_\<alpha> Q\<close>}
  "

definition "brc_invar \<delta> == brc_invar_add \<inter> {s. brc_\<alpha> s \<in> br'_invar \<delta>}"

definition brc_cond :: "('q::hashable,'l::hashable) brc_state \<Rightarrow> bool" 
  where "brc_cond == \<lambda>(Q,W,rcm). W\<noteq>[]"

definition brc_inner_step 
  :: "('q,'l) ta_rule \<Rightarrow> ('q::hashable,'l::hashable) brc_state 
      \<Rightarrow> ('q,'l) brc_state"
  where 
  "brc_inner_step r == \<lambda>(Q,W,rcm). 
    let c=the (hm_lookup r rcm);
        rcm' = hm_update r (c-(1::nat)) rcm;
        Q' = (if c \<le> 1 then hs_ins (lhs r) Q else Q);
        W' = (if c \<le> 1 \<and> \<not> hs_memb (lhs r) Q then lhs r # W else W) in
      (Q',W',rcm')"

definition brc_step 
  :: "('q,('q,'l) ta_rule ls) hm 
      \<Rightarrow> ('q::hashable,'l::hashable) brc_state 
      \<Rightarrow> ('q,'l) brc_state" 
where 
  "brc_step rqrm == \<lambda>(Q,W,rcm).
    ls_iteratei (rqrm_lookup rqrm (hd W)) (\<lambda>_. True) brc_inner_step 
      (Q,tl W, rcm)"

  \<comment> \<open>Initial concrete state\<close>
definition brc_iq :: "('q,'l) ta_rule ls \<Rightarrow> 'q::hashable hs" 
  where "brc_iq \<delta> == lh_set_xy.g_image_filter (\<lambda>r. 
    if rhsq r = [] then Some (lhs r) else None) \<delta>"

definition brc_rcm_init 
  :: "('q::hashable,'l::hashable) ta_rule ls 
      \<Rightarrow> (('q,'l) ta_rule,nat) hm" 
  where "brc_rcm_init \<delta> == 
    ls_iteratei \<delta> (\<lambda>_. True) 
      (\<lambda>r res. hm_update r ((length (remdups (rhsq r)))) res) 
      (hm_empty ())"

definition brc_initial 
  :: "('q::hashable,'l::hashable) ta_rule ls \<Rightarrow> ('q,'l) brc_state" 
  where "brc_initial \<delta> == 
    let iq=brc_iq \<delta> in 
      (iq, hs_to_list (iq), brc_rcm_init \<delta>)"

definition "brc_det_algo rqrm \<delta> == \<lparr>
  dwa_cond = brc_cond,
  dwa_step = brc_step rqrm,
  dwa_initial = brc_initial \<delta>,
  dwa_invar = brc_invar (ls_\<alpha> \<delta>)
\<rparr>"

  \<comment> \<open>Additional facts needed from the abstract level\<close>
lemma brc_inv_imp_WssQ: "brc_\<alpha> (Q,W,rcm)\<in>br'_invar \<delta> \<Longrightarrow> set W \<subseteq> hs_\<alpha> Q"
  by (auto simp add: brc_\<alpha>_def br'_invar_def br'_\<alpha>_def br_invar_def)

lemma brc_iq_correct: 
  assumes [simp]: "ls_invar \<delta>"
  shows "hs_invar (brc_iq \<delta>)"
        "hs_\<alpha> (brc_iq \<delta>) = br_iq (ls_\<alpha> \<delta>)"
  by (auto simp add: brc_iq_def br_iq_def lh_set_xy.image_filter_correct)

lemma brc_rcm_init_correct:
  assumes INV[simp]: "ls_invar \<delta>"
  shows "r\<in>ls_\<alpha> \<delta> 
    \<Longrightarrow> hm_\<alpha> (brc_rcm_init \<delta>) r = Some ((card (set (rhsq r))))" 
  (is "_ \<Longrightarrow> ?T1 r") and
    "hm_invar (brc_rcm_init \<delta>)" (is ?T2)
proof -
  have G: "(\<forall>r\<in>ls_\<alpha> \<delta>. ?T1 r) \<and> ?T2"
    apply (unfold brc_rcm_init_def)
    apply (rule_tac 
      I="\<lambda>it res. hm_invar res 
           \<and> (\<forall>r\<in>ls_\<alpha> \<delta> - it. hm_\<alpha> res r = Some ((card (set (rhsq r)))))" 
      in ls.iterate_rule_P)
      \<comment> \<open>Invar\<close>
    apply simp
      \<comment> \<open>Init\<close>
    apply (auto simp add: hm_correct) [1]
      \<comment> \<open>Step\<close>
    apply (rule conjI)
      apply (simp add: hm.update_correct)

      apply (simp only: hm_correct hs_correct INV)
      apply (rule ballI)
      apply (case_tac "r=x")
      apply (auto 
        simp add: length_remdups_card 
        intro!: arg_cong[where f=card]) [1]
      apply simp
      \<comment> \<open>Final\<close>
    apply simp
    done
  from G show ?T2 by auto
  fix r
  assume "r\<in>ls_\<alpha> \<delta>"
  thus "?T1 r" using G by auto
qed

lemma brc_inner_step_br'_desc: 
  "\<lbrakk> (Q,W,rcm)\<in>brc_invar \<delta> \<rbrakk> \<Longrightarrow> brc_\<alpha> (brc_inner_step r (Q,W,rcm)) = (
    if the (hm_\<alpha> rcm r) \<le> 1 then 
      insert (lhs r) (hs_\<alpha> Q) 
    else hs_\<alpha> Q, 
    if the (hm_\<alpha> rcm r) \<le> 1 \<and> (lhs r) \<notin> hs_\<alpha> Q then 
      insert (lhs r) (set W) 
    else (set W), 
    ((hm_\<alpha> rcm)(r \<mapsto> the (hm_\<alpha> rcm r) - 1))
  )"
  by (simp 
    add: brc_invar_def brc_invar_add_def brc_\<alpha>_def brc_inner_step_def Let_def 
         hs_correct hm_correct)

lemma brc_step_invar:
  assumes RQRM: "rqrm_invar rqrm"
  shows "\<lbrakk> \<Sigma>\<in>brc_invar_add; brc_\<alpha> \<Sigma>\<in>br'_invar \<delta>; brc_cond \<Sigma> \<rbrakk> 
         \<Longrightarrow> (brc_step rqrm \<Sigma>)\<in>brc_invar_add"
  apply (cases \<Sigma>)
  apply (simp add: brc_step_def)
  apply (rule_tac I="\<lambda>it (Q,W,rcm). (Q,W,rcm)\<in>brc_invar_add \<and> set W \<subseteq> hs_\<alpha> Q" 
                  in ls.iterate_rule_P)
  apply (simp add: RQRM[unfolded rqrm_invar_def])
  apply (case_tac b)
  apply (simp add: brc_invar_add_def distinct_tl brc_cond_def)
  apply (auto simp add: brc_invar_add_def distinct_tl brc_cond_def 
              dest!: brc_inv_imp_WssQ) [1]
  apply (case_tac \<sigma>)
  apply (auto simp add: brc_invar_add_def br_invar_def brc_inner_step_def 
                        Let_def hs_correct hm_correct) [1]
  apply (case_tac \<sigma>)
  apply simp
  done


lemma brc_step_abs:
  assumes RQRM: "rqrm_invar rqrm" "rqrm_prop \<delta> rqrm"
  assumes A: "\<Sigma>\<in>brc_invar \<delta>" "brc_cond \<Sigma>"  
  shows "(brc_\<alpha> \<Sigma>, brc_\<alpha> (brc_step rqrm \<Sigma>)) \<in> br'_step \<delta>"
proof -
  obtain Q W rcm where [simp]: "\<Sigma>=(Q,W,rcm)" by (cases \<Sigma>) auto
  from A show ?thesis
    apply (simp add: brc_step_def)
    apply (rule 
      br'_inner_step_proof[OF ls.v1_iteratei_impl, 
         where cinvar="\<lambda>it (Q,W,rcm). (Q,W,rcm)\<in>brc_invar_add 
                                      \<and> set W \<subseteq> hs_\<alpha> Q" and 
               q="hd W"])
    apply (case_tac W) 
    apply (auto simp add: brc_cond_def brc_invar_add_def brc_invar_def 
                dest!: brc_inv_imp_WssQ) [2]
    prefer 6
    apply (simp add: brc_\<alpha>_def)
    apply (case_tac \<Sigma>)
    apply (auto 
      simp add: brc_invar_def brc_invar_add_def brc_inner_step_def 
                Let_def hm_correct hs_correct) [1]
    apply (auto 
      simp add: brc_invar_add_def brc_inner_step_def brc_\<alpha>_def 
                br'_inner_step_def Let_def hm_correct hs_correct) [1]
    apply (simp add: RQRM[unfolded rqrm_invar_def])
    apply (simp add: rqrm_propD[OF RQRM(2)])
    apply (case_tac W)
    apply (simp_all add: brc_\<alpha>_def brc_cond_def brc_invar_def) [2]
    apply (case_tac W)
    apply (simp_all add: brc_\<alpha>_def brc_cond_def brc_invar_def 
                         brc_invar_add_def) [2]
    done
qed
    
lemma brc_initial_invar: "ls_invar \<delta> \<Longrightarrow> (brc_initial \<delta>)\<in>brc_invar_add"
  by (simp 
    add: brc_invar_add_def brc_initial_def brc_iq_correct Let_def 
         brc_rcm_init_correct hs_correct)

lemma brc_cond_abs: "brc_cond \<Sigma> \<longleftrightarrow> (brc_\<alpha> \<Sigma>)\<in>br'_cond"
  apply (cases \<Sigma>)
  apply (simp add: brc_cond_def br'_cond_def brc_\<alpha>_def)
  done

lemma brc_initial_abs: 
  "ls_invar \<delta> \<Longrightarrow> brc_\<alpha> (brc_initial \<delta>) \<in> br'_initial (ls_\<alpha> \<delta>)"
  by (auto 
    simp add: brc_initial_def Let_def brc_\<alpha>_def brc_iq_correct 
              brc_rcm_init_correct hs_correct 
    intro: br'_initial.intros)

lemma brc_pref_br':
  assumes RQRM[simp]: "rqrm_invar rqrm" "rqrm_prop (ls_\<alpha> \<delta>) rqrm"
  assumes INV[simp]: "ls_invar \<delta>"
  shows "wa_precise_refine (det_wa_wa (brc_det_algo rqrm \<delta>)) 
                           (br'_algo (ls_\<alpha> \<delta>)) 
                           brc_\<alpha>"
  apply (unfold_locales)
  apply (simp_all add: brc_det_algo_def br'_algo_def det_wa_wa_def)
  apply (simp add: brc_cond_abs)
  apply (auto simp add: brc_step_abs[OF RQRM]) [1]
  apply (simp add: brc_initial_abs)
  apply (auto simp add: brc_invar_def) [1]
  apply (simp add: brc_cond_abs)
  done

lemma brc_while_algo:
  assumes RQRM[simp]: "rqrm_invar rqrm" "rqrm_prop (ls_\<alpha> \<delta>) rqrm"
  assumes INV[simp]: "ls_invar \<delta>"
  shows "while_algo (det_wa_wa (brc_det_algo rqrm \<delta>))"
proof -
  from brc_pref_br'[OF RQRM INV] interpret 
    ref: wa_precise_refine "(det_wa_wa (brc_det_algo rqrm \<delta>))" 
                           "(br'_algo (ls_\<alpha> \<delta>))" 
                           brc_\<alpha> .
  show ?thesis
    apply (rule ref.wa_intro)
    apply (simp add: br'_while_algo)
    apply (simp_all add: det_wa_wa_def brc_det_algo_def br'_algo_def)
    apply (simp add: brc_invar_def)
    apply (auto simp add: brc_step_invar) [1]
    apply (simp add: brc_initial_invar)
    done
qed

lemmas brc_det_while_algo =
  det_while_algo_intro[OF brc_while_algo]


lemma fst_brc_\<alpha>: "fst (brc_\<alpha> s) = hs_\<alpha> (fst s)" 
  by (cases s) (simp add: brc_\<alpha>_def)

lemmas brc_invar_final =
  wa_precise_refine.transfer_correctness[OF 
    brc_pref_br' br'_invar_final, unfolded fst_brc_\<alpha>]

definition "hta_bwd_reduce H == 
  let rqrm = build_rqrm (hta_\<delta> H) in 
    hta_reduce 
      H 
      (fst (while brc_cond (brc_step rqrm) (brc_initial (hta_\<delta> H))))
"

theorem (in hashedTa) hta_bwd_reduce_correct:
  shows "hta_\<alpha> (hta_bwd_reduce H) 
         = ta_reduce (hta_\<alpha> H) (b_accessible (ls_\<alpha> (hta_\<delta> H)))" (is ?T1)
        "hashedTa (hta_bwd_reduce H)" (is ?T2)
proof -
  interpret det_while_algo "(brc_det_algo (build_rqrm \<delta>) \<delta>)"
    by (rule brc_det_while_algo)
       (simp_all add: build_rqrm_correct)

  have LC: "(while brc_cond (brc_step (build_rqrm \<delta>)) (brc_initial \<delta>)) = loop"
    by (unfold loop_def)
       (simp add: brc_det_algo_def)

  from while_proof'[OF brc_invar_final] have 
    G1: "hs_\<alpha> (fst loop) = b_accessible (ls_\<alpha> \<delta>)" 
    by (simp add: build_rqrm_correct)
  have G2: "loop \<in> brc_invar (ls_\<alpha> \<delta>)"
    by (rule while_proof)
       (simp add: brc_det_algo_def)
  hence [simp]: "hs_invar (fst loop)"
    by (cases loop)
       (simp add: brc_invar_def brc_invar_add_def)

  show ?T1 ?T2
    by (simp_all add: hta_bwd_reduce_def LC hta_reduce_correct G1)
    
qed

subsubsection \<open>Emptiness Check with Witness Computation\<close>

definition brec_construct_witness 
  :: "('q::hashable,'l::hashable tree) hm \<Rightarrow> ('q,'l) ta_rule \<Rightarrow> 'l tree"
  where "brec_construct_witness Qm r == 
  NODE (rhsl r) (List.map (\<lambda>q. the (hm_lookup q Qm)) (rhsq r))"

lemma brec_construct_witness_correct: 
  "\<lbrakk>hm_invar Qm\<rbrakk> \<Longrightarrow> 
    brec_construct_witness Qm r = construct_witness (hm_\<alpha> Qm) r"
  by (auto 
    simp add: construct_witness_def brec_construct_witness_def hm_correct)

type_synonym ('Q,'L) brec_state 
  = "(('Q,'L tree) hm 
      \<times> 'Q fifo 
      \<times> (('Q,'L) ta_rule, nat) hm 
      \<times> 'Q option)"


  \<comment> \<open>Abstractions\<close>
definition brec_\<alpha> 
  :: "('Q::hashable,'L::hashable) brec_state \<Rightarrow> ('Q,'L) brw_state"
  where "brec_\<alpha> == \<lambda>(Q,W,rcm,f). (hm_\<alpha> Q, set (fifo_\<alpha> W), (hm_\<alpha> rcm))"

definition brec_inner_step 
  :: "'q hs \<Rightarrow> ('q,'l) ta_rule 
      \<Rightarrow> ('q::hashable,'l::hashable) brec_state 
      \<Rightarrow> ('q,'l) brec_state"
  where "brec_inner_step Qi r == \<lambda>(Q,W,rcm,qwit). 
    let c=the (hm_lookup r rcm); 
        cond = c \<le> 1 \<and> hm_lookup (lhs r) Q = None;
        rcm' = hm_update r (c-(1::nat)) rcm;
        Q' = ( if cond then 
                 hm_update (lhs r) (brec_construct_witness Q r) Q 
               else Q);
        W' = (if cond then fifo_enqueue (lhs r) W else W);
        qwit' = (if c \<le> 1 \<and> hs_memb (lhs r) Qi then Some (lhs r) else qwit)
    in
      (Q',W',rcm',qwit')"

definition brec_step 
  :: "('q,('q,'l) ta_rule ls) hm \<Rightarrow> 'q hs 
      \<Rightarrow> ('q::hashable,'l::hashable) brec_state 
      \<Rightarrow> ('q,'l) brec_state" 
  where "brec_step rqrm Qi == \<lambda>(Q,W,rcm,qwit).
    let (q,W')=fifo_dequeue W in 
      ls_iteratei (rqrm_lookup rqrm q) (\<lambda>_. True) 
        (brec_inner_step Qi) (Q,W',rcm,qwit)
  "

definition brec_iqm 
  :: "('q::hashable,'l::hashable) ta_rule ls \<Rightarrow> ('q,'l tree) hm" 
  where "brec_iqm \<delta> == 
    ls_iteratei \<delta> (\<lambda>_. True) (\<lambda>r m. if rhsq r = [] then 
                         hm_update (lhs r) (NODE (rhsl r) []) m 
                      else m) 
                (hm_empty ())"

definition brec_initial 
  :: "'q hs \<Rightarrow> ('q::hashable,'l::hashable) ta_rule ls 
      \<Rightarrow> ('q,'l) brec_state" 
  where "brec_initial Qi \<delta> == 
  let iq=brc_iq \<delta> in 
    ( brec_iqm \<delta>, 
      hs_to_fifo.g_set_to_listr iq, 
      brc_rcm_init \<delta>,
      hh_set_xx.g_disjoint_witness iq Qi)"

definition brec_cond 
  :: "('q,'l) brec_state \<Rightarrow> bool" 
  where "brec_cond == \<lambda>(Q,W,rcm,qwit). \<not> fifo_isEmpty W \<and> qwit = None"

definition brec_invar_add
  :: "'Q set \<Rightarrow> ('Q::hashable,'L::hashable) brec_state set" 
  where
  "brec_invar_add Qi == {(Q,W,rcm,qwit). 
    hm_invar Q \<and> 
    distinct (fifo_\<alpha> W) \<and> 
    hm_invar rcm \<and>
    ( case qwit of 
        None \<Rightarrow> Qi \<inter> dom (hm_\<alpha> Q) = {} | 
        Some q \<Rightarrow> q\<in>Qi \<inter> dom (hm_\<alpha> Q))}
  "

definition "brec_invar Qi \<delta> == brec_invar_add Qi \<inter> {s. brec_\<alpha> s \<in> brw_invar \<delta>}"

definition "brec_invar_inner Qi == 
  brec_invar_add Qi \<inter> {(Q,W,_,_). set (fifo_\<alpha> W) \<subseteq> dom (hm_\<alpha> Q)}"

lemma brec_invar_cons: 
  "\<Sigma>\<in>brec_invar Qi \<delta> \<Longrightarrow> \<Sigma>\<in>brec_invar_inner Qi"
  apply (cases \<Sigma>)
  apply (simp add: brec_invar_def brw_invar_def br'_invar_def br_invar_def
                   brec_\<alpha>_def brw_\<alpha>_def br'_\<alpha>_def brec_invar_inner_def)
  done

lemma brec_brw_invar_cons: 
  "brec_\<alpha> \<Sigma> \<in> brw_invar Qi \<Longrightarrow> set (fifo_\<alpha> (fst (snd \<Sigma>))) \<subseteq> dom (hm_\<alpha> (fst \<Sigma>))"
  apply (cases \<Sigma>)
  apply (simp add: brec_invar_def brw_invar_def br'_invar_def br_invar_def
                   brec_\<alpha>_def brw_\<alpha>_def br'_\<alpha>_def)
  done

definition "brec_det_algo rqrm Qi \<delta> == \<lparr>
  dwa_cond=brec_cond,
  dwa_step=brec_step rqrm Qi,
  dwa_initial=brec_initial Qi \<delta>,
  dwa_invar=brec_invar (hs_\<alpha> Qi) (ls_\<alpha> \<delta>)
\<rparr>"

lemma brec_iqm_correct':
  assumes INV[simp]: "ls_invar \<delta>"
  shows 
    "dom (hm_\<alpha> (brec_iqm \<delta>)) = {lhs r | r. r\<in>ls_\<alpha> \<delta> \<and> rhsq r = []}" (is ?T1)
    "witness_prop (ls_\<alpha> \<delta>) (hm_\<alpha> (brec_iqm \<delta>))" (is ?T2)
    "hm_invar (brec_iqm \<delta>)" (is ?T3)
proof -
  have "?T1 \<and> ?T2 \<and> ?T3"
    apply (unfold brec_iqm_def)
    apply (rule_tac 
      I="\<lambda>it m. hm_invar m 
                \<and> dom (hm_\<alpha> m) = {lhs r | r. r\<in>ls_\<alpha> \<delta> - it \<and> rhsq r = []} 
                \<and> witness_prop (ls_\<alpha> \<delta>) (hm_\<alpha> m)" 
      in ls.iterate_rule_P)
    apply simp
    apply (auto simp add: hm_correct witness_prop_def) [1]
    apply (auto simp add: hm_correct witness_prop_def) [1]
    apply (case_tac x)
    apply (auto intro: accs.intros) [1]
    apply simp
    done
  thus ?T1 ?T2 ?T3 by auto
qed

lemma brec_iqm_correct:
  assumes INV[simp]: "ls_invar \<delta>"
  shows "hm_\<alpha> (brec_iqm \<delta>) \<in> brw_iq (ls_\<alpha> \<delta>)"
proof -
  have "(\<forall>q t. hm_\<alpha> (brec_iqm \<delta>) q = Some t 
          \<longrightarrow> (\<exists>r\<in>ls_\<alpha> \<delta>. rhsq r = [] \<and> q = lhs r \<and> t = NODE (rhsl r) [])) 
        \<and> (\<forall>r\<in>ls_\<alpha> \<delta>. rhsq r = [] \<longrightarrow> hm_\<alpha> (brec_iqm \<delta>) (lhs r) \<noteq> None)" 
    apply (unfold brec_iqm_def)
    apply (rule_tac I="\<lambda>it m. (
      (hm_invar m) \<and> 
      (\<forall>q t. hm_\<alpha> m q = Some t 
        \<longrightarrow> (\<exists>r\<in>ls_\<alpha> \<delta>. rhsq r = [] \<and> q = lhs r \<and> t = NODE (rhsl r) [])) \<and> 
      (\<forall>r\<in>ls_\<alpha> \<delta>-it. rhsq r = [] \<longrightarrow> hm_\<alpha> m (lhs r) \<noteq> None)
      )" 
      in ls.iterate_rule_P)
    apply simp
    apply (simp add: hm_correct)
    apply (auto simp add: hm_correct) [1]
    apply (auto simp add: hm_correct) [1]
    done
  thus ?thesis by (blast intro: brw_iq.intros)
qed

lemma brec_inner_step_brw_desc: 
  "\<lbrakk> \<Sigma>\<in>brec_invar_inner (hs_\<alpha> Qi) \<rbrakk> 
    \<Longrightarrow> (brec_\<alpha> \<Sigma>, brec_\<alpha> (brec_inner_step Qi r \<Sigma>)) \<in> brw_inner_step r"
  apply (cases \<Sigma>)
  apply (rule brw_inner_step.intros)
  apply (simp only: )
  apply (simp only: brec_\<alpha>_def split_conv)
  apply (simp only: brec_inner_step_def brec_\<alpha>_def Let_def split_conv)
  apply (auto 
    simp add: brec_invar_inner_def brec_invar_add_def brec_\<alpha>_def 
              brec_inner_step_def 
              Let_def hs_correct hm_correct fifo_correct
              brec_construct_witness_correct)
  done


lemma brec_step_invar:
  assumes RQRM: "rqrm_invar rqrm" "rqrm_prop \<delta> rqrm"
  assumes [simp]: "hs_invar Qi"
  shows "\<lbrakk> \<Sigma>\<in>brec_invar_add (hs_\<alpha> Qi); brec_\<alpha> \<Sigma> \<in> brw_invar \<delta>;  brec_cond \<Sigma> \<rbrakk> 
          \<Longrightarrow> (brec_step rqrm Qi \<Sigma>)\<in>brec_invar_add (hs_\<alpha> Qi)"
  apply (frule brec_brw_invar_cons)
  apply (cases \<Sigma>)
  apply (simp add: brec_step_def fifo_correct)
  apply (case_tac "fifo_\<alpha> b")
  apply (simp 
    add: brec_invar_def distinct_tl brec_cond_def fifo_correct
         )
  apply (rule_tac s=b in fifo.removelE)
  apply simp
  apply simp
  apply simp

  apply (rule_tac 
    I="\<lambda>it (Q,W,rcm,qwit). (Q,W,rcm,qwit)\<in>brec_invar_add (hs_\<alpha> Qi) 
                           \<and> set (fifo_\<alpha> W) \<subseteq> dom (hm_\<alpha> Q)" 
    in ls.iterate_rule_P)
  apply simp
  apply (simp 
    add: brec_invar_def distinct_tl brec_cond_def fifo_correct
         )
  apply (simp 
    add: brec_invar_def brec_invar_add_def distinct_tl brec_cond_def 
         fifo_correct)
  apply (case_tac \<sigma>)
  apply (auto 
    simp add: brec_invar_add_def brec_inner_step_def Let_def hs_correct 
              hm_correct fifo_correct split: option.split_asm) [1]
  apply (case_tac \<sigma>)
  apply simp
  done

lemma brec_step_abs:
  assumes RQRM: "rqrm_invar rqrm" "rqrm_prop \<delta> rqrm"
  assumes INV[simp]: "hs_invar Qi"
  assumes A': "\<Sigma>\<in>brec_invar (hs_\<alpha> Qi) \<delta>"
  assumes COND: "brec_cond \<Sigma>"
  shows "(brec_\<alpha> \<Sigma>, brec_\<alpha> (brec_step rqrm Qi \<Sigma>)) \<in> brw_step \<delta>"
proof -
  from A' have A: "(brec_\<alpha> \<Sigma>)\<in>brw_invar \<delta>" "\<Sigma>\<in>brec_invar_add (hs_\<alpha> Qi)"
    by (simp_all add: brec_invar_def)

  obtain Q W rcm qwit where [simp]: "\<Sigma>=(Q,W,rcm,qwit)" by (cases \<Sigma>) blast
  from A COND show ?thesis
    apply (simp add: brec_step_def fifo_correct)
    apply (case_tac "fifo_\<alpha> W")
    apply (simp 
      add: brec_invar_def distinct_tl brec_cond_def fifo_correct
    )
    apply (rule_tac s=W in fifo.removelE)
    apply simp
    apply simp
    apply simp

    apply (rule brw_inner_step_proof[
      OF ls.v1_iteratei_impl, 
      where cinvar="\<lambda>it \<Sigma>. \<Sigma>\<in>brec_invar_inner (hs_\<alpha> Qi)" and 
            q="hd (fifo_\<alpha> W)"])
    apply assumption
    apply (frule brec_brw_invar_cons)
    apply (simp_all 
      add: brec_cond_def brec_invar_add_def fifo_correct
            brec_invar_inner_def) [1]
    prefer 6
    apply (simp add: brec_\<alpha>_def)
    apply (case_tac \<Sigma>)
    apply (auto 
      simp add: brec_invar_add_def brec_inner_step_def Let_def hm_correct 
                hs_correct fifo_correct brec_invar_inner_def 
      split: option.split_asm) [1]
    apply (blast intro: brec_inner_step_brw_desc)
    apply (simp add: RQRM[unfolded rqrm_invar_def])
    apply (simp 
      add: rqrm_propD[OF RQRM(2)] fifo_correct)
    apply (simp_all 
      add: brec_\<alpha>_def brec_cond_def brec_invar_def fifo_correct) [1]
    apply (simp_all 
      add: brec_\<alpha>_def brec_cond_def brec_invar_add_def fifo_correct) [1]
    done
qed
    
lemma brec_invar_initial: 
  "\<lbrakk>ls_invar \<delta>; hs_invar Qi\<rbrakk> \<Longrightarrow> (brec_initial Qi \<delta>) \<in> brec_invar_add (hs_\<alpha> Qi)"
  apply (auto 
    simp add: brec_invar_add_def brec_initial_def brc_iq_correct 
              brec_iqm_correct' hs_correct hs.isEmpty_correct Let_def 
              brc_rcm_init_correct br_iq_def 
              hh_set_xx.disjoint_witness_correct 
              hs_to_fifo.g_set_to_listr_correct 
    split: option.split)
  apply (auto simp add: brc_iq_correct 
    hh_set_xx.disjoint_witness_None br_iq_def) [1]

  apply (drule hh_set_xx.disjoint_witness_correct[simplified])
  apply simp

  apply (drule hh_set_xx.disjoint_witness_correct[simplified])
  apply (simp add: brc_iq_correct br_iq_def)
  done

lemma brec_cond_abs: 
  "\<lbrakk>\<Sigma>\<in>brec_invar Qi \<delta>\<rbrakk> \<Longrightarrow> brec_cond \<Sigma> \<longleftrightarrow> (brec_\<alpha> \<Sigma>)\<in>brw_cond Qi"
  apply (cases \<Sigma>)
  apply (auto 
    simp add: brec_cond_def brw_cond_def brec_\<alpha>_def brec_invar_def 
              brec_invar_add_def fifo_correct
    split: option.split_asm)
  done

lemma brec_initial_abs: 
  "\<lbrakk> ls_invar \<delta>; hs_invar Qi \<rbrakk> 
     \<Longrightarrow> brec_\<alpha> (brec_initial Qi \<delta>) \<in> brw_initial (ls_\<alpha> \<delta>)"
  by (auto simp add: brec_initial_def Let_def brec_\<alpha>_def 
                     brc_iq_correct brc_rcm_init_correct brec_iqm_correct 
                     br_iq_def fifo_correct hs_to_fifo.g_set_to_listr_correct 
              intro: brw_initial.intros[unfolded br_iq_def])

lemma brec_pref_brw:
  assumes RQRM[simp]: "rqrm_invar rqrm" "rqrm_prop (ls_\<alpha> \<delta>) rqrm"
  assumes INV[simp]: "ls_invar \<delta>" "hs_invar Qi"
  shows "wa_precise_refine (det_wa_wa (brec_det_algo rqrm Qi \<delta>)) 
                           (brw_algo (hs_\<alpha> Qi) (ls_\<alpha> \<delta>))  
                           brec_\<alpha>"
  apply (unfold_locales)
  apply (simp_all add: det_wa_wa_def brec_det_algo_def brw_algo_def)
  apply (auto simp add: brec_cond_abs brec_step_abs brec_initial_abs)
  apply (simp add: brec_invar_def)
  done

lemma brec_while_algo:
  assumes RQRM[simp]: "rqrm_invar rqrm" "rqrm_prop (ls_\<alpha> \<delta>) rqrm"
  assumes INV[simp]: "ls_invar \<delta>" "hs_invar Qi"
  shows "while_algo (det_wa_wa (brec_det_algo rqrm Qi \<delta>))"
proof -
  interpret ref: 
    wa_precise_refine "(det_wa_wa (brec_det_algo rqrm Qi \<delta>))" 
                      "(brw_algo (hs_\<alpha> Qi) (ls_\<alpha> \<delta>))" 
                      "brec_\<alpha>" 
    using brec_pref_brw[OF RQRM INV] . 

  show ?thesis
    apply (rule ref.wa_intro)
    apply (simp add: brw_while_algo)
    apply (simp_all add: det_wa_wa_def brec_det_algo_def brw_algo_def)
    apply (simp add: brec_invar_def)
    apply (auto simp add: brec_step_invar[OF RQRM INV(2)]) [1]
    apply (simp add: brec_invar_initial) [1]
    done
qed

lemma fst_brec_\<alpha>: "fst (brec_\<alpha> \<Sigma>) = hm_\<alpha> (fst \<Sigma>)"
  by (cases \<Sigma>) (simp add: brec_\<alpha>_def)

lemmas brec_invar_final = 
  wa_precise_refine.transfer_correctness[
    OF brec_pref_brw brw_invar_final, 
    unfolded fst_brec_\<alpha>]

lemmas brec_det_algo = det_while_algo_intro[OF brec_while_algo]

definition "hta_is_empty_witness H == 
  let rqrm = build_rqrm (hta_\<delta> H);
      (Q,_,_,qwit) = (while brec_cond (brec_step rqrm (hta_Qi H)) 
                            (brec_initial (hta_Qi H) (hta_\<delta> H))) 
  in
    case qwit of 
      None \<Rightarrow> None |
      Some q \<Rightarrow> (hm_lookup q Q)
"

theorem (in hashedTa) hta_is_empty_witness_correct:
  shows [rule_format]: "hta_is_empty_witness H = Some t 
                        \<longrightarrow> t\<in>ta_lang (hta_\<alpha> H)" (is ?T1)
        "hta_is_empty_witness H = None \<longrightarrow> ta_lang (hta_\<alpha> H) = {}" (is ?T2)
proof -

  interpret det_while_algo "(brec_det_algo (build_rqrm \<delta>) Qi \<delta>)"
    by (rule brec_det_algo)
       (simp_all add: build_rqrm_correct)

  have LC: 
    "(while brec_cond (brec_step (build_rqrm \<delta>) Qi) (brec_initial Qi \<delta>)) = loop"
    by (unfold loop_def)
       (simp add: brec_det_algo_def)

  from while_proof'[OF brec_invar_final] have X:
    "hs_\<alpha> Qi \<inter> dom (hm_\<alpha> (fst loop)) = {} 
     \<longleftrightarrow> (hs_\<alpha> Qi \<inter> b_accessible (ls_\<alpha> \<delta>) = {})"
    "witness_prop (ls_\<alpha> \<delta>) (hm_\<alpha> (fst loop))"
    by (simp_all add: build_rqrm_correct)

  obtain Q W rcm qwit where 
    [simp]: "loop = (Q,W,rcm,qwit)" 
    by (case_tac "loop") blast

  from loop_invar have I: "loop \<in> brec_invar (hs_\<alpha> Qi) (ls_\<alpha> \<delta>)" 
    by (simp add: brec_det_algo_def)
  hence INVARS[simp]: "hm_invar Q" "hm_invar rcm" 
    by (simp_all add: brec_invar_def brec_invar_add_def) 
  
  {
    assume C: "hta_is_empty_witness H = Some t"
    then obtain q where 
      [simp]: "qwit=Some q" and 
        LUQ: "hm_lookup q Q = Some t"
      by (unfold hta_is_empty_witness_def)
         (simp add: LC split: option.split_asm)
    from LUQ have QqF: "hm_\<alpha> Q q = Some t" by (simp add: hm_correct)
    from I have QMEM: "q\<in>hs_\<alpha> Qi" 
      by (simp_all add: brec_invar_def brec_invar_add_def)
    moreover from witness_propD[OF X(2)] QqF have "accs (ls_\<alpha> \<delta>) t q" by simp
    ultimately have "t\<in>ta_lang (hta_\<alpha> H)"
      by (auto simp add: ta_lang_def hta_\<alpha>_def)
  } moreover {
    assume C: "hta_is_empty_witness H = None"
    hence DJ: "hs_\<alpha> Qi \<inter> dom (hm_\<alpha> Q) = {}" using I
      by (auto simp add: hta_is_empty_witness_def LC brec_invar_def 
                         brec_invar_add_def hm_correct 
               split: option.split_asm)
    with X have "hs_\<alpha> Qi \<inter> b_accessible (ls_\<alpha> \<delta>) = {}" 
      by (simp add: brec_\<alpha>_def)
    with empty_if_no_b_accessible[of "hta_\<alpha> H"] have "ta_lang (hta_\<alpha> H) = {}"
      by (simp add: hta_\<alpha>_def)
  } ultimately show ?T1 ?T2 by auto
qed

subsection \<open>Interface for Natural Number States and Symbols\<close>
  text_raw \<open>\label{sec:htai_intf}\<close>
text \<open>
  The library-interface is statically instantiated to use natural numbers 
  as both, states and symbols.

  This interface is easier to use from ML and OCaml, because there is no 
  overhead with typeclass emulation.
\<close>

type_synonym htai = "(nat,nat) hashedTa"

definition htai_mem :: "_ \<Rightarrow> htai \<Rightarrow> bool" 
  where "htai_mem == hta_mem"
definition htai_prod :: "htai \<Rightarrow> htai \<Rightarrow> htai" 
  where "htai_prod H1 H2 == hta_reindex (hta_prod H1 H2)"
definition htai_prodWR :: "htai \<Rightarrow> htai \<Rightarrow> htai" 
  where "htai_prodWR H1 H2 == hta_reindex (hta_prodWR H1 H2)"
definition htai_union :: "htai \<Rightarrow> htai \<Rightarrow> htai" 
  where "htai_union H1 H2 == hta_reindex (hta_union H1 H2)"
definition htai_empty :: "unit \<Rightarrow> htai"
  where "htai_empty == hta_empty"
definition htai_add_qi :: "_ \<Rightarrow> htai \<Rightarrow> htai" 
  where "htai_add_qi == hta_add_qi"
definition htai_add_rule :: "_ \<Rightarrow> htai \<Rightarrow> htai" 
  where "htai_add_rule == hta_add_rule"
definition htai_bwd_reduce :: "htai \<Rightarrow> htai" 
  where "htai_bwd_reduce == hta_bwd_reduce"
definition htai_is_empty_witness :: "htai \<Rightarrow> _" 
  where "htai_is_empty_witness == hta_is_empty_witness"
definition htai_ensure_idx_f :: "htai \<Rightarrow> htai" 
  where "htai_ensure_idx_f == hta_ensure_idx_f"
definition htai_ensure_idx_s :: "htai \<Rightarrow> htai" 
  where "htai_ensure_idx_s == hta_ensure_idx_s"
definition htai_ensure_idx_sf :: "htai \<Rightarrow> htai" 
  where "htai_ensure_idx_sf == hta_ensure_idx_sf"

definition htaip_prod :: "htai \<Rightarrow> htai \<Rightarrow> (nat * nat,nat) hashedTa" 
  where "htaip_prod == hta_prod"
definition htaip_prodWR :: "htai \<Rightarrow> htai \<Rightarrow> (nat * nat,nat) hashedTa" 
  where "htaip_prodWR == hta_prodWR"
definition htaip_reindex :: "(nat * nat,nat) hashedTa \<Rightarrow> htai" 
  where "htaip_reindex == hta_reindex"

locale htai = hashedTa +
  constrains H :: htai
begin
  lemmas htai_mem_correct = hta_mem_correct[folded htai_mem_def]

  lemma htai_empty_correct[simp]:
    "hta_\<alpha> (htai_empty ()) = ta_empty"
    "hashedTa (htai_empty ())"
  by (auto simp add: htai_empty_def hta_empty_correct)

  lemmas htai_add_qi_correct = hta_add_qi_correct[folded htai_add_qi_def]
  lemmas htai_add_rule_correct = hta_add_rule_correct[folded htai_add_rule_def]

  lemmas htai_bwd_reduce_correct = 
    hta_bwd_reduce_correct[folded htai_bwd_reduce_def]
  lemmas htai_is_empty_witness_correct = 
    hta_is_empty_witness_correct[folded htai_is_empty_witness_def]

  lemmas htai_ensure_idx_f_correct = 
    hta_ensure_idx_f_correct[folded htai_ensure_idx_f_def]
  lemmas htai_ensure_idx_s_correct = 
    hta_ensure_idx_s_correct[folded htai_ensure_idx_s_def]
  lemmas htai_ensure_idx_sf_correct = 
    hta_ensure_idx_sf_correct[folded htai_ensure_idx_sf_def]

end

lemma htai_prod_correct:
  assumes [simp]: "hashedTa H1" "hashedTa H2"
  shows 
  "ta_lang (hta_\<alpha> (htai_prod H1 H2)) = ta_lang (hta_\<alpha> H1) \<inter> ta_lang (hta_\<alpha> H2)"
  "hashedTa (htai_prod H1 H2)"
  apply (unfold htai_prod_def)
  apply (auto simp add: hta_prod_correct hashedTa.hta_reindex_correct)
  done

lemma htai_prodWR_correct:
  assumes [simp]: "hashedTa H1" "hashedTa H2"
  shows 
  "ta_lang (hta_\<alpha> (htai_prodWR H1 H2)) 
   = ta_lang (hta_\<alpha> H1) \<inter> ta_lang (hta_\<alpha> H2)"
  "hashedTa (htai_prodWR H1 H2)"
  apply (unfold htai_prodWR_def)
  apply (auto simp add: hta_prodWR_correct hashedTa.hta_reindex_correct)
  done

lemma htai_union_correct:
  assumes [simp]: "hashedTa H1" "hashedTa H2"
  shows 
  "ta_lang (hta_\<alpha> (htai_union H1 H2)) 
   = ta_lang (hta_\<alpha> H1) \<union> ta_lang (hta_\<alpha> H2)"
  "hashedTa (htai_union H1 H2)"
  apply (unfold htai_union_def)
  apply (auto simp add: hta_union_correct hashedTa.hta_reindex_correct)
  done

subsection \<open>Interface Documentation\<close> text_raw\<open>\label{sec:intf_doc}\<close>
text \<open>
  This section contains a documentation of the executable tree-automata
  interface. The documentation contains a description of each function along
  with the relevant correctness lemmas.
\<close>

text \<open>
  ML/OCaml users should note, that there is an interface that has the fixed type
  Int for both states and function symbols. This interface is simpler to use
  from ML/OCaml than the generic one, as it requires no overhead to emulate
  Isabelle/HOL type-classes.

  The functions of this interface start with the prefix {\em htai} instead of
  {\em hta}, but have the same semantics otherwise 
  (cf Section~\ref{sec:htai_intf}).
\<close>

subsubsection \<open>Building a Tree Automaton\<close>
text_raw \<open>
  \newcommand{\fundesc}[2]{{\bf Function: #1}\\#2}

\<close>

text \<open>
  \fundesc{@{const [show_types] hta_empty}}{
    Returns a tree automaton with no states and no rules. 
  }
  
  \paragraph{Relevant Lemmas}
  \begin{description}
    \item[@{thm [source] hta_empty_correct}:] @{thm hta_empty_correct[no_vars]}
    \item[@{thm [source] ta_empty_lang}:] @{thm ta_empty_lang[no_vars]}
  \end{description}
\<close>

text \<open>
  \fundesc{@{const [show_types] hta_add_qi}}{
    Adds an initial state to the given automaton.
  }
  \paragraph{Relevant Lemmas}
  \begin{description}
    \item[@{thm [source] hashedTa.hta_add_qi_correct}]
      @{thm hashedTa.hta_add_qi_correct[no_vars]}
  \end{description}
\<close>

text \<open>
  \fundesc{@{const [show_types] hta_add_rule}}{
    Adds a rule to the given automaton.
  }
  \paragraph{Relevant Lemmas}
  \begin{description}
    \item[@{thm [source] hashedTa.hta_add_rule_correct}:]
      @{thm hashedTa.hta_add_rule_correct[no_vars]}
  \end{description}
\<close>

subsubsection \<open>Basic Operations\<close>

text \<open>
  The tree automata of this library may have some optional indices, that 
  accelerate computation. The tree-automata operations will compute the 
  indices if necessary, but due to the pure nature of the Isabelle-language,
  the computed index cannot be stored for the next usage. Hence, before using a
  bulk of tree-automaton operations on the same tree-automata, the relevant 
  indexes should be pre-computed.
\<close>

text \<open>
  \fundesc{
    @{const [show_types] hta_ensure_idx_f}\\
    @{const [show_types] hta_ensure_idx_s}\\
    @{const [show_types] hta_ensure_idx_sf}
  }{
    Computes an index for a tree automaton, if it is not yet present.
  }
\<close>

text \<open>
  \fundesc{@{const [show_types] hta_mem}, @{const [show_types] hta_mem'}}{
    Check whether a tree is accepted by the tree automaton.
  }
  \paragraph{Relevant Lemmas}
  \begin{description}
    \item[@{thm [source] hashedTa.hta_mem_correct}:]
      @{thm hashedTa.hta_mem_correct[no_vars]}
    \item[@{thm [source] hashedTa.hta_mem'_correct}:]
      @{thm hashedTa.hta_mem'_correct[no_vars]}
  \end{description}
\<close>

text \<open>
  \fundesc{@{const [show_types] hta_prod}, @{const [show_types] hta_prod'}}{
    Compute the product automaton. The computed automaton is in 
    forward-reduced form. 
    The language of the product automaton is the intersection of 
    the languages of the two argument automata.
  }
  \paragraph{Relevant Lemmas}
  \begin{description}
    \item[@{thm [source] hta_prod_correct_aux}:] 
      @{thm hta_prod_correct_aux[no_vars]}
    \item[@{thm [source] hta_prod_correct}:] 
      @{thm hta_prod_correct[no_vars]}
    \item[@{thm [source] hta_prod'_correct_aux}:] 
      @{thm hta_prod'_correct_aux[no_vars]}
    \item[@{thm [source] hta_prod'_correct}:] 
      @{thm hta_prod'_correct[no_vars]}
  \end{description}
\<close>

text \<open>
  \fundesc{@{const [show_types] hta_prodWR}}{
    Compute the product automaton by brute-force algorithm. 
    The resulting automaton is not reduced.
    The language of the product automaton is the intersection of 
    the languages of the two argument automata.
  }
  \paragraph{Relevant Lemmas}
  \begin{description}
  \item[@{thm [source] hta_prodWR_correct_aux}:]
    @{thm hta_prodWR_correct_aux[no_vars]}
  \item[@{thm [source] hta_prodWR_correct}:] 
    @{thm hta_prodWR_correct[no_vars]}
  \end{description}
\<close>

text \<open>
  \fundesc{@{const [show_types] hta_union}}{
    Compute the union of two tree automata.
  }
  \paragraph{Relevant Lemmas}
  \begin{description}
  \item[@{thm [source] hta_union_correct'}:] @{thm hta_union_correct'[no_vars]}
  \item[@{thm [source] hta_union_correct}:] @{thm hta_union_correct[no_vars]}
  \end{description}
\<close>

text \<open>
  \fundesc{@{const [show_types] hta_reduce}}{
    Reduce the automaton to the given set of states. All initial states outside
    this set will be removed. Moreover, all rules that contain states outside 
    this set are removed, too.
  }
  \paragraph{Relevant Lemmas}
  \begin{description}
    \item[@{thm [source] hashedTa.hta_reduce_correct}:]
      @{thm hashedTa.hta_reduce_correct[no_vars]}
  \end{description}
\<close>

text \<open>
  \fundesc{@{const [show_types] hta_bwd_reduce}}{
    Compute the backwards-reduced version of a tree automata.
    States from that no tree can be produced are removed. 
    Backwards reduction does not change the language of the automaton.
  }
  \paragraph{Relevant Lemmas}
  \begin{description}
    \item[@{thm [source] hashedTa.hta_bwd_reduce_correct}:]
      @{thm hashedTa.hta_bwd_reduce_correct[no_vars]}
    \item[@{thm [source] ta_reduce_b_acc}:] @{thm ta_reduce_b_acc[no_vars]}
  \end{description}
\<close>

text \<open>
  \fundesc{@{const [show_types] hta_is_empty_witness}}{
    Check whether the language of the automaton is empty.
    If the language is not empty, a tree of the language is returned.

    The following property is not (yet) formally proven, but should hold: 
    If a tree is returned, the language contains no tree with a smaller depth
    than the returned one.
  }
  \paragraph{Relevant Lemmas}
  \begin{description}
    \item[@{thm [source] hashedTa.hta_is_empty_witness_correct}:]
       @{thm hashedTa.hta_is_empty_witness_correct[no_vars]}
  \end{description}
\<close>

subsection \<open>Code Generation\<close>

(* TODO/FIXME: There seems to be no way to reference the project-directory,
  in order to control the placement of the generated code files.
  The code-generation in this file only dumps the generated code to standard output.
  Hence it is safe to include this file from other projects.

  Actual code generation is done in Ta_impl_codegen.thy
  *)

export_code 
  hta_mem hta_mem' hta_prod hta_prod' hta_prodWR hta_union 
  hta_empty hta_add_qi hta_add_rule
  hta_reduce hta_bwd_reduce hta_is_empty_witness
  hta_ensure_idx_f hta_ensure_idx_s hta_ensure_idx_sf

  htai_mem htai_prod htai_prodWR htai_union 
  htai_empty htai_add_qi htai_add_rule
  htai_bwd_reduce htai_is_empty_witness
  htai_ensure_idx_f htai_ensure_idx_s htai_ensure_idx_sf

  (*ls_size hs_size rs_size*)
  in SML 
  module_name Ta


export_code 
  hta_mem hta_mem' hta_prod hta_prod' hta_prodWR hta_union 
  hta_empty hta_add_qi hta_add_rule
  hta_reduce hta_bwd_reduce hta_is_empty_witness
  hta_ensure_idx_f hta_ensure_idx_s hta_ensure_idx_sf

  htai_mem htai_prod htai_prodWR htai_union 
  htai_empty htai_add_qi htai_add_rule
  htai_bwd_reduce htai_is_empty_witness
  htai_ensure_idx_f htai_ensure_idx_s htai_ensure_idx_sf

  (*ls_size hs_size rs_size*)
  in Haskell 
  module_name Ta
  (string_classes)

export_code 
  hta_mem hta_mem' hta_prod hta_prod' hta_prodWR hta_union 
  hta_empty hta_add_qi hta_add_rule
  hta_reduce hta_bwd_reduce hta_is_empty_witness
  hta_ensure_idx_f hta_ensure_idx_s hta_ensure_idx_sf

  htai_mem htai_prod htai_prodWR htai_union 
  htai_empty htai_add_qi htai_add_rule
  htai_bwd_reduce htai_is_empty_witness
  htai_ensure_idx_f htai_ensure_idx_s htai_ensure_idx_sf

  (*ls_size hs_size rs_size*)
  in OCaml 
  module_name Ta

(* If this statement fails with an error from ML, this indicates a problem 
  with the code-generator. The most frequent problem in this context is, that
  the code generator generates code that violates the ML value-restriction.
*)

ML \<open>
  @{code hta_mem};
  @{code hta_mem'};
  @{code hta_prod};
  @{code hta_prod'};
  @{code hta_prodWR};
  @{code hta_union};
  @{code hta_empty};
  @{code hta_add_qi};
  @{code hta_add_rule};
  @{code hta_reduce};
  @{code hta_bwd_reduce};
  @{code hta_is_empty_witness};
  @{code hta_ensure_idx_f};
  @{code hta_ensure_idx_s};
  @{code hta_ensure_idx_sf};
  @{code htai_mem};
  @{code htai_prod};
  @{code htai_prodWR};
  @{code htai_union};
  @{code htai_empty};
  @{code htai_add_qi};
  @{code htai_add_rule};
  @{code htai_bwd_reduce};
  @{code htai_is_empty_witness};
  @{code htai_ensure_idx_f};
  @{code htai_ensure_idx_s};
  @{code htai_ensure_idx_sf};
  (*@{code ls_size};
  @{code hs_size};
  @{code rs_size}*)
\<close>

end
