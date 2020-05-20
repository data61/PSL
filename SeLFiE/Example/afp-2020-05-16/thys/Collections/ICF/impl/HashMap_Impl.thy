(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
section \<open>\isaheader{Hash maps implementation}\<close>
theory HashMap_Impl
imports 
  RBTMapImpl 
  ListMapImpl
  "../../Lib/HashCode"
  "../../Lib/Code_Target_ICF"
begin

text \<open>
  We use a red-black tree instead of an indexed array. This
  has the disadvantage of being more complex, however we need not bother
  about a fixed-size array and rehashing if the array becomes too full.

  The entries of the red-black tree are lists of (key,value) pairs.
\<close>

subsection \<open>Abstract Hashmap\<close>
text \<open>
  We first specify the behavior of our hashmap on the level of maps.
  We will then show that our implementation based on hashcode-map and bucket-map 
  is a correct implementation of this specification.
\<close>
type_synonym 
  ('k,'v) abs_hashmap = "hashcode \<rightharpoonup> ('k \<rightharpoonup> 'v)"

  \<comment> \<open>Map entry of map by function\<close>
abbreviation map_entry where "map_entry k f m == m(k := f (m k))"


  \<comment> \<open>Invariant: Buckets only contain entries with the right hashcode and there are no empty buckets\<close>
definition ahm_invar:: "('k::hashable,'v) abs_hashmap \<Rightarrow> bool" 
  where "ahm_invar m == 
    (\<forall>hc cm k. m hc = Some cm \<and> k\<in>dom cm \<longrightarrow> hashcode k = hc) \<and> 
    (\<forall>hc cm. m hc = Some cm \<longrightarrow> cm \<noteq> Map.empty)"



  \<comment> \<open>Abstract a hashmap to the corresponding map\<close>
definition ahm_\<alpha> where
  "ahm_\<alpha> m k == case m (hashcode k) of 
    None \<Rightarrow> None |
    Some cm \<Rightarrow> cm k"

  \<comment> \<open>Lookup an entry\<close>
definition ahm_lookup :: "'k::hashable \<Rightarrow> ('k,'v) abs_hashmap \<Rightarrow> 'v option" 
  where "ahm_lookup k m == (ahm_\<alpha> m) k"

  \<comment> \<open>The empty hashmap\<close>
definition ahm_empty :: "('k::hashable,'v) abs_hashmap" 
  where "ahm_empty = Map.empty"

  \<comment> \<open>Update/insert an entry\<close>
definition ahm_update where
  "ahm_update k v m ==
    case m (hashcode k) of
      None \<Rightarrow> m (hashcode k \<mapsto> [k \<mapsto> v]) |
      Some cm \<Rightarrow> m (hashcode k \<mapsto> cm (k \<mapsto> v))
  "

  \<comment> \<open>Delete an entry\<close>
definition ahm_delete where 
  "ahm_delete k m == map_entry (hashcode k) 
    (\<lambda>v. case v of 
      None \<Rightarrow> None | 
      Some bm \<Rightarrow> (
        if bm |` (- {k}) = Map.empty then
          None
        else
          Some ( bm |` (- {k}))
      )
    ) m
  "

definition ahm_isEmpty where
  "ahm_isEmpty m == m=Map.empty"

text \<open>
  Now follow correctness lemmas, that relate the hashmap operations to
  operations on the corresponding map. Those lemmas are named op\_correct, where
  (is) the operation.
\<close>

lemma ahm_invarI: "\<lbrakk> 
  !!hc cm k. \<lbrakk>m hc = Some cm; k\<in>dom cm\<rbrakk> \<Longrightarrow> hashcode k = hc;
  !!hc cm. \<lbrakk> m hc = Some cm \<rbrakk> \<Longrightarrow> cm \<noteq> Map.empty
  \<rbrakk> \<Longrightarrow> ahm_invar m"
  by (unfold ahm_invar_def) blast

lemma ahm_invarD: "\<lbrakk> ahm_invar m; m hc = Some cm; k\<in>dom cm \<rbrakk> \<Longrightarrow> hashcode k = hc"
  by (unfold ahm_invar_def) blast

lemma ahm_invarDne: "\<lbrakk> ahm_invar m; m hc = Some cm \<rbrakk> \<Longrightarrow> cm \<noteq> Map.empty"
  by (unfold ahm_invar_def) blast

lemma ahm_invar_bucket_not_empty[simp]: 
  "ahm_invar m \<Longrightarrow> m hc \<noteq> Some Map.empty"
  by (auto dest: ahm_invarDne)

lemmas ahm_lookup_correct = ahm_lookup_def

lemma ahm_empty_correct: 
  "ahm_\<alpha> ahm_empty = Map.empty"
  "ahm_invar ahm_empty"
  apply (rule ext)
  apply (unfold ahm_empty_def) 
  apply (auto simp add: ahm_\<alpha>_def intro: ahm_invarI split: option.split)
  done


lemma ahm_update_correct: 
  "ahm_\<alpha> (ahm_update k v m) = ahm_\<alpha> m (k \<mapsto> v)"
  "ahm_invar m \<Longrightarrow> ahm_invar (ahm_update k v m)"
  apply (rule ext)
  apply (unfold ahm_update_def)
  apply (auto simp add: ahm_\<alpha>_def split: option.split)
  apply (rule ahm_invarI)
  apply (auto dest: ahm_invarD ahm_invarDne split: if_split_asm)
  apply (rule ahm_invarI)
  apply (auto dest: ahm_invarD split: if_split_asm)
  apply (drule (1) ahm_invarD)
  apply auto
  done

lemma fun_upd_apply_ne: "x\<noteq>y \<Longrightarrow> (f(x:=v)) y = f y"
  by simp

lemma cancel_one_empty_simp: "m |` (-{k}) = Map.empty \<longleftrightarrow> dom m \<subseteq> {k}"
proof
  assume "m |` (- {k}) = Map.empty"
  hence "{} = dom (m |` (-{k}))" by auto
  also have "\<dots> = dom m - {k}" by auto
  finally show "dom m \<subseteq> {k}" by blast
next
  assume "dom m \<subseteq> {k}"
  hence "dom m - {k} = {}" by auto
  hence "dom (m |` (-{k})) = {}" by auto
  thus "m |` (-{k}) = Map.empty" by blast
qed
  
lemma ahm_delete_correct: 
  "ahm_\<alpha> (ahm_delete k m) = (ahm_\<alpha> m) |` (-{k})"
  "ahm_invar m \<Longrightarrow> ahm_invar (ahm_delete k m)"
  apply (rule ext)
  apply (unfold ahm_delete_def)
  apply (auto simp add: ahm_\<alpha>_def Let_def Map.restrict_map_def 
              split: option.split)[1]
  apply (drule_tac x=x in fun_cong)
  apply (auto)[1]
  apply (rule ahm_invarI)
  apply (auto split: if_split_asm option.split_asm dest: ahm_invarD)
  apply (drule (1) ahm_invarD)
  apply (auto simp add: restrict_map_def split: if_split_asm option.split_asm)
  done

lemma ahm_isEmpty_correct: "ahm_invar m \<Longrightarrow> ahm_isEmpty m \<longleftrightarrow> ahm_\<alpha> m = Map.empty"
proof
  assume "ahm_invar m" "ahm_isEmpty m"
  thus "ahm_\<alpha> m = Map.empty"
    by (auto simp add: ahm_isEmpty_def ahm_\<alpha>_def intro: ext)
next
  assume I: "ahm_invar m" 
    and E: "ahm_\<alpha> m = Map.empty"

  show "ahm_isEmpty m"
  proof (rule ccontr)
    assume "\<not>ahm_isEmpty m"
    then obtain hc bm where MHC: "m hc = Some bm"
      by (unfold ahm_isEmpty_def)
         (blast elim: nempty_dom dest: domD)
    from ahm_invarDne[OF I, OF MHC] obtain k v where
      BMK: "bm k = Some v"
      by (blast elim: nempty_dom dest: domD)
    from ahm_invarD[OF I, OF MHC] BMK have [simp]: "hashcode k = hc"
      by auto
    hence "ahm_\<alpha> m k = Some v"
      by (simp add: ahm_\<alpha>_def MHC BMK)
    with E show False by simp
  qed
qed

lemmas ahm_correct = ahm_empty_correct ahm_lookup_correct ahm_update_correct 
                     ahm_delete_correct ahm_isEmpty_correct

  \<comment> \<open>Bucket entries correspond to map entries\<close>
lemma ahm_be_is_e:
  assumes I: "ahm_invar m"
  assumes A: "m hc = Some bm" "bm k = Some v"
  shows "ahm_\<alpha> m k = Some v"
  using A
  apply (auto simp add: ahm_\<alpha>_def split: option.split dest: ahm_invarD[OF I])
  apply (frule ahm_invarD[OF I, where k=k])
  apply auto
  done

  \<comment> \<open>Map entries correspond to bucket entries\<close>
lemma ahm_e_is_be: "\<lbrakk>
  ahm_\<alpha> m k = Some v; 
  !!bm. \<lbrakk>m (hashcode k) = Some bm; bm k = Some v \<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
  by (unfold ahm_\<alpha>_def)
     (auto split: option.split_asm)

subsection \<open>Concrete Hashmap\<close>
text \<open>
  In this section, we define the concrete hashmap that is made from the 
  hashcode map and the bucket map.

  We then show the correctness of the operations w.r.t. the abstract hashmap, and
  thus, indirectly, w.r.t. the corresponding map.
\<close>

type_synonym
  ('k,'v) hm_impl = "(hashcode, ('k,'v) lm) rm"

subsubsection "Operations"

  \<comment> \<open>Auxiliary function: Apply function to value of an entry\<close>
definition rm_map_entry 
  :: "hashcode \<Rightarrow> ('v option \<Rightarrow> 'v option) \<Rightarrow> (hashcode, 'v) rm \<Rightarrow> (hashcode,'v) rm" 
  where 
  "rm_map_entry k f m ==
      case rm.lookup k m of
        None \<Rightarrow> (
          case f None of 
            None \<Rightarrow> m |
            Some v \<Rightarrow> rm.update k v m
        ) |
        Some v \<Rightarrow> (
          case f (Some v) of
            None \<Rightarrow> rm.delete k m |
            Some v' \<Rightarrow> rm.update k v' m
        )
    "

  \<comment> \<open>Empty hashmap\<close>
definition empty :: "unit \<Rightarrow> ('k :: hashable, 'v) hm_impl" where "empty == rm.empty"

  \<comment> \<open>Update/insert entry\<close>
definition update :: "'k::hashable \<Rightarrow> 'v \<Rightarrow> ('k,'v) hm_impl \<Rightarrow> ('k,'v) hm_impl"
  where 
  "update k v m == 
   let hc = hashcode k in
     case rm.lookup hc m of
       None \<Rightarrow> rm.update hc (lm.update k v (lm.empty ())) m |
       Some bm \<Rightarrow> rm.update hc (lm.update k v bm) m" 

  \<comment> \<open>Lookup value by key\<close>
definition lookup :: "'k::hashable \<Rightarrow> ('k,'v) hm_impl \<Rightarrow> 'v option" where
  "lookup k m ==
   case rm.lookup (hashcode k) m of
     None \<Rightarrow> None |
     Some lm \<Rightarrow> lm.lookup k lm"

  \<comment> \<open>Delete entry by key\<close>
definition delete :: "'k::hashable \<Rightarrow> ('k,'v) hm_impl \<Rightarrow> ('k,'v) hm_impl" where
  "delete k m ==
   rm_map_entry (hashcode k) 
     (\<lambda>v. case v of 
       None \<Rightarrow> None | 
       Some lm \<Rightarrow> (
         let lm' = lm.delete k lm 
         in  if lm.isEmpty lm' then None else Some lm'
       )
     ) m"

  \<comment> \<open>Emptiness check\<close>
definition "isEmpty == rm.isEmpty"

  \<comment> \<open>Interruptible iterator\<close>
definition "iteratei m c f \<sigma>0 ==
  rm.iteratei m c (\<lambda>(hc, lm) \<sigma>. 
    lm.iteratei lm c f \<sigma>
  ) \<sigma>0"

lemma iteratei_alt_def :
  "iteratei m = set_iterator_image snd (
     set_iterator_product (rm.iteratei m) (\<lambda>hclm. lm.iteratei (snd hclm)))"
proof -
  have aux: "\<And>c f. (\<lambda>(hc, lm). lm.iteratei lm c f) = (\<lambda>m. lm.iteratei (snd m) c f)"
    by auto
  show ?thesis
    unfolding set_iterator_product_def set_iterator_image_alt_def 
      iteratei_def[abs_def] aux
    by (simp add: split_beta)
qed


subsubsection "Correctness w.r.t. Abstract HashMap"
text \<open>
  The following lemmas establish the correctness of the operations w.r.t. the 
  abstract hashmap.

  They have the naming scheme op\_correct', where (is) the name of the 
  operation.
\<close>

  \<comment> \<open>Abstract concrete hashmap to abstract hashmap\<close>
definition hm_\<alpha>' where "hm_\<alpha>' m == \<lambda>hc. case rm.\<alpha> m hc of
  None \<Rightarrow> None |
  Some lm \<Rightarrow> Some (lm.\<alpha> lm)"

  \<comment> \<open>Invariant for concrete hashmap: 
    The hashcode-map and bucket-maps satisfy their invariants and
    the invariant of the corresponding abstract hashmap is satisfied.\<close>

definition "invar m == ahm_invar (hm_\<alpha>' m)"

lemma rm_map_entry_correct:
  "rm.\<alpha> (rm_map_entry k f m) = (rm.\<alpha> m)(k := f (rm.\<alpha> m k))"
  apply (auto 
    simp add: rm_map_entry_def rm.delete_correct rm.lookup_correct rm.update_correct 
    split: option.split)
  done

lemma empty_correct': 
  "hm_\<alpha>' (empty ()) = ahm_empty"
  "invar (empty ())"
  by (simp_all add: hm_\<alpha>'_def empty_def ahm_empty_def rm.correct invar_def ahm_invar_def)

lemma lookup_correct': 
  "invar m \<Longrightarrow> lookup k m = ahm_lookup k (hm_\<alpha>' m)"
  apply (unfold lookup_def invar_def)
  apply (auto split: option.split 
              simp add: ahm_lookup_def ahm_\<alpha>_def hm_\<alpha>'_def 
                        rm.correct lm.correct)
  done

lemma update_correct': 
  "invar m \<Longrightarrow> hm_\<alpha>' (update k v m) = ahm_update k v (hm_\<alpha>' m)"
  "invar m \<Longrightarrow> invar (update k v m)"
proof -
  assume "invar m"
  thus "hm_\<alpha>' (update k v m) = ahm_update k v (hm_\<alpha>' m)"
    apply (unfold invar_def)
    apply (rule ext)
    apply (auto simp add: update_def ahm_update_def hm_\<alpha>'_def Let_def 
                          rm.correct lm.correct 
                split: option.split)
    done
  thus "invar m \<Longrightarrow> invar (update k v m)"
    by (simp add: invar_def ahm_update_correct)
qed

lemma delete_correct':
  "invar m \<Longrightarrow> hm_\<alpha>' (delete k m) = ahm_delete k (hm_\<alpha>' m)"
  "invar m \<Longrightarrow> invar (delete k m)"
proof -
  assume "invar m"
  thus "hm_\<alpha>' (delete k m) = ahm_delete k (hm_\<alpha>' m)"
    apply (unfold invar_def)
    apply (rule ext)
    apply (auto simp add: delete_def ahm_delete_def hm_\<alpha>'_def 
                          rm_map_entry_correct
                          rm.correct lm.correct Let_def 
                split: option.split option.split_asm)
    done
  thus "invar (delete k m)" using \<open>invar m\<close>
    by (simp add: ahm_delete_correct invar_def)
qed

lemma isEmpty_correct':
  "invar hm \<Longrightarrow> isEmpty hm \<longleftrightarrow> ahm_\<alpha> (hm_\<alpha>' hm) = Map.empty"
apply (simp add: isEmpty_def rm.isEmpty_correct invar_def
                 ahm_isEmpty_correct[unfolded ahm_isEmpty_def, symmetric])
by (auto simp add: hm_\<alpha>'_def ahm_\<alpha>_def fun_eq_iff split: option.split_asm)

(*
lemma sel_correct':
  assumes "invar hm"
  shows "\<lbrakk> sel hm f = Some r; \<And>u v. \<lbrakk> ahm_\<alpha> (hm_\<alpha>' hm) u = Some v; f (u, v) = Some r \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  and "\<lbrakk> sel hm f = None; ahm_\<alpha> (hm_\<alpha>' hm) u = Some v \<rbrakk> \<Longrightarrow> f (u, v) = None"
proof -
  assume sel: "sel hm f = Some r"
    and P: "\<And>u v. \<lbrakk>ahm_\<alpha> (hm_\<alpha>' hm) u = Some v; f (u, v) = Some r\<rbrakk> \<Longrightarrow> P"
  from `invar hm` have IA: "ahm_invar (hm_\<alpha>' hm)" by(simp add: invar_def)
  from TrueI sel obtain hc lm where "rm_\<alpha> hm hc = Some lm"
    and "lm_sel lm f = Some r"
    unfolding sel_def by (rule rm.sel_someE) simp
  from TrueI `lm_sel lm f = Some r`
  obtain k v where "lm_\<alpha> lm k = Some v" "f (k, v) = Some r"
    by(rule lm.sel_someE)
  from `rm_\<alpha> hm hc = Some lm` have "hm_\<alpha>' hm hc = Some (lm_\<alpha> lm)"
    by(simp add: hm_\<alpha>'_def)
  with IA have "ahm_\<alpha> (hm_\<alpha>' hm) k = Some v" using `lm_\<alpha> lm k = Some v`
    by(rule ahm_be_is_e)
  thus P using `f (k, v) = Some r` by(rule P)
next
  assume sel: "sel hm f = None" 
    and \<alpha>: "ahm_\<alpha> (hm_\<alpha>' hm) u = Some v"
  from `invar hm` have IA: "ahm_invar (hm_\<alpha>' hm)" by(simp add: invar_def)
  from \<alpha> obtain lm where \<alpha>_u: "hm_\<alpha>' hm (hashcode u) = Some lm"
    and "lm u = Some v" by (rule ahm_e_is_be)
  from \<alpha>_u obtain lmc where "rm_\<alpha> hm (hashcode u) = Some lmc" "lm = lm_\<alpha> lmc" 
    by(auto simp add: hm_\<alpha>'_def split: option.split_asm)
  with `lm u = Some v` have "lm_\<alpha> lmc u = Some v" by simp
  from sel rm.sel_noneD [OF TrueI _ `rm_\<alpha> hm (hashcode u) = Some lmc`, 
         of "(\<lambda>(hc, lm). lm_sel lm f)"]
  have "lm_sel lmc f = None" unfolding sel_def by simp  
  with TrueI show "f (u, v) = None" using `lm_\<alpha> lmc u = Some v` by(rule lm.sel_noneD)
qed
*)

lemma iteratei_correct':
  assumes invar: "invar hm"
  shows "map_iterator (iteratei hm) (ahm_\<alpha> (hm_\<alpha>' hm))"
proof -
  from rm.iteratei_correct
  have it_rm: "map_iterator (rm.iteratei hm) (rm.\<alpha> hm)" by simp

  from lm.iteratei_correct
  have it_lm: "\<And>lm. map_iterator (lm.iteratei lm) (lm.\<alpha> lm)" by simp
 
  from set_iterator_product_correct 
    [OF it_rm, of "\<lambda>hclm. lm.iteratei (snd hclm)"
     "\<lambda>hclm. map_to_set (lm.\<alpha> (snd hclm))", OF it_lm]
  have it_prod: "set_iterator
         (set_iterator_product (rm.iteratei hm) (\<lambda>hclm. lm.iteratei (snd hclm)))
         (SIGMA hclm:map_to_set (rm.\<alpha> hm). map_to_set (lm.\<alpha> (snd hclm)))" 
    by simp
 
  show ?thesis unfolding iteratei_alt_def
  proof (rule set_iterator_image_correct[OF it_prod])
    from invar
    show "inj_on snd
       (SIGMA hclm:map_to_set (rm.\<alpha> hm). map_to_set (lm.\<alpha> (snd hclm)))"
      apply (simp add: inj_on_def invar_def ahm_invar_def hm_\<alpha>'_def Ball_def 
                       map_to_set_def split: option.splits)
      apply (metis domI option.inject)
    done
  next
    from invar
    show "map_to_set (ahm_\<alpha> (hm_\<alpha>' hm)) =
          snd ` (SIGMA hclm:map_to_set (rm.\<alpha> hm). map_to_set (lm.\<alpha> (snd hclm)))" 
      apply (simp add: inj_on_def invar_def ahm_invar_def hm_\<alpha>'_def Ball_def 
                       map_to_set_def set_eq_iff image_iff split: option.splits)
      apply (auto simp add: dom_def ahm_\<alpha>_def split: option.splits)
    done
  qed
qed


lemmas hm_correct' = empty_correct' lookup_correct' update_correct' 
                     delete_correct' isEmpty_correct' 
                     iteratei_correct'
lemmas hm_invars = empty_correct'(2) update_correct'(2) 
                   delete_correct'(2)

hide_const (open) empty invar lookup update delete isEmpty iteratei

end
