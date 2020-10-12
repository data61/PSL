(* Author: Andreas Lochbihler and Tobias Nipkow *)

section "Trie"

theory Trie
imports "HOL-Library.AList"
begin

(* A truly generic Trie would be parameterized by the data type for mappings
in each node. For this purpose the mapping type needs to become a bnf.

import "HOL-Library.Mapping"

lift_definition all_mapping :: "('b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) mapping \<Rightarrow> bool"
is "\<lambda>p m. \<forall>a b. m a = Some b \<longrightarrow> p b" .

lemma all_mapping_cong [fundef_cong]:
  "m = n \<Longrightarrow> (\<And>x y. Mapping.lookup n x = Some y \<Longrightarrow> p y = q y) \<Longrightarrow> all_mapping p m = all_mapping q n"
by transfer auto

lift_definition set_mapping :: "('a,'b)mapping \<Rightarrow> 'b set" is "\<lambda>f. Union(set_option ` range f)" .

lift_definition rel_mapping :: "('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('a,'b)mapping \<Rightarrow> ('a,'c)mapping \<Rightarrow> bool"
  is "\<lambda>r. rel_fun (=) (rel_option r)" .

bnf "('a,'b)mapping"
  map: "Mapping.map id"
  sets: set_mapping
  bd: "BNF_Cardinal_Arithmetic.csum (card_of (UNIV::'a set)) natLeq"
  wits: Mapping.empty
  rel: rel_mapping
proof-
  case goal1 show ?case by(rule Mapping.map.id)
next
  case goal2 show ?case by transfer (simp add: fun_eq_iff option.map_comp)
next
  case goal3 thus ?case by transfer (auto simp: fun_eq_iff intro: option.map_cong)
next
  case goal4 thus ?case by transfer (auto simp: fun_eq_iff)
next
  case goal5 thus ?case
    by (simp add: Field_card_of Field_natLeq card_of_card_order_on csum_def)
next
  case goal6 thus ?case
    by (simp add: cinfinite_csum natLeq_cinfinite)
next
  case goal7 thus ?case
    apply transfer
    apply(rule ordLeq_transitive[OF comp_single_set_bd[where fset=set_option and gset=range, of natLeq "BNF_Cardinal_Arithmetic.csum (card_of (UNIV::'d set)) natLeq"]])
    apply (rule natLeq_Card_order)
    apply(rename_tac opt)
    apply(case_tac opt)
    apply (simp add: card_of_empty1 natLeq_Well_order)
    using Card_order_singl_ordLeq Field_natLeq natLeq_Card_order apply fastforce
    apply(rule ordLeq_transitive[OF card_of_image])
    apply (simp add: card_of_Card_order ordLeq_csum1)
    apply(rule cprod_cinfinite_bound)
    apply(rule ordLeq_refl)
    apply (rule Card_order_csum)
    apply (simp add: natLeq_Card_order ordLeq_csum2)
    apply (rule Card_order_csum)
    apply (rule natLeq_Card_order)
    using Cinfinite_csum natLeq_Card_order natLeq_cinfinite by blast
next
  case goal8 thus ?case apply(rule predicate2I) apply transfer
    by(auto simp: option.rel_compp rel_fun_def)
next
  case goal9 show ?case
    unfolding OO_Grp_alt fun_eq_iff
    apply transfer
    apply safe
    apply(rename_tac f g)
    apply(rule_tac x = "\<lambda>x. case (f x, g x) of (Some u,Some v) \<Rightarrow> Some(u,v) | _ \<Rightarrow> None" in exI)
    apply(auto simp: fun_eq_iff rel_fun_def elim!: Option.option.rel_cases split: option.splits)
    apply (metis option.rel_inject(2))
    apply (metis rel_option_None1)
    apply(auto simp add: option.rel_map subset_eq intro!: rel_option_reflI split: prod.splits)
    done
next
  case goal10 thus ?case by transfer simp
qed
*)

datatype ('k, 'v) trie =
  Trie "'v option"  "('k * ('k,'v)trie) list"

lemma trie_induct [case_names Trie, induct type]:
  "(\<And>vo kvs. (\<And>k t. (k, t) \<in> set kvs \<Longrightarrow> P t) \<Longrightarrow> P (Trie vo kvs)) \<Longrightarrow> P t"
by induction_schema (pat_completeness, lexicographic_order)

definition empty_trie :: "('k, 'v) trie" where
"empty_trie = Trie None []"

fun is_empty_trie :: "('k, 'v) trie \<Rightarrow> bool" where
"is_empty_trie (Trie v m) = (v = None \<and> m = [])"

fun lookup_trie :: "('k, 'v) trie \<Rightarrow> 'k list \<Rightarrow> 'v option" where
"lookup_trie (Trie v m) [] = v" |
"lookup_trie (Trie v m) (k#ks) =
   (case map_of m k of
      None \<Rightarrow> None |
      Some st \<Rightarrow> lookup_trie st ks)"

fun update_with_trie ::
  "'k list \<Rightarrow> ('v option \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) trie \<Rightarrow> ('k, 'v) trie" where
"update_with_trie []     f (Trie v ps)  = Trie (Some(f v)) ps" |
"update_with_trie (k#ks) f (Trie v ps) =
  Trie v (AList.update_with_aux empty_trie k (update_with_trie ks f) ps)"

text\<open>The function argument \<open>f\<close> of @{const update_with_trie}
does not return an optional value because @{const None} could break the invariant
that no empty tries are contained in a trie because @{const AList.update_with_aux}
cannot recognise and remove empty tries.
Therefore the delete function is implemented separately rather than via
@{const update_with_trie}.

Do not use @{const update_with_trie} if most of the calls do not change
the entry (because of the garbage this creates); use @{const lookup_trie} possibly
followed by \<open>update_trie\<close>. This shortcoming could be addressed if
\<open>f\<close> indicated that the entry is unchanged, eg by @{const None}.\<close>

definition update_trie :: "'k list \<Rightarrow> 'v \<Rightarrow> ('k, 'v) trie \<Rightarrow> ('k, 'v) trie" where
"update_trie ks v = update_with_trie ks (%_. v)"

lemma update_trie_induct:
  "\<lbrakk>\<And>v ps. P [] (Trie v ps); \<And>k ks v ps. (\<And>x. P ks x) \<Longrightarrow> P (k#ks) (Trie v ps)\<rbrakk> \<Longrightarrow> P xs t"
by induction_schema (pat_completeness, lexicographic_order)

lemma update_trie_Nil[simp]: "update_trie [] v (Trie vo ts) = Trie (Some v) ts"
by(simp add: update_trie_def)

lemma update_trie_Cons[simp]: "update_trie (k#ks) v (Trie vo ts) =
  Trie vo (AList.update_with_aux (Trie None []) k (update_trie ks v) ts)"
by(simp add: update_trie_def empty_trie_def)

(* A simple implementation of delete; does not shrink the trie!
definition delete_trie :: "'k list \<Rightarrow> ('k, 'v) trie \<Rightarrow> ('k, 'v) trie" where
"delete_trie ks t = update_with_trie ks (\<lambda>_. None) t"
*)

fun delete_trie :: "'key list \<Rightarrow> ('key, 'val) trie \<Rightarrow> ('key, 'val) trie"
where
"delete_trie [] (Trie vo ts) = Trie None ts" |
"delete_trie (k#ks) (Trie vo ts) =
   (case map_of ts k of
      None \<Rightarrow> Trie vo ts |
      Some t \<Rightarrow> let t' = delete_trie ks t 
                in if is_empty_trie t'
                   then Trie vo (AList.delete_aux k ts)
                   else Trie vo (AList.update k t' ts))"

fun all_trie :: "('v \<Rightarrow> bool) \<Rightarrow> ('k, 'v) trie \<Rightarrow> bool" where
"all_trie p (Trie v ps) =
  ((case v of None \<Rightarrow> True | Some v \<Rightarrow> p v) \<and> (\<forall>(k,t) \<in> set ps. all_trie p t))"

fun invar_trie :: "('key, 'val) trie \<Rightarrow> bool" where
"invar_trie (Trie vo kts) =
  (distinct (map fst kts) \<and>
   (\<forall>(k, t) \<in> set kts. \<not> is_empty_trie t \<and> invar_trie t))"


subsection \<open>Empty trie\<close>

lemma invar_empty [simp]: "invar_trie empty_trie"
by(simp add: empty_trie_def)

lemma is_empty_conv: "is_empty_trie ts \<longleftrightarrow> ts = Trie None []"
by(cases ts)(simp)

subsection \<open>@{const lookup_trie}\<close>

lemma lookup_empty [simp]: "lookup_trie empty_trie = Map.empty"
proof
  fix ks show "lookup_trie empty_trie ks = Map.empty ks"
    by(cases ks)(auto simp add: empty_trie_def)
qed

lemma lookup_empty' [simp]: "lookup_trie (Trie None []) ks = None"
by(simp add: lookup_empty[unfolded empty_trie_def])

lemma lookup_update:
  "lookup_trie (update_trie ks v t) ks' = (if ks = ks' then Some v else lookup_trie t ks')"
proof(induct ks t arbitrary: ks' rule: update_trie_induct)
  case (1 vo ts ks')
  show ?case by(fastforce simp add: neq_Nil_conv dest: not_sym)
next
  case (2 k ks vo ts ks')
  show ?case by(cases ks')(auto simp add: map_of_update_with_aux 2 split: option.split)
qed

lemma lookup_update':
  "lookup_trie (update_trie ks v t) = (lookup_trie t)(ks \<mapsto> v)"
by(rule ext)(simp add: lookup_update)

lemma lookup_eq_Some_iff:
assumes invar: "invar_trie ((Trie vo kvs) :: ('key, 'val) trie)"
shows "lookup_trie (Trie vo kvs) ks = Some v \<longleftrightarrow>
    (ks = [] \<and> vo = Some v) \<or>
    (\<exists>k t ks'. ks = k # ks' \<and> 
        (k, t) \<in> set kvs \<and> lookup_trie t ks' = Some v)"
proof (cases ks)
  case Nil thus ?thesis by simp
next
  case (Cons k ks')
  note ks_eq[simp] = Cons
  show ?thesis
  proof (cases "map_of kvs k")
    case None thus ?thesis 
      apply (simp)
      apply (auto simp add: map_of_eq_None_iff image_iff Ball_def)
    done
  next
    case (Some t') note map_eq = this
    from invar have dist_kvs: "distinct (map fst kvs)" by simp

    from map_of_eq_Some_iff[OF dist_kvs, of k] map_eq
    show ?thesis by simp metis
  qed
qed

lemma lookup_eq_None_iff:
assumes invar: "invar_trie ((Trie vo kvs) :: ('key, 'val) trie)"
shows "lookup_trie (Trie vo kvs) ks = None \<longleftrightarrow>
    (ks = [] \<and> vo = None) \<or>
    (\<exists>k ks'. ks = k # ks' \<and> (\<forall>t. (k, t) \<in> set kvs \<longrightarrow> lookup_trie t ks' = None))"
using lookup_eq_Some_iff[of vo kvs ks, OF invar]
  apply (cases ks)
    apply auto[]
  apply (auto split: option.split)
    apply (metis option.simps(3) weak_map_of_SomeI)
    apply (metis option.exhaust)
    apply (metis option.exhaust)
done

lemma update_not_empty: "\<not> is_empty_trie (update_trie ks v t)"
apply(cases t)
apply(rename_tac kvs)
apply(cases ks)
apply(case_tac [2] kvs)
apply (auto)
done

lemma invar_trie_update: "invar_trie t \<Longrightarrow> invar_trie (update_trie ks v t)"
by(induct ks t rule: update_trie_induct)(auto simp add: set_update_with_aux update_not_empty split: option.splits)
 
lemma is_empty_lookup_empty:
  "invar_trie t \<Longrightarrow> is_empty_trie t \<longleftrightarrow> lookup_trie t = Map.empty"
proof(induct t)
  case (Trie vo kvs)
  thus ?case
    apply(cases kvs)
    apply(auto simp add: fun_eq_iff elim: allE[where x="[]"])
    apply(erule meta_allE)+
    apply(erule meta_impE)
    apply(rule disjI1)
    apply(fastforce intro: exI[where x="a # b" for a b])+
    done
qed

lemma lookup_update_with_trie:
  "lookup_trie (update_with_trie ks f t) ks' =
  (if ks' = ks then Some(f(lookup_trie t ks')) else lookup_trie t ks')"
proof(induction ks t arbitrary: ks' rule: update_trie_induct)
  case 1 thus ?case by(auto simp add: neq_Nil_conv)
next
  have *: "\<And>xs y ys. (xs \<noteq> y#ys) = (xs = [] \<or> (\<exists>x zs. xs = x#zs \<and> (x \<noteq> y \<or> zs \<noteq> ys)))"
    by auto (metis neq_Nil_conv)
  case 2
  thus ?case by(auto simp: * map_of_update_with_aux split: option.split)
qed

subsection \<open>@{const delete_trie}\<close>

lemma delete_eq_empty_lookup_other_fail:
  "\<lbrakk> delete_trie ks t = Trie None []; ks' \<noteq> ks \<rbrakk> \<Longrightarrow> lookup_trie t ks' = None"
proof(induct ks t arbitrary: ks' rule: delete_trie.induct)
  case 1 thus ?case by(auto simp add: neq_Nil_conv)
next
  case (2 k ks vo ts)
  show ?case
  proof(cases "map_of ts k")
    case (Some t)
    show ?thesis
    proof(cases ks')
      case (Cons k' ks'')
      show ?thesis
      proof(cases "k' = k")
        case False
        from Some Cons "2.prems"(1) have "AList.delete_aux k ts = []"
          by(clarsimp simp add: Let_def split: if_split_asm)
        with False have "map_of ts k' = None"
          by(cases "map_of ts k'")(auto dest: map_of_SomeD simp add: delete_aux_eq_Nil_conv)
        thus ?thesis using False Some Cons "2.prems"(1) by simp
      next
        case True
        with Some "2.prems" Cons show ?thesis
          by(clarsimp simp add: "2.hyps" Let_def is_empty_conv split: if_split_asm)
      qed
    qed(insert Some "2.prems"(1), simp add: Let_def split: if_split_asm)
  next
    case None thus ?thesis using "2.prems"(1) by simp
  qed
qed

lemma lookup_delete: "invar_trie t \<Longrightarrow>
  lookup_trie (delete_trie ks t) ks' =
  (if ks = ks' then None else lookup_trie t ks')"
proof(induct ks t arbitrary: ks' rule: delete_trie.induct)
  case 1 show ?case by(fastforce dest: not_sym simp add: neq_Nil_conv)
next
  case (2 k ks vo ts)
  show ?case
  proof(cases ks')
    case Nil thus ?thesis by(simp split: option.split add: Let_def)
  next
    case [simp]: (Cons k' ks'')
    show ?thesis
    proof(cases "k' = k")
      case False thus ?thesis using "2.prems"
        by(auto simp add: Let_def update_conv' map_of_delete_aux split: option.split)
    next
      case [simp]: True
      show ?thesis
      proof(cases "map_of ts k")
        case None thus ?thesis by simp
      next
        case (Some t)
        thus ?thesis 
        proof(cases "is_empty_trie (delete_trie ks t)")
          case True
          with Some "2.prems" show ?thesis
            by(auto simp add: map_of_delete_aux is_empty_conv dest: delete_eq_empty_lookup_other_fail)
        next
          case False
          thus ?thesis using Some 2 by(auto simp add: update_conv')
        qed
      qed
    qed
  qed
qed

lemma lookup_delete':
  "invar_trie t \<Longrightarrow> lookup_trie (delete_trie ks t) = (lookup_trie t)(ks := None)"
by(rule ext)(simp add: lookup_delete)

lemma invar_trie_delete:
  "invar_trie t \<Longrightarrow> invar_trie (delete_trie ks t)"
proof(induct ks t rule: delete_trie.induct)
  case 1 thus ?case by simp
next
  case (2 k ks vo ts)
  show ?case
  proof(cases "map_of ts k")
    case None
    thus ?thesis using "2.prems" by simp
  next
    case (Some t)
    with "2.prems" have "invar_trie t" by auto
    with Some have "invar_trie (delete_trie ks t)" by(rule 2)
    from "2.prems" Some have distinct: "distinct (map fst ts)" "\<not> is_empty_trie t" by auto
    show ?thesis
    proof(cases "is_empty_trie (delete_trie ks t)")
      case True
      { fix k' t'
        assume k't': "(k', t') \<in> set (AList.delete_aux k ts)"
        with distinct have "map_of (AList.delete_aux k ts) k' = Some t'" by simp
        hence "map_of ts k' = Some t'" using distinct
          by (auto 
            simp del: map_of_eq_Some_iff
            simp add: map_of_delete_aux 
            split: if_split_asm)
        with "2.prems" have "\<not> is_empty_trie t' \<and> invar_trie t'" by auto }
      with "2.prems" have "invar_trie (Trie vo (AList.delete_aux k ts))" by auto
      thus ?thesis using True Some by(simp)
    next
      case False
      { fix k' t'
        assume k't':"(k', t') \<in> set (AList.update k (delete_trie ks t) ts)"
        hence "map_of (AList.update k (delete_trie ks t) ts) k' = Some t'"
          using "2.prems" by(auto simp add: distinct_update)
        hence eq: "((map_of ts)(k \<mapsto> delete_trie ks t)) k' = Some t'" unfolding update_conv .
        have "\<not> is_empty_trie t' \<and> invar_trie t'"
        proof(cases "k' = k")
          case True
          with eq have "t' = delete_trie ks t" by simp
          with \<open>invar_trie (delete_trie ks t)\<close> False
          show ?thesis by simp
        next
          case False
          with eq distinct have "(k', t') \<in> set ts" by simp
          with "2.prems" show ?thesis by auto
        qed }
      thus ?thesis using Some "2.prems" False by(auto simp add: distinct_update)
    qed
  qed
qed


subsection \<open>@{const update_with_trie}\<close>

(* FIXME mv *)
lemma nonempty_update_with_aux: "AList.update_with_aux v k f ps \<noteq> []"
by (induction ps) auto

lemma nonempty_update_with_trie: "\<not> is_empty_trie (update_with_trie ks f t)"
by(induction ks t rule: update_trie_induct)
  (auto simp: nonempty_update_with_aux)

lemma invar_update_with_trie:
  "invar_trie t \<Longrightarrow> invar_trie (update_with_trie ks f t)"
by(induction ks f t rule: update_with_trie.induct)
  (auto simp: set_update_with_aux nonempty_update_with_trie
     split: option.split prod.splits)


subsection \<open>Domain of a trie\<close>

lemma dom_lookup: 
  "dom (lookup_trie (Trie vo kts)) = 
  (\<Union>k\<in>dom (map_of kts). Cons k ` dom (lookup_trie (the (map_of kts k)))) \<union>
  (if vo = None then {} else {[]})"
unfolding dom_def
apply(rule sym)
apply(safe)
  apply simp
 apply(clarsimp simp add: if_split_asm)
apply(case_tac x)
apply(auto split: option.split_asm)
done

lemma finite_dom_lookup:
  "finite (dom (lookup_trie t))"
proof(induct t)
  case (Trie vo kts)
  have "finite (\<Union>k\<in>dom (map_of kts). Cons k ` dom (lookup_trie (the (map_of kts k))))"
  proof(rule finite_UN_I)
    show "finite (dom (map_of kts))" by(rule finite_dom_map_of)
  next
    fix k
    assume "k \<in> dom (map_of kts)"
    then obtain v where "(k, v) \<in> set kts" "map_of kts k = Some v" by(auto dest: map_of_SomeD)
    hence "finite (dom (lookup_trie (the (map_of kts k))))" by simp(rule Trie)
    thus "finite (Cons k ` dom (lookup_trie (the (map_of kts k))))" by(rule finite_imageI)
  qed
  thus ?case by(simp add: dom_lookup)
qed

lemma dom_lookup_empty_conv: "invar_trie t \<Longrightarrow> dom (lookup_trie t) = {} \<longleftrightarrow> is_empty_trie t"
proof(induct t)
  case (Trie vo kvs)
  show ?case
  proof
    assume dom: "dom (lookup_trie (Trie vo kvs)) = {}"
    have "vo = None"
    proof(cases vo)
      case (Some v)
      hence "[] \<in> dom (lookup_trie (Trie vo kvs))" by auto
      with dom have False by simp
      thus ?thesis ..
    qed
    moreover have "kvs = []"
    proof(cases kvs)
      case (Cons kt kvs')
      with \<open>invar_trie (Trie vo kvs)\<close>
      have "\<not> is_empty_trie (snd kt)" "invar_trie (snd kt)" by auto
      from Cons have "(fst kt, snd kt) \<in> set kvs" by simp
      hence "dom (lookup_trie (snd kt)) = {} \<longleftrightarrow> is_empty_trie (snd kt)"
        using \<open>invar_trie (snd kt)\<close> by(rule Trie)
      with \<open>\<not> is_empty_trie (snd kt)\<close> have "dom (lookup_trie (snd kt)) \<noteq> {}" by simp
      with dom Cons have False by(auto simp add: dom_lookup)
      thus ?thesis ..
    qed
    ultimately show "is_empty_trie (Trie vo kvs)" by simp
  next
    assume "is_empty_trie (Trie vo kvs)"
    thus "dom (lookup_trie (Trie vo kvs)) = {}"
      by(simp add: lookup_empty[unfolded empty_trie_def])
  qed
qed


subsection \<open>Range of a trie\<close>

lemma ran_lookup_Trie: "invar_trie (Trie vo ps) \<Longrightarrow>
  ran (lookup_trie (Trie vo ps)) =
  (case vo of None \<Rightarrow> {} | Some v \<Rightarrow> {v}) \<union> (UN (k,t) : set ps. ran(lookup_trie t))"
by(auto simp add: ran_def lookup_eq_Some_iff split: prod.splits option.split)

lemma all_trie_eq_ran:
  "invar_trie t \<Longrightarrow> all_trie P t = (\<forall>x \<in> ran(lookup_trie t). P x)"
by(induction P t rule: all_trie.induct)
  (auto simp add: ran_lookup_Trie split: prod.splits option.split)

end
