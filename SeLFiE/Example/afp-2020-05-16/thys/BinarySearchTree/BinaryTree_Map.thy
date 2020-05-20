(*  Title:       Binary Search Trees, Isar-Style
    Author:      Viktor Kuncak, MIT CSAIL, November 2003
    Maintainer:  Larry Paulson <Larry.Paulson at cl.cam.ac.uk>
    License:     LGPL
*)

section \<open>Mostly Isar-style Reasoning for Binary Tree Operations\<close>
theory BinaryTree_Map imports BinaryTree begin

text \<open>We prove correctness of map operations
 implemented using binary search trees from BinaryTree.

 This document is LGPL.

 Author: Viktor Kuncak, MIT CSAIL, November 2003\<close>


(*============================================================*)
section \<open>Map implementation and an abstraction function\<close>
(*============================================================*)

type_synonym 
  'a tarray = "(index * 'a) Tree"

definition valid_tmap :: "'a tarray => bool" where
  "valid_tmap t == sortedTree fst t"

declare valid_tmap_def [simp]

definition mapOf :: "'a tarray => index => 'a option" where
  \<comment> \<open>the abstraction function from trees to maps\<close>
  "mapOf t i == 
   (case (tlookup fst i t) of
     None => None
   | Some ia => Some (snd ia))"

(*============================================================*)
section \<open>Auxiliary Properties of our Implementation\<close>
(*============================================================*)

lemma mapOf_lookup1: "tlookup fst i t = None ==> mapOf t i = None"
by (simp add: mapOf_def)

lemma mapOf_lookup2: "tlookup fst i t = Some (j,a) ==> mapOf t i = Some a"
by (simp add: mapOf_def)

lemma assumes h: "mapOf t i = None"
      shows mapOf_lookup3: "tlookup fst i t = None"
proof (cases "tlookup fst i t")
case None from this show ?thesis by assumption
next case (Some ia) note tsome = this
  from this have o1: "tlookup fst i t = Some (fst ia, snd ia)" by simp
  have "mapOf t i = Some (snd ia)"
  by (insert mapOf_lookup2 [of i t "fst ia" "snd ia"], simp add: o1)
  from this have "mapOf t i ~= None" by simp
  from this h show ?thesis by simp \<comment> \<open>contradiction\<close>
qed

lemma assumes v: "valid_tmap t"
      assumes h: "mapOf t i = Some a"
      shows mapOf_lookup4: "tlookup fst i t = Some (i,a)"
proof (cases "tlookup fst i t")
case None 
  from this mapOf_lookup1 have "mapOf t i = None" by auto
  from this h show ?thesis by simp \<comment> \<open>contradiction\<close>
next case (Some ia) note tsome = this
  have tlookup_some_inst: "sortedTree fst t & (tlookup fst i t = Some ia) --> 
        ia : setOf t & fst ia = i" by (simp add: tlookup_some)
  from tlookup_some_inst tsome v have "ia : setOf t" by simp
  from tsome have "mapOf t i = Some (snd ia)" by (simp add: mapOf_def)
  from this h have o1: "snd ia = a" by simp
  from tlookup_some_inst tsome v have o2: "fst ia = i" by simp
  from o1 o2 have "ia = (i,a)" by auto
  from this tsome show "tlookup fst i t = Some (i, a)" by simp
qed

subsection \<open>Lemmas \<open>mapset_none\<close> and \<open>mapset_some\<close> establish 
              a relation between the set and map abstraction of the tree\<close>

lemma assumes v: "valid_tmap t"
      shows mapset_none: "(mapOf t i = None) = (\<forall>a. (i,a) \<notin> setOf t)"
proof
  \<comment> \<open>==>\<close>
  assume mapNone: "mapOf t i = None"
  from v mapNone mapOf_lookup3 have lnone: "tlookup fst i t = None" by auto
  show "\<forall>a. (i,a) \<notin> setOf t"
  proof
    fix a
    show "(i,a) ~: setOf t"
    proof
      assume iain: "(i,a) : setOf t"
      have tlookup_none_inst: 
      "sortedTree fst t & (tlookup fst i t = None) --> (\<forall>x \<in> setOf t. fst x ~= i)"
      by (insert tlookup_none [of "fst" "t" "i"], assumption)
      from v lnone tlookup_none_inst have "\<forall>x \<in> setOf t. fst x ~= i" by simp
      from this iain have "fst (i,a) ~= i" by fastforce
      from this show False by simp
    qed
  qed
  \<comment> \<open><==\<close>
  next assume h: "\<forall>a. (i,a) \<notin> setOf t"
  show "mapOf t i = None"
  proof (cases "mapOf t i")
  case None then show ?thesis .
  next case (Some a) note mapsome = this
    from v mapsome have o1: "tlookup fst i t = Some (i,a)" by (simp add: mapOf_lookup4)
    (* moving mapOf_lookup4 to assumption does not work, although it uses
       no == !! *)
    from tlookup_some have tlookup_some_inst:
    "sortedTree fst t & tlookup fst i t = Some (i,a) --> 
     (i,a) : setOf t & fst (i,a) = i"
    by (insert tlookup_some [of fst t i "(i,a)"], assumption)   
    from v o1 this have "(i,a) : setOf t" by simp
    from this h show ?thesis by auto \<comment> \<open>contradiction\<close>
  qed
qed

lemma assumes v: "valid_tmap t"
      shows mapset_some: "(mapOf t i = Some a) = ((i,a) : setOf t)"
proof
  \<comment> \<open>==>\<close>
  assume mapsome: "mapOf t i = Some a"
  from v mapsome have o1: "tlookup fst i t = Some (i,a)" by (simp add: mapOf_lookup4)
  from tlookup_some have tlookup_some_inst:
  "sortedTree fst t & tlookup fst i t = Some (i,a) --> 
   (i,a) : setOf t & fst (i,a) = i"
  by (insert tlookup_some [of fst t i "(i,a)"], assumption)   
  from v o1 this show "(i,a) : setOf t" by simp
  \<comment> \<open><==\<close>
  next assume iain: "(i,a) : setOf t"
  from v iain tlookup_finds have "tlookup fst (fst (i,a)) t = Some (i,a)" by fastforce
  from this have "tlookup fst i t = Some (i,a)" by simp
  from this show "mapOf t i = Some a" by (simp add: mapOf_def)
qed

(*============================================================*)
section \<open>Empty Map\<close>
(*============================================================*)

lemma mnew_spec_valid: "valid_tmap Tip"
by (simp add: mapOf_def)

lemma mtip_spec_empty: "mapOf Tip k = None"
by (simp add: mapOf_def)


(*============================================================*)
section \<open>Map Update Operation\<close>
(*============================================================*)

definition mupdate :: "index => 'a => 'a tarray => 'a tarray" where
  "mupdate i a t == binsert fst (i,a) t"

lemma assumes v: "valid_tmap t"
      shows mupdate_map: "mapOf (mupdate i a t) = (mapOf t)(i |-> a)"
proof
  fix i2
  let ?tr = "binsert fst (i,a) t"
  have upres: "mupdate i a t = ?tr" by (simp add: mupdate_def)
  from v binsert_set 
  have setSpec: "setOf ?tr = setOf t - eqs fst (i,a) Un {(i,a)}" by fastforce
  from v binsert_sorted have vr: "valid_tmap ?tr" by fastforce
  show "mapOf (mupdate i a t) i2 = ((mapOf t)(i |-> a)) i2"
  proof (cases "i = i2")
  case True note i2ei = this
    from i2ei have rhs_res: "((mapOf t)(i |-> a)) i2 = Some a" by simp
    have lhs_res: "mapOf (mupdate i a t) i = Some a"
    proof -
      have will_find: "tlookup fst i ?tr = Some (i,a)"
      proof -
        from setSpec have kvin: "(i,a) : setOf ?tr" by simp
        have binsert_sorted_inst: "sortedTree fst t --> 
                                 sortedTree fst ?tr"
        by (insert binsert_sorted [of "fst" "t" "(i,a)"], assumption)
        from v binsert_sorted_inst have rs: "sortedTree fst ?tr" by simp
        have tlookup_finds_inst: "sortedTree fst ?tr & (i,a) : setOf ?tr --> 
                                  tlookup fst i ?tr = Some (i,a)"
        by (insert tlookup_finds [of "fst" "?tr" "(i,a)"], simp)
        from rs kvin tlookup_finds_inst show ?thesis by simp
      qed
      from upres will_find show ?thesis by (simp add: mapOf_def)
    qed
    from lhs_res rhs_res i2ei show ?thesis by simp
  next case False note i2nei = this
    from i2nei have rhs_res: "((mapOf t)(i |-> a)) i2 = mapOf t i2" by auto
    have lhs_res: "mapOf (mupdate i a t) i2 = mapOf t i2"
    proof (cases "mapOf t i2")
    case None from this have mapNone: "mapOf t i2 = None" by simp
      from v mapNone mapset_none have i2nin: "\<forall>a. (i2,a) \<notin> setOf t" by fastforce
      have noneIn: "\<forall>b. (i2,b) \<notin> setOf ?tr"
      proof 
        fix b 
        from v binsert_set 
        have "setOf ?tr = setOf t - eqs fst (i,a) Un {(i,a)}"
        by fastforce
        from this i2nei i2nin show "(i2,b) ~: setOf ?tr" by fastforce
      qed
      have mapset_none_inst: 
      "valid_tmap ?tr --> (mapOf ?tr i2 = None) = (\<forall>a. (i2, a) \<notin> setOf ?tr)" 
      by (insert mapset_none [of "?tr" i2], simp)
      from vr noneIn mapset_none_inst have "mapOf ?tr i2 = None" by fastforce
      from this upres mapNone show ?thesis by simp
    next case (Some z) from this have mapSome: "mapOf t i2 = Some z" by simp
      from v mapSome mapset_some have "(i2,z) : setOf t" by fastforce
      from this setSpec i2nei have "(i2,z) : setOf ?tr" by (simp add: eqs_def)
      from this vr mapset_some have "mapOf ?tr i2 = Some z" by fastforce
      from this upres mapSome show ?thesis by simp
    qed
    from lhs_res rhs_res show ?thesis by simp
  qed
qed

lemma assumes v: "valid_tmap t"
      shows mupdate_valid: "valid_tmap (mupdate i a t)"
proof -
  let ?tr = "binsert fst (i,a) t"
  have upres: "mupdate i a t = ?tr" by (simp add: mupdate_def)
  from v binsert_sorted have vr: "valid_tmap ?tr" by fastforce
  from vr upres show ?thesis by simp
qed

(*============================================================*)
section \<open>Map Remove Operation\<close>
(*============================================================*)

definition mremove :: "index => 'a tarray => 'a tarray" where
  "mremove i t == remove fst (i, undefined) t"

lemma assumes v: "valid_tmap t"
      shows mremove_valid: "valid_tmap (mremove i t)"
proof (simp add: mremove_def)
  from v remove_sort 
  show "sortedTree fst (remove fst (i, undefined) t)" by fastforce
qed

lemma assumes v: "valid_tmap t"
      shows mremove_map: "mapOf (mremove i t) i = None"
proof (simp add: mremove_def)
  let ?tr = "remove fst (i, undefined) t"
  show "mapOf ?tr i = None"
  proof -
    from v remove_spec 
    have remSet: "setOf ?tr = setOf t - eqs fst (i, undefined)"
    by fastforce
    have noneIn: "\<forall>a. (i,a) \<notin> setOf ?tr"
    proof 
      fix a
      from remSet show "(i,a) ~: setOf ?tr" by (simp add: eqs_def)
    qed
    from v remove_sort have vr: "valid_tmap ?tr" by fastforce
    have mapset_none_inst: "valid_tmap ?tr ==>
    (mapOf ?tr i = None) = (\<forall>a. (i,a) \<notin> setOf ?tr)"
    by (insert mapset_none [of "?tr" "i"], simp)
    from vr this have "(mapOf ?tr i = None) = (\<forall>a. (i,a) \<notin> setOf ?tr)" by fastforce
    from this noneIn show "mapOf ?tr i = None" by simp    
  qed
qed

end
