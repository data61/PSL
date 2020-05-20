section\<open>Imparative implementation for Pointermap\<close>
theory Pointer_Map_Impl
imports Array_List 
  Separation_Logic_Imperative_HOL.Sep_Main
  Separation_Logic_Imperative_HOL.Hash_Map_Impl
  Pointer_Map
begin

  record 'a pointermap_impl =
    entriesi :: "'a array_list"
    getentryi :: "('a,nat) hashtable"
  lemma pointermapieq_exhaust: "entries a = entries b \<Longrightarrow> getentry a = getentry b \<Longrightarrow> a = (b :: 'a pointermap)" by simp

  definition is_pointermap_impl :: "('a::{hashable,heap}) pointermap \<Rightarrow> 'a pointermap_impl \<Rightarrow> assn" where
    "is_pointermap_impl b bi \<equiv> 
      is_array_list (entries b) (entriesi bi) 
    * is_hashmap (getentry b) (getentryi bi)"

  lemma is_pointermap_impl_prec: "precise is_pointermap_impl"
    unfolding is_pointermap_impl_def[abs_def]
  apply(rule preciseI)
  apply(clarsimp)
  apply(rename_tac a a' x y p F F')
  apply(rule pointermapieq_exhaust)
   apply(rule_tac p = "entriesi p" and h = "(x,y)" in preciseD[OF is_array_list_prec])
   apply(unfold star_aci(1))
   apply blast
  apply(rule_tac p = "getentryi p" and h = "(x,y)" in preciseD[OF is_hashmap_prec])
  apply(simp only: star_aci(2)[symmetric])
  apply(simp only: star_aci(1)[symmetric]) (* black unfold magic *)
  apply(simp only: star_aci(2)[symmetric])
  done

  definition pointermap_empty where
    "pointermap_empty \<equiv> do {
      hm \<leftarrow> hm_new;
      arl \<leftarrow> arl_empty;
      return \<lparr>entriesi = arl, getentryi = hm \<rparr>
    }"

  lemma [sep_heap_rules]: "< emp > pointermap_empty <is_pointermap_impl empty_pointermap>\<^sub>t"
    unfolding is_pointermap_impl_def
    by (sep_auto simp: pointermap_empty_def empty_pointermap_def)

  definition pm_pthi where
    "pm_pthi m p \<equiv> arl_nth (entriesi m) p"

  lemma [sep_heap_rules]: "pointermap_sane m \<Longrightarrow> pointermap_p_valid p m \<Longrightarrow>
    < is_pointermap_impl m mi > pm_pthi mi p <\<lambda>ai. is_pointermap_impl m mi * \<up>(ai = pm_pth m p)>"
    by (sep_auto simp: pm_pthi_def pm_pth_def is_pointermap_impl_def pointermap_p_valid_def)

  definition pointermap_getmki where
    "pointermap_getmki a m \<equiv> do {
        lo \<leftarrow> ht_lookup a (getentryi m);
        (case lo of 
          Some l \<Rightarrow> return (l,m) | 
          None \<Rightarrow> do {
            p \<leftarrow> return (snd (entriesi m));
        ent \<leftarrow> arl_append (entriesi m) a;
        lut \<leftarrow> hm_update a p (getentryi m);
        u \<leftarrow> return \<lparr>entriesi = ent, getentryi = lut\<rparr>;
        return (p,u)
          }
        )
    }"

  lemmas pointermap_getmki_defs = pointermap_getmki_def pointermap_getmk_def pointermap_insert_def is_pointermap_impl_def
  lemma [sep_heap_rules]: "pointermap_sane m \<Longrightarrow> pointermap_getmk a m = (p,u) \<Longrightarrow>
    < is_pointermap_impl m mi >
      pointermap_getmki a mi
    <\<lambda>(pi,ui). is_pointermap_impl u ui * \<up>(pi = p)>\<^sub>t"
  apply(cases "getentry m a")
   apply(unfold pointermap_getmki_def)
   apply(unfold return_bind)
   apply(rule bind_rule[where R = "\<lambda>r. is_pointermap_impl m mi * \<up>(r = None \<and> (snd (entriesi mi) = p)) * true"])
    apply(sep_auto simp: pointermap_getmki_defs is_array_list_def split: prod.splits;fail)
   apply(sep_auto simp: pointermap_getmki_defs)+
  done

end
