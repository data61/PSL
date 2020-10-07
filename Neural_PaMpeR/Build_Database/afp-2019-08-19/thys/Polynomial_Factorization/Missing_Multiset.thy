(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Preliminaries\<close>
subsection \<open>Missing Multiset\<close>

text \<open>This theory provides some definitions and lemmas on multisets which we did not find in the 
  Isabelle distribution.\<close>

theory Missing_Multiset
imports
  "HOL-Library.Multiset"
  Missing_List
begin

lemma remove_nth_soundness:
  assumes "n < length as"
  shows "mset (remove_nth n as) = mset as - {#(as!n)#}"
using assms 
proof (induct as arbitrary: n)
  case (Cons a as)
  note [simp] = remove_nth_def
  show ?case
  proof (cases n)
    case (Suc n)
    with Cons have n_bd: "n < length as" by auto
    with Cons have "mset (remove_nth n as) = mset as - {#as ! n#}" by auto
    hence G: "mset (remove_nth (Suc n) (a # as)) = mset as - {#as ! n#} + {#a#}"
      by simp
    thus ?thesis
    proof (cases "a = as!n")
      case True
      with G and Suc and insert_DiffM2[symmetric]
        and insert_DiffM2[of _ "{#as ! n#}"]
        and nth_mem_mset[of n as] and n_bd
      show ?thesis by auto
    next
      case False
      from G and Suc and diff_union_swap[OF this[symmetric], symmetric] show ?thesis by simp
    qed
  qed auto
qed auto


lemma multiset_subset_insert: "{ps. ps \<subseteq># add_mset x xs} =
    {ps. ps \<subseteq># xs} \<union> add_mset x ` {ps. ps \<subseteq># xs}" (is "?l = ?r")
proof -
  {
    fix ps
    have "(ps \<in> ?l) = (ps \<subseteq># xs + {# x #})" by auto
    also have "\<dots> = (ps \<in> ?r)"
    proof (cases "x \<in># ps")
      case True
      then obtain qs where ps: "ps = qs + {#x#}" by (metis insert_DiffM2)
      show ?thesis unfolding ps mset_subset_eq_mono_add_right_cancel
        by (auto dest: mset_subset_eq_insertD)
    next
      case False
      hence id: "(ps \<subseteq># xs + {#x#}) = (ps \<subseteq># xs)"
        by (simp add: subset_mset.inf.absorb_iff2 inter_add_left1)
      show ?thesis unfolding id using False by auto
    qed
    finally have "(ps \<in> ?l) = (ps \<in> ?r)" .
  }
  thus ?thesis by auto
qed

lemma multiset_of_subseqs: "mset ` set (subseqs xs) = { ps. ps \<subseteq># mset xs}"
proof (induct xs)
  case (Cons x xs)
  show ?case (is "?l = ?r")
  proof -
    have id: "?r = {ps. ps \<subseteq># mset xs} \<union> (add_mset x) ` {ps. ps \<subseteq># mset xs}"
      by (simp add: multiset_subset_insert)
    show ?thesis unfolding id Cons[symmetric]
      by (auto simp add: Let_def) (metis UnCI image_iff mset.simps(2))
  qed
qed simp

lemma remove1_mset: "w \<in> set vs \<Longrightarrow> mset (remove1 w vs) + {#w#} = mset vs"
  by (induct vs) auto

lemma fold_remove1_mset: "mset ws \<subseteq># mset vs \<Longrightarrow> mset (fold remove1 ws vs) + mset ws = mset vs" 
proof (induct ws arbitrary: vs)
  case (Cons w ws vs)
  from Cons(2) have "w \<in> set vs" using set_mset_mono by force
  from remove1_mset[OF this] have vs: "mset vs = mset (remove1 w vs) + {#w#}" by simp
  from Cons(2)[unfolded vs] have "mset ws \<subseteq># mset (remove1 w vs)" by auto
  from Cons(1)[OF this,symmetric]
  show ?case unfolding vs by (simp add: ac_simps)
qed simp

lemma subseqs_sub_mset: "ws \<in> set (subseqs vs) \<Longrightarrow> mset ws \<subseteq># mset vs" 
proof (induct vs arbitrary: ws)
  case (Cons v vs Ws)
  note mem = Cons(2)
  note IH = Cons(1)
  show ?case
  proof (cases Ws)
    case (Cons w ws)
    show ?thesis
    proof (cases "v = w")
      case True
      from mem Cons have "ws \<in> set (subseqs vs)" by (auto simp: Let_def Cons_in_subseqsD[of _ ws vs])
      from IH[OF this]
      show ?thesis unfolding Cons True by simp
    next
      case False
      with mem Cons have "Ws \<in> set (subseqs vs)" by (auto simp: Let_def Cons_in_subseqsD[of _ ws vs])      
      note IH = mset_subset_eq_count[OF IH[OF this]]
      with IH[of v] show ?thesis by (intro mset_subset_eqI, auto, linarith) 
    qed 
  qed simp
qed simp

lemma filter_mset_inequality: "filter_mset f xs \<noteq> xs \<Longrightarrow> \<exists> x \<in># xs. \<not> f x" 
  by (induct xs, auto)

end
