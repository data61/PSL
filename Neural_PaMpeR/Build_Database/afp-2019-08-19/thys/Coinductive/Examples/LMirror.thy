(*  Title:       LMirror
    Author:      Andreas Lochbihler, ETH Zurich
*)

section \<open>Definition of the function lmirror\<close>

theory LMirror imports "../Coinductive_List" begin

text \<open>This theory defines a function \<open>lmirror\<close>.\<close>

primcorec lmirror_aux :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist"
where
  "lmirror_aux acc xs = (case xs of LNil \<Rightarrow> acc | LCons x xs' \<Rightarrow> LCons x (lmirror_aux (LCons x acc) xs'))"

definition lmirror :: "'a llist \<Rightarrow> 'a llist"
where "lmirror = lmirror_aux LNil"


simps_of_case lmirror_aux_simps [simp]: lmirror_aux.code

lemma lnull_lmirror_aux [simp]:
  "lnull (lmirror_aux acc xs) = (lnull xs \<and> lnull acc)"
by(fact lmirror_aux.simps)

lemma ltl_lmirror_aux:
  "ltl (lmirror_aux acc xs) = (if lnull xs then ltl acc else lmirror_aux (LCons (lhd xs) acc) (ltl xs))"
by(cases acc)(simp_all split: llist.split)

lemma lhd_lmirror_aux:
  "lhd (lmirror_aux acc xs) = (if lnull xs then lhd acc else lhd xs)"
by(cases acc)(simp_all split: llist.split)

declare lmirror_aux.sel[simp del]

lemma lfinite_lmirror_aux [simp]:
  "lfinite (lmirror_aux acc xs) \<longleftrightarrow> lfinite xs \<and> lfinite acc"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  thus ?rhs
  proof(induct zs\<equiv>"lmirror_aux acc xs" arbitrary: acc xs rule: lfinite_induct)
    case LCons
    thus ?case
    proof(cases "lnull xs")
      case True
      with LCons.hyps(3)[of "ltl acc" LNil]
      show ?thesis by(simp add: ltl_lmirror_aux)
    qed(fastforce simp add: ltl_lmirror_aux)
  qed simp
next
  assume ?rhs
  hence "lfinite xs" "lfinite acc" by simp_all
  thus ?lhs by(induction arbitrary: acc) simp_all
qed

lemma lmirror_aux_inf:
  "\<not> lfinite xs \<Longrightarrow> lmirror_aux acc xs = xs"
by(coinduction arbitrary: acc xs)(auto simp add: lhd_lmirror_aux ltl_lmirror_aux)

lemma lmirror_aux_acc:
  "lmirror_aux (lappend ys zs) xs = lappend (lmirror_aux ys xs) zs"
proof(cases "lfinite xs")
  case False
  thus ?thesis by(simp add: lmirror_aux_inf lappend_inf)
next
  case True
  thus ?thesis
    by(induction arbitrary: ys)(simp_all add: lappend_code(2)[symmetric] del: lappend_code(2))
qed

lemma lmirror_aux_LCons:
  "lmirror_aux acc (LCons x xs) = LCons x (lappend (lmirror_aux LNil xs) (LCons x acc))"
by (metis lappend_code(1) lmirror_aux_acc lmirror_aux_simps(2))

lemma llength_lmirror_aux: "llength (lmirror_aux acc xs) = 2 * llength xs + llength acc"
apply(coinduction arbitrary: acc xs rule: enat_coinduct)
apply(auto simp add: iadd_is_0 epred_iadd1 mult_2 epred_llength ltl_lmirror_aux iadd_Suc_right)
apply(rule exI conjI refl)+
apply(simp add: iadd_Suc_right llength_ltl)
by (metis (hide_lams, no_types) add.commute epred_llength iadd_Suc_right lhd_LCons_ltl llength_LCons)

lemma lnull_lmirror [simp]: "lnull (lmirror xs) = lnull xs"
by(simp add: lmirror_def)

lemma lmirror_LNil [simp]: "lmirror LNil = LNil"
by(simp add: lmirror_def)

lemma lmirror_LCons [simp]: "lmirror (LCons x xs) = LCons x (lappend (lmirror xs) (LCons x LNil))"
by(simp only: lmirror_aux_LCons lmirror_def)

lemma ltl_lmirror [simp]:
  "\<not> lnull xs \<Longrightarrow> ltl (lmirror xs) = lappend (lmirror (ltl xs)) (LCons (lhd xs) LNil)"
by(clarsimp simp add: not_lnull_conv)

lemma lmap_lmirror_aux: "lmap f (lmirror_aux acc xs) = lmirror_aux (lmap f acc) (lmap f xs)"
by(coinduction arbitrary: acc xs rule: llist.coinduct_strong)(auto 4 3 simp add: lhd_lmirror_aux ltl_lmirror_aux)

lemma lmap_lmirror: "lmap f (lmirror xs) = lmirror (lmap f xs)"
by(simp add: lmirror_def lmap_lmirror_aux)

lemma lset_lmirror_aux: "lset (lmirror_aux acc xs) = lset (lappend xs acc)"
proof(cases "lfinite xs")
  case True thus ?thesis
    by(induction arbitrary: acc) simp_all
qed(simp add: lmirror_aux_inf lappend_inf)

lemma lset_lmirror [simp]: "lset (lmirror xs) = lset xs"
by(simp add: lmirror_def lset_lmirror_aux)

lemma llength_lmirror [simp]: "llength (lmirror xs) = 2 * llength xs"
by(simp add: lmirror_def llength_lmirror_aux)

lemma lmirror_llist_of [simp]: "lmirror (llist_of xs) = llist_of (xs @ rev xs)"
by(induct xs)(simp_all add: lappend_llist_of_LCons)

lemma list_of_lmirror [simp]: "lfinite xs \<Longrightarrow> list_of (lmirror xs) = list_of xs @ rev (list_of xs)"
by (metis list_of_llist_of llist_of_list_of lmirror_llist_of)

lemma llist_all2_lmirror_aux:
  "\<lbrakk> llist_all2 P acc acc'; llist_all2 P xs xs' \<rbrakk>
  \<Longrightarrow> llist_all2 P (lmirror_aux acc xs) (lmirror_aux acc' xs')"
by(coinduction arbitrary: acc acc' xs xs')(auto simp add: lhd_lmirror_aux ltl_lmirror_aux elim: llist_all2_lhdD intro!: llist_all2_ltlI exI dest: llist_all2_lnullD)

lemma enat_mult_cancel1 [simp]:
  "k * m = k * n \<longleftrightarrow> m = n \<or> k = 0 \<or> k = (\<infinity> :: enat) \<and> n \<noteq> 0 \<and> m \<noteq> 0"
by(cases k m n rule: enat.exhaust[case_product enat.exhaust[case_product enat.exhaust]])(simp_all add: zero_enat_def)

lemma llist_all2_lmirror_auxD:
  "\<lbrakk> llist_all2 P (lmirror_aux acc xs) (lmirror_aux acc' xs'); llist_all2 P acc acc'; lfinite acc \<rbrakk>
  \<Longrightarrow> llist_all2 P xs xs'"
proof(coinduction arbitrary: xs xs' acc acc')
  case (LNil xs xs' acc acc')
  from \<open>llist_all2 P (lmirror_aux acc xs) (lmirror_aux acc' xs')\<close>
  have "llength (lmirror_aux acc xs) = llength (lmirror_aux acc' xs')"
    by(rule llist_all2_llengthD)
  moreover from \<open>llist_all2 P acc acc'\<close>
  have "llength acc = llength acc'" by(rule llist_all2_llengthD)
  ultimately have "llength xs = llength xs'"
    using \<open>lfinite acc\<close> by(auto simp add: llength_lmirror_aux dest: lfinite_llength_enat)
  thus ?case by auto
next
  case (LCons xs xs' acc acc')
  from \<open>llist_all2 P (lmirror_aux acc xs) (lmirror_aux acc' xs')\<close> \<open>\<not> lnull xs\<close> \<open>\<not> lnull xs'\<close>
  have ?lhd by(auto dest: llist_all2_lhdD simp add: lhd_lmirror_aux)
  thus ?case using LCons \<open>llist_all2 P (lmirror_aux acc xs) (lmirror_aux acc' xs')\<close>[THEN llist_all2_ltlI]
    by(auto 4 3 simp add: ltl_lmirror_aux)
qed

lemma llist_all2_lmirrorI:
  "llist_all2 P xs ys \<Longrightarrow> llist_all2 P (lmirror xs) (lmirror ys)"
by(simp add: lmirror_def llist_all2_lmirror_aux)

lemma llist_all2_lmirrorD:
  "llist_all2 P (lmirror xs) (lmirror ys) \<Longrightarrow> llist_all2 P xs ys"
unfolding lmirror_def by(erule llist_all2_lmirror_auxD) simp_all

lemma llist_all2_lmirror [simp]:
  "llist_all2 P (lmirror xs) (lmirror ys) \<longleftrightarrow> llist_all2 P xs ys"
by(blast intro: llist_all2_lmirrorI llist_all2_lmirrorD)

lemma lmirror_parametric [transfer_rule]:
  includes lifting_syntax
  shows "(llist_all2 A ===> llist_all2 A) lmirror lmirror"
by(rule rel_funI)(rule llist_all2_lmirrorI)

end
