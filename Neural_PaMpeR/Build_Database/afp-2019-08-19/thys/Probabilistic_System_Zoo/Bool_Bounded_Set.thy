section \<open>Sets with at Most 2 Elements\<close>

(*<*)
theory Bool_Bounded_Set
imports
  "HOL-Cardinals.Cardinals"
begin
(*>*)

typedef 'a bset =
  "{A :: 'a set. |A| \<le>o ctwo}"
  morphisms set_bset Abs_bset
  by (rule exI[of _ "{}"]) (auto simp: card_of_empty4 ctwo_def)

setup_lifting type_definition_bset

lift_definition map_bset ::
  "('a \<Rightarrow> 'b) \<Rightarrow> 'a bset \<Rightarrow> 'b bset" is image
  using card_of_image ordLeq_transitive by blast

inductive rel_bset :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a bset \<Rightarrow> 'b bset \<Rightarrow> bool" for R where
  "set_bset x \<subseteq> {(x, y). R x y} \<Longrightarrow> rel_bset R (map_bset fst x) (map_bset snd x)"

lift_definition bempty :: "'a bset" is "{}"  by (auto simp: card_of_empty4 ctwo_def)
lift_definition bsingleton :: "'a \<Rightarrow> 'a bset" is "\<lambda>x. {x}" by (auto simp: ctwo_def)
lift_definition bdoubleton :: "'a \<Rightarrow> 'a \<Rightarrow> 'a bset" is "\<lambda>x y. {x, y}"
  by (auto simp: ctwo_def finite_card_of_iff_card2 card_insert card_Diff_singleton_if)

lemma map_bset_bempty[simp]: "map_bset f bempty = bempty"
  by transfer simp

lemma map_bset_eq_bempty[simp]:
  "map_bset f x = bempty \<longleftrightarrow> x = bempty"
  "bempty = map_bset f x \<longleftrightarrow> x = bempty"
  by (transfer, simp)+

lemma map_bset_bsingleton[simp]: "map_bset f (bsingleton x) = bsingleton (f x)"
  by transfer simp

lemma map_bset_bdoubleton[simp]: "map_bset f (bdoubleton x y) = bdoubleton (f x) (f y)"
  by transfer simp

lemma bdoubleton_same[simp]: "bdoubleton x x = bsingleton x"
  by transfer simp

lemma bempty_neq_bsingleton[simp]:
  "bempty \<noteq> bsingleton x"
  "bsingleton x \<noteq> bempty"
  by (transfer, simp)+

lemma bempty_neq_bdoubleton[simp]:
  "bempty \<noteq> bdoubleton x y"
  "bdoubleton x y \<noteq> bempty"
  by (transfer, simp)+

lemma bsinleton_eq_bdoubleton[simp]:
  "bsingleton x = bdoubleton y z \<longleftrightarrow> (x = y \<and> y = z)"
  "bdoubleton y z = bsingleton x \<longleftrightarrow> (x = y \<and> y = z)"
  by (transfer, auto)+

lemma bsinleton_inj[simp]:
  "bsingleton x = bsingleton y \<longleftrightarrow> (x = y)"
  by (transfer, simp)

lemma bdoubleton_eq_iff[simp]:
  "bdoubleton x y = bdoubleton z w \<longleftrightarrow> (x = z \<and> y = w \<or> x = w \<and> y = z)"
  by transfer (simp add: doubleton_eq_iff)

lemmas [simp] = bempty.rep_eq bsingleton.rep_eq bdoubleton.rep_eq

lemma bset_cases:
  "\<lbrakk>X = bempty \<Longrightarrow> P; \<And>x. X = bsingleton x \<Longrightarrow> P; \<And>x y. \<lbrakk>x \<noteq> y; X = bdoubleton x y\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
proof (transfer fixing: P)
  fix Z :: "'a set"
  assume "|Z| \<le>o ctwo"
  moreover then have "finite Z" by (metis card_of_ordLeq_infinite ctwo_def finite_code)
  ultimately have "card Z \<le> 2" unfolding ctwo_def by (subst (asm) finite_card_of_iff_card2) auto
  moreover assume "Z = {} \<Longrightarrow> P" "\<And>x. Z = {x} \<Longrightarrow> P" "\<And>x y. \<lbrakk>x \<noteq> y; Z = {x, y}\<rbrakk> \<Longrightarrow> P"
  ultimately show P using \<open>finite Z\<close>
  proof (induct "card Z")
    case (Suc m) from Suc(2)[symmetric] Suc(2-7) show P by (cases m) (auto simp: card_Suc_eq)
  qed simp
qed

bnf "'k bset"
  map: map_bset
  sets: set_bset
  bd: natLeq
  rel: rel_bset
proof (standard, goal_cases)
  case 1 then show ?case
    by transfer simp
next
  case 2 then show ?case
    apply (rule ext)
    apply transfer
    apply auto
    done
next
  case 3 then show ?case
    apply transfer
    apply (auto simp: image_iff)
    done
next
  case 4 then show ?case
    apply (rule ext)
    apply transfer
    apply simp
    done
next
  case 5 then show ?case by (simp add: card_order_csum natLeq_card_order)
next
  case 6 then show ?case by (simp add: cinfinite_csum natLeq_cinfinite)
next
  case 7 then show ?case
    apply transfer
    apply (erule ordLeq_transitive[OF _ ordLess_imp_ordLeq[OF ctwo_ordLess_natLeq]])
    done
next
  case (8 R S)
  then show ?case
  proof (safe elim!: rel_bset.cases, unfold rel_bset.simps)
    fix z1 z2
    assume "set_bset z1 \<subseteq> {(x, y). R x y}" "set_bset z2 \<subseteq> {(x, y). S x y}" "map_bset snd z1 = map_bset fst z2"
    then show "\<exists>x. map_bset fst z1 = map_bset fst x \<and> map_bset snd z2 = map_bset snd x \<and>
      set_bset x \<subseteq> {(x, y). (R OO S) x y}"
      by (cases z1 z2 rule: bset_cases[case_product bset_cases])
        (fastforce intro: exI[of _ "bsingleton (a, b)" for a b]
        dest: spec[of _ "bdoubleton (a, b) (c, d)" for a b c d])+
  qed
next
  case (9 R)
  then show ?case
    by (auto simp: fun_eq_iff intro: rel_bset.intros elim: rel_bset.cases)
qed

(*<*)
end
(*>*)
