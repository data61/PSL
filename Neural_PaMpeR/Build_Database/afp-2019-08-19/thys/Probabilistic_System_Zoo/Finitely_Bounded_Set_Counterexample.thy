section \<open>Sets Bounded by a Finite Cardinal $>2$ Are Not BNFs\<close>

(*<*)
theory Finitely_Bounded_Set_Counterexample
imports
  "HOL-Cardinals.Cardinals"
begin
(*>*)

text \<open>Do not import this theory. It contains an inconsistent axiomatization.
The point is to exhibit the particular inconsistency.\<close>

typedef ('a, 'k) bset ("_ set[_]" [22, 21] 21) =
  "{A :: 'a set. |A| <o |UNIV :: 'k set|}"
  morphisms set_bset Abs_bset
  by (rule exI[of _ "{}"]) (auto simp: card_of_empty4 csum_def)

setup_lifting type_definition_bset

lift_definition map_bset ::
  "('a \<Rightarrow> 'b) \<Rightarrow> 'a set['k] \<Rightarrow> 'b set['k]" is image
  using card_of_image ordLeq_ordLess_trans by blast

inductive rel_bset :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a, 'k) bset \<Rightarrow> ('b, 'k) bset \<Rightarrow> bool" for R where
  "set_bset x \<subseteq> {(x, y). R x y} \<Longrightarrow> rel_bset R (map_bset fst x) (map_bset snd x)"

text \<open>
We axiomatize the relator commutation property and show that we can deduce @{term False} from it.

We cannot do this with a locale, since we need the fully polymorphic version of the following axiom.
\<close>

axiomatization where
  inconsistent: "rel_bset R1 OO rel_bset R2 \<le> rel_bset (R1 OO R2)"

bnf "('a, 'k) bset"
  map: map_bset
  sets: set_bset
  bd: "|UNIV :: 'k set| +c natLeq"
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
    apply (erule ordLeq_transitive[OF ordLess_imp_ordLeq ordLeq_csum1])
    apply simp
    done
next
  case 8 then show ?case by (rule inconsistent) \<comment> \<open>BAAAAAMMMM\<close>
next
  case 9 then show ?case
    by (auto simp: fun_eq_iff intro: rel_bset.intros elim: rel_bset.cases)
qed

lemma card_option_finite[simp]:
  assumes "finite (UNIV :: 'k set)"
  shows "card (UNIV :: 'k option set) = Suc (card (UNIV :: 'k set))"
  (is "card ?L = Suc (card ?R)")
proof -
  have "card ?L = Suc (card (?L - {None}))" by (rule card.remove) (auto simp: assms)
  also have "card (?L - {None}) = card ?R"
    by (rule bij_betw_same_card[of the])
      (auto simp: bij_betw_def inj_on_def image_iff intro!: bexI[of _ "Some x" for x])
  finally show ?thesis .
qed

datatype ('a :: enum) x = A | B "'a option" | C

abbreviation "Bs \<equiv> B ` (insert None (Some ` set Enum.enum))"

lemma UNIV_x[simp]:
  "(UNIV :: ('a :: enum) x set) = {A, C} \<union> Bs"
  (is "_ = ?R")
proof (intro set_eqI iffI)
  fix x :: "'a x" show "x \<in> ?R" by (cases x) (auto simp add: enum_UNIV)
qed simp

lemma Collect_split_in_rel: "{(x, y). in_rel R x y} = R"
  by auto

lift_definition X :: "('a :: enum x, 'a x) bset" is "insert A Bs"
  by (subst finite_card_of_iff_card3) (auto simp: card_insert card_Diff_singleton_if)

lift_definition Y :: "('a :: enum x, 'a x) bset" is "insert C Bs"
  by (subst finite_card_of_iff_card3) (auto simp: card_insert card_Diff_singleton_if)

lift_definition Z :: "('a :: enum x, 'a x) bset" is "{A, C}"
  by (subst finite_card_of_iff_card3) (auto simp: card_insert card_Diff_singleton_if)

lift_definition R :: "('a x \<times> 'a x, 'a :: enum x) bset" is "insert (A, A) ((\<lambda>B. (B, C)) ` Bs)"
  by (subst finite_card_of_iff_card3)
    (auto simp: card_insert card_Diff_singleton_if image_iff card_image inj_on_def)

lift_definition S :: "('a x \<times> 'a x, 'a :: enum x) bset" is "insert (C, C) ((\<lambda>B. (A, B)) ` Bs)"
  by (subst finite_card_of_iff_card3)
    (auto simp: card_insert card_Diff_singleton_if image_iff card_image inj_on_def)

lift_definition in_brel :: "('a \<times> 'b, 'k) bset \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> bool" is in_rel .

lemma False
proof -
  have "rel_bset (in_brel R) X Z"
    unfolding bset.in_rel mem_Collect_eq
    apply (intro exI[of _ R])
    apply transfer
    apply (auto simp: image_iff)
    done
  moreover
  have "rel_bset (in_brel S) Z Y"
    unfolding bset.in_rel mem_Collect_eq
    apply (intro exI[of _ S])
    apply transfer
    apply (auto simp: image_iff)
    done
  ultimately have "rel_bset (in_brel R OO in_brel S) X Y"
    unfolding bset.rel_compp by blast
  moreover
  have *: "insert (A, A) ((\<lambda>B. (B, C)) ` Bs) O insert (C, C) ((\<lambda>B. (A, B)) ` Bs) =
    ((\<lambda>B. (B, C)) ` Bs) \<union> ((\<lambda>B. (A, B)) ` Bs)" (is "_ = ?RS" ) by auto
  have "\<not> rel_bset (in_brel R OO in_brel S) X Y"
  unfolding bset.in_rel mem_Collect_eq
  proof (transfer, safe, unfold relcompp_in_rel * Collect_split_in_rel)
    fix Z :: "('a :: enum x \<times> 'a x) set"
    note enum_UNIV[simp] UNIV_option_conv[symmetric, simp]
    assume "Z \<subseteq> ?RS" "fst ` Z = insert A Bs" "snd ` Z = insert C Bs"
    then have "Z = ?RS" unfolding fst_eq_Domain snd_eq_Range by auto
    moreover assume "|Z| <o |UNIV :: 'a x set|"
    ultimately show False unfolding \<open>Z = ?RS\<close>
      by (subst (asm) finite_card_of_iff_card3, simp, simp, subst (asm) card_Un_disjoint)
        (auto simp: card_insert card_Diff_singleton_if card_image inj_on_def split: if_splits)
  qed
  ultimately show False by blast
qed

(*<*)
end
(*>*)
