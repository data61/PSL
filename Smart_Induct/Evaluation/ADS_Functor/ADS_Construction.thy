(* Author: Andreas Lochbihler, Digital Asset
   Author: Ognjen Maric, Digital Asset *)

theory ADS_Construction imports
  Merkle_Interface
  "HOL-Library.Simps_Case_Conv"
begin

(************************************************************)
section \<open> Building blocks for authenticated data structures on datatypes \<close>
(************************************************************)

(************************************************************)
subsection \<open> Building Block: Identity Functor \<close>
(************************************************************)

text \<open>If nothing is blindable in a type, then the type itself is the hash and the ADS of itself.\<close>

abbreviation (input) hash_discrete :: "('a, 'a) hash" where "hash_discrete \<equiv> id"

abbreviation (input) blinding_of_discrete :: "'a blinding_of" where
  "blinding_of_discrete \<equiv> (=)"

definition merge_discrete :: "'a merge" where
  "merge_discrete x y = (if x = y then Some y else None)"

lemma blinding_of_discrete_hash:
  "blinding_of_discrete \<le> vimage2p hash_discrete hash_discrete (=)"
  by(auto simp add: vimage2p_def)

lemma blinding_of_on_discrete [locale_witness]:
  "blinding_of_on UNIV hash_discrete blinding_of_discrete"
  by(unfold_locales)(simp_all add: OO_eq eq_onp_def blinding_of_discrete_hash)

lemma merge_on_discrete [locale_witness]:
  "merge_on UNIV hash_discrete blinding_of_discrete merge_discrete"
  by unfold_locales(auto simp add: merge_discrete_def)

lemma merkle_discrete [locale_witness]:
  "merkle_interface hash_discrete blinding_of_discrete merge_discrete"
  ..

parametric_constant merge_discrete_parametric [transfer_rule]: merge_discrete_def

(************************************************************)
subsubsection \<open>Example: instantiation for @{typ unit}\<close>
(************************************************************)

abbreviation (input) hash_unit :: "(unit, unit) hash" where "hash_unit \<equiv> hash_discrete"

abbreviation blinding_of_unit :: "unit blinding_of" where
  "blinding_of_unit \<equiv> blinding_of_discrete"

abbreviation merge_unit :: "unit merge" where "merge_unit \<equiv> merge_discrete"

lemma blinding_of_unit_hash:
  "blinding_of_unit \<le> vimage2p hash_unit hash_unit (=)"
  by(fact blinding_of_discrete_hash)

lemma blinding_of_on_unit:
  "blinding_of_on UNIV hash_unit blinding_of_unit"
  by(fact blinding_of_on_discrete)

lemma merge_on_unit:
  "merge_on UNIV hash_unit blinding_of_unit merge_unit"
  by(fact merge_on_discrete)

lemma merkle_interface_unit:
  "merkle_interface hash_unit blinding_of_unit merge_unit"
  by(intro merkle_interfaceI merge_on_unit)

(************************************************************)
subsection \<open> Building Block: Blindable Position \<close>
(************************************************************)

type_synonym 'a blindable = 'a

text \<open> The following type represents the hashes of a datatype. We model hashes as being injective,
  but not surjective; some hashes do not correspond to any values of the original datatypes. We
  model such values as "garbage" coming from a countable set (here, naturals). \<close>

type_synonym garbage = nat

datatype 'a\<^sub>h blindable\<^sub>h = Content 'a\<^sub>h | Garbage garbage

datatype ('a\<^sub>m, 'a\<^sub>h) blindable\<^sub>m = Unblinded 'a\<^sub>m | Blinded "'a\<^sub>h blindable\<^sub>h"

(************************************************************)
subsubsection \<open> Hashes \<close>
(************************************************************)

primrec hash_blindable' :: "(('a\<^sub>h, 'a\<^sub>h) blindable\<^sub>m, 'a\<^sub>h blindable\<^sub>h) hash" where
  "hash_blindable' (Unblinded x) = Content x"
| "hash_blindable' (Blinded x) = x"

definition hash_blindable :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> (('a\<^sub>m, 'a\<^sub>h) blindable\<^sub>m, 'a\<^sub>h blindable\<^sub>h) hash" where
  "hash_blindable h = hash_blindable' \<circ> map_blindable\<^sub>m h id"

lemma hash_blindable_simps [simp]:
  "hash_blindable h (Unblinded x) = Content (h x)"
  "hash_blindable h (Blinded y) = y"
  by(simp_all add: hash_blindable_def blindable\<^sub>h.map_id)

lemma hash_map_blindable_simp:
  "hash_blindable f (map_blindable\<^sub>m f' id x) = hash_blindable (f o f') x"
  by(cases x) (simp_all add: hash_blindable_def blindable\<^sub>h.map_comp)

parametric_constant hash_blindable'_parametric [transfer_rule]: hash_blindable'_def

parametric_constant hash_blindable_parametric [transfer_rule]: hash_blindable_def

(************************************************************)
subsubsection \<open> Blinding \<close>
(************************************************************)

context
  fixes h :: "('a\<^sub>m, 'a\<^sub>h) hash"
    and bo :: "'a\<^sub>m blinding_of"
begin

inductive blinding_of_blindable :: "('a\<^sub>m, 'a\<^sub>h) blindable\<^sub>m blinding_of" where
  "blinding_of_blindable (Unblinded x) (Unblinded y)" if "bo x y"
| "blinding_of_blindable (Blinded x) t" if "hash_blindable h t = x"

inductive_simps blinding_of_blindable_simps [simp]:
  "blinding_of_blindable (Unblinded x) y"
  "blinding_of_blindable (Blinded x) y"
  "blinding_of_blindable z (Unblinded x)"
  "blinding_of_blindable z (Blinded x)"

inductive_simps blinding_of_blindable_simps2:
   "blinding_of_blindable (Unblinded x) (Unblinded y)"
   "blinding_of_blindable (Unblinded x) (Blinded y')"
   "blinding_of_blindable (Blinded x') (Unblinded y)"
   "blinding_of_blindable (Blinded x') (Blinded y')"

end

lemma blinding_of_blindable_mono:
  assumes "bo \<le> bo'"
  shows "blinding_of_blindable h bo \<le> blinding_of_blindable h bo'"
  apply(rule predicate2I)
  apply(erule blinding_of_blindable.cases; hypsubst)
  subgoal by(rule blinding_of_blindable.intros)(rule assms[THEN predicate2D])
  subgoal by(rule blinding_of_blindable.intros) simp
  done

lemma blinding_of_blindable_hash:
  assumes "bo \<le> vimage2p h h (=)"
  shows "blinding_of_blindable h bo \<le> vimage2p (hash_blindable h) (hash_blindable h) (=)"
  apply(rule predicate2I vimage2pI)+
  apply(erule blinding_of_blindable.cases; hypsubst)
  subgoal using assms[THEN predicate2D] by(simp add: vimage2p_def)
  subgoal by simp
  done

lemma blinding_of_on_blindable [locale_witness]:
  assumes "blinding_of_on A h bo"
  shows "blinding_of_on {x. set1_blindable\<^sub>m x \<subseteq> A} (hash_blindable h) (blinding_of_blindable h bo)"
  (is "blinding_of_on ?A ?h ?bo")
proof -
  interpret blinding_of_on A h bo by fact
  show ?thesis
  proof
    show "?bo \<le> vimage2p ?h ?h (=)"
      by(rule blinding_of_blindable_hash)(rule hash)
    show "?bo x x" if "x \<in> ?A" for x using that by(cases x)(auto simp add: refl)
    show "?bo x z" if "?bo x y" "?bo y z" "x \<in> ?A" for x y z using that
      by(auto elim!: blinding_of_blindable.cases dest: trans blinding_hash_eq)
    show "x = y" if "?bo x y" "?bo y x" "x \<in> ?A" for x y using that
      by(auto elim!: blinding_of_blindable.cases dest: antisym)
  qed
qed

lemmas blinding_of_blindable [locale_witness] = blinding_of_on_blindable[of UNIV, simplified]

case_of_simps blinding_of_blindable_alt_def: blinding_of_blindable_simps2
parametric_constant blinding_of_blindable_parametric [transfer_rule]: blinding_of_blindable_alt_def

(************************************************************)
subsubsection \<open> Merging \<close>
(************************************************************)

context
  fixes h :: "('a\<^sub>m, 'a\<^sub>h) hash"
  fixes m :: "'a\<^sub>m merge"
begin

fun merge_blindable :: "('a\<^sub>m, 'a\<^sub>h) blindable\<^sub>m merge" where
  "merge_blindable (Unblinded x) (Unblinded y) = map_option Unblinded (m x y)"
| "merge_blindable (Blinded x) (Unblinded y) = (if x = Content (h y) then Some (Unblinded y) else None)"
| "merge_blindable (Unblinded y) (Blinded x) = (if x = Content (h y) then Some (Unblinded y) else None)"
| "merge_blindable (Blinded t) (Blinded u) = (if t = u then Some (Blinded u) else None)"

lemma merge_on_blindable [locale_witness]:
  assumes "merge_on A h bo m"
  shows "merge_on {x. set1_blindable\<^sub>m x \<subseteq> A} (hash_blindable h) (blinding_of_blindable h bo) merge_blindable"
  (is "merge_on ?A ?h ?bo ?m")
proof -
  interpret merge_on A h bo m by fact
  show ?thesis
  proof
    show "\<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and> (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u)" if "?h a = ?h b" "a \<in> ?A" for a b
      using that by(cases "(a, b)" rule: merge_blindable.cases)(auto simp add: refl dest!: join)
    show "?m a b = None" if "?h a \<noteq> ?h b" "a \<in> ?A" for a b 
      using that by(cases "(a, b)" rule: merge_blindable.cases)(auto simp add: dest!: undefined)
  qed
qed

lemmas merge_blindable [locale_witness] = 
  merge_on_blindable[of UNIV, simplified]

end

lemma merge_blindable_alt_def:
  "merge_blindable h m x y = (case (x, y) of
    (Unblinded x, Unblinded y) \<Rightarrow> map_option Unblinded (m x y)
  | (Blinded x, Unblinded y) \<Rightarrow> (if Content (h y) = x then Some (Unblinded y) else None)
  | (Unblinded y, Blinded x) \<Rightarrow> (if Content (h y) = x then Some (Unblinded y) else None)
  | (Blinded t, Blinded u) \<Rightarrow> (if t = u then Some (Blinded u) else None))"
  by(simp split: blindable\<^sub>m.split blindable\<^sub>h.split)

parametric_constant merge_blindable_parametric [transfer_rule]: merge_blindable_alt_def

lemma merge_blindable_cong [fundef_cong]:
  assumes "\<And>a b. \<lbrakk> a \<in> set1_blindable\<^sub>m x; b \<in> set1_blindable\<^sub>m y \<rbrakk> \<Longrightarrow> m a b = m' a b"
  shows "merge_blindable h m x y = merge_blindable h m' x y"
  by(auto simp add: merge_blindable_alt_def split: blindable\<^sub>m.split intro: assms intro!: arg_cong[where f="map_option _"])

(************************************************************)
subsubsection \<open> Merkle interface \<close>
(************************************************************)

lemma merkle_blindable [locale_witness]:
  assumes "merkle_interface h bo m"
  shows "merkle_interface (hash_blindable h) (blinding_of_blindable h bo) (merge_blindable h m)"
proof -
  interpret merge_on UNIV h bo m using assms by(simp add: merkle_interface_aux)
  show ?thesis unfolding merkle_interface_aux ..
qed


(************************************************************)
subsubsection \<open> Non-recursive blindable positions \<close>
(************************************************************)

text \<open> For a non-recursive data type @{typ 'a}, the type of hashes in @{type blindable\<^sub>m} is fixed
to be simply @{typ "'a blindable\<^sub>h"}. We obtain this by instantiating the type variable with the
identity building block. \<close>

type_synonym 'a nr_blindable = "('a, 'a) blindable\<^sub>m"

abbreviation hash_nr_blindable :: "('a nr_blindable, 'a blindable\<^sub>h) hash" where
  "hash_nr_blindable \<equiv> hash_blindable hash_discrete"

abbreviation blinding_of_nr_blindable :: "'a nr_blindable blinding_of" where
  "blinding_of_nr_blindable \<equiv> blinding_of_blindable hash_discrete blinding_of_discrete"

abbreviation merge_nr_blindable :: "'a nr_blindable merge" where
  "merge_nr_blindable \<equiv> merge_blindable hash_discrete merge_discrete"

lemma merge_on_nr_blindable:
  "merge_on UNIV hash_nr_blindable blinding_of_nr_blindable merge_nr_blindable"
  ..

lemma merkle_nr_blindable:
  "merkle_interface hash_nr_blindable blinding_of_nr_blindable merge_nr_blindable"
  ..

(************************************************************)
subsection \<open> Building block: Sums \<close>
(************************************************************)

text \<open> We prove that we can lift the ADS construction through sums.\<close>

type_synonym ('a\<^sub>h, 'b\<^sub>h) sum\<^sub>h = "'a\<^sub>h + 'b\<^sub>h"
type_notation sum\<^sub>h (infixr "+\<^sub>h" 10)

type_synonym ('a\<^sub>m, 'b\<^sub>m) sum\<^sub>m = "'a\<^sub>m + 'b\<^sub>m"
  \<comment> \<open>If a functor does not introduce blindable positions, then we don't need the type variable copies.\<close>
type_notation sum\<^sub>m (infixr "+\<^sub>m" 10)

(************************************************************)
subsubsection \<open> Hashes \<close>
(************************************************************)

abbreviation (input) hash_sum' :: "('a\<^sub>h +\<^sub>h 'b\<^sub>h, 'a\<^sub>h +\<^sub>h 'b\<^sub>h) hash" where
  "hash_sum' \<equiv> id"

abbreviation (input) hash_sum :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> ('b\<^sub>m, 'b\<^sub>h) hash \<Rightarrow> ('a\<^sub>m +\<^sub>m 'b\<^sub>m, 'a\<^sub>h +\<^sub>h 'b\<^sub>h) hash"
  where "hash_sum \<equiv> map_sum"

(************************************************************)
subsubsection \<open> Blinding \<close>
(************************************************************)

abbreviation (input) blinding_of_sum :: "'a\<^sub>m blinding_of \<Rightarrow> 'b\<^sub>m blinding_of \<Rightarrow> ('a\<^sub>m +\<^sub>m 'b\<^sub>m) blinding_of" where
  "blinding_of_sum \<equiv> rel_sum"

lemmas blinding_of_sum_mono = sum.rel_mono

lemma blinding_of_sum_hash:
  assumes "boa \<le> vimage2p rha rha (=)" "bob \<le> vimage2p rhb rhb (=)"
  shows "blinding_of_sum boa bob \<le> vimage2p (hash_sum rha rhb) (hash_sum rha rhb) (=)"
  using assms by(auto simp add: vimage2p_def elim!: rel_sum.cases)

lemma blinding_of_on_sum [locale_witness]:
  assumes "blinding_of_on A rha boa" "blinding_of_on B rhb bob"
  shows "blinding_of_on {x. setl x \<subseteq> A \<and> setr x \<subseteq> B} (hash_sum rha rhb) (blinding_of_sum boa bob)"
  (is "blinding_of_on ?A ?h ?bo")
proof -
  interpret a: blinding_of_on A rha boa by fact
  interpret b: blinding_of_on B rhb bob by fact
  show ?thesis
  proof
    show "?bo x x" if "x \<in> ?A" for x using that by(intro sum.rel_refl_strong)(auto intro: a.refl b.refl)
    show "?bo x z" if "?bo x y" "?bo y z" "x \<in> ?A" for x y z
      using that by(auto elim!: rel_sum.cases dest: a.trans b.trans)
    show "x = y" if "?bo x y" "?bo y x" "x \<in> ?A" for x y 
      using that by(auto elim!: rel_sum.cases dest: a.antisym b.antisym)
  qed(rule blinding_of_sum_hash a.hash b.hash)+
qed

lemmas blinding_of_sum [locale_witness] = blinding_of_on_sum[of UNIV _ _ UNIV, simplified]

(************************************************************)
subsubsection \<open> Merging \<close>
(************************************************************)

context
  fixes ma :: "'a\<^sub>m merge"
  fixes mb :: "'b\<^sub>m merge"
begin

fun merge_sum :: "('a\<^sub>m +\<^sub>m 'b\<^sub>m) merge" where
  "merge_sum (Inl x) (Inl y) = map_option Inl (ma x y)"
| "merge_sum (Inr x) (Inr y) = map_option Inr (mb x y)"
| "merge_sum _ _ = None"

lemma merge_on_sum [locale_witness]:
  assumes "merge_on A rha boa ma" "merge_on B rhb bob mb"
  shows "merge_on {x. setl x \<subseteq> A \<and> setr x \<subseteq> B} (hash_sum rha rhb) (blinding_of_sum boa bob) merge_sum"
  (is "merge_on ?A ?h ?bo ?m")
proof -
  interpret a: merge_on A rha boa ma by fact
  interpret b: merge_on B rhb bob mb by fact
  show ?thesis
  proof
    show "\<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and> (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u)"
      if "?h a = ?h b" "a \<in> ?A" for a b using that
      by(cases "(a, b)" rule: merge_sum.cases)(auto dest!: a.join b.join elim!: rel_sum.cases)
    show "?m a b = None" if "?h a \<noteq> ?h b" "a \<in> ?A" for a b using that
      by(cases "(a, b)" rule: merge_sum.cases)(auto dest!: a.undefined b.undefined)
  qed
qed

lemmas merge_sum [locale_witness] = merge_on_sum[where A=UNIV and B=UNIV, simplified]

lemma merge_sum_alt_def:
  "merge_sum x y = (case (x, y) of
    (Inl x, Inl y) \<Rightarrow> map_option Inl (ma x y)
  | (Inr x, Inr y) \<Rightarrow> map_option Inr (mb x y)
  | _ \<Rightarrow> None)"
  by(simp add: split: sum.split)

end

lemma merge_sum_cong[fundef_cong]:
  "\<lbrakk> x = x'; y = y'; 
    \<And>xl yl. \<lbrakk> x = Inl xl; y = Inl yl \<rbrakk> \<Longrightarrow> ma xl yl = ma' xl yl;
    \<And>xr yr. \<lbrakk> x = Inr xr; y = Inr yr \<rbrakk> \<Longrightarrow> mb xr yr = mb' xr yr \<rbrakk> \<Longrightarrow>
    merge_sum ma mb x y = merge_sum ma' mb' x' y'"
  by(cases x; simp_all; cases y; auto)

parametric_constant merge_sum_parametric [transfer_rule]: merge_sum_alt_def

subsubsection \<open> Merkle interface \<close>

lemma merkle_sum [locale_witness]:
  assumes "merkle_interface rha boa ma" "merkle_interface rhb bob mb"
  shows "merkle_interface (hash_sum rha rhb) (blinding_of_sum boa bob) (merge_sum ma mb)"
proof -
  interpret a: merge_on UNIV rha boa ma unfolding merkle_interface_aux[symmetric] by fact
  interpret b: merge_on UNIV rhb bob mb unfolding merkle_interface_aux[symmetric] by fact
  show ?thesis unfolding merkle_interface_aux[symmetric] ..
qed

(************************************************************)
subsection \<open> Building Block: Products\<close>
(************************************************************)

text \<open> We prove that we can lift the ADS construction through products.\<close>

type_synonym ('a\<^sub>h, 'b\<^sub>h) prod\<^sub>h = "'a\<^sub>h \<times> 'b\<^sub>h"
type_notation prod\<^sub>h ("(_ \<times>\<^sub>h/ _)" [21, 20] 20)

type_synonym ('a\<^sub>m, 'b\<^sub>m) prod\<^sub>m = "'a\<^sub>m \<times> 'b\<^sub>m"
  \<comment> \<open>If a functor does not introduce blindable positions, then we don't need the type variable copies.\<close>
type_notation prod\<^sub>m ("(_ \<times>\<^sub>m/ _)" [21, 20] 20)

(************************************************************)
subsubsection \<open> Hashes \<close>
(************************************************************)

abbreviation (input) hash_prod' :: "('a\<^sub>h \<times>\<^sub>h 'b\<^sub>h, 'a\<^sub>h \<times>\<^sub>h 'b\<^sub>h) hash" where
  "hash_prod' \<equiv> id"

abbreviation (input) hash_prod :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> ('b\<^sub>m, 'b\<^sub>h) hash \<Rightarrow> ('a\<^sub>m \<times>\<^sub>m 'b\<^sub>m, 'a\<^sub>h \<times>\<^sub>h 'b\<^sub>h) hash"
  where "hash_prod \<equiv> map_prod"

(************************************************************)
subsubsection \<open> Blinding \<close>
(************************************************************)

abbreviation (input) blinding_of_prod :: "'a\<^sub>m blinding_of \<Rightarrow> 'b\<^sub>m blinding_of \<Rightarrow> ('a\<^sub>m \<times>\<^sub>m 'b\<^sub>m) blinding_of" where
  "blinding_of_prod \<equiv> rel_prod"

lemmas blinding_of_prod_mono = prod.rel_mono

lemma blinding_of_prod_hash:
  assumes "boa \<le> vimage2p rha rha (=)" "bob \<le> vimage2p rhb rhb (=)"
  shows "blinding_of_prod boa bob \<le> vimage2p (hash_prod rha rhb) (hash_prod rha rhb) (=)"
  using assms by(auto simp add: vimage2p_def)

lemma blinding_of_on_prod [locale_witness]:
  assumes "blinding_of_on A rha boa" "blinding_of_on B rhb bob"
  shows "blinding_of_on {x. fsts x \<subseteq> A \<and> snds x \<subseteq> B} (hash_prod rha rhb) (blinding_of_prod boa bob)"
  (is "blinding_of_on ?A ?h ?bo")
proof -
  interpret a: blinding_of_on A rha boa by fact
  interpret b: blinding_of_on B rhb bob by fact
  show ?thesis
  proof
    show "?bo x x" if "x \<in> ?A" for x using that by(cases x)(auto intro: a.refl b.refl)
    show "?bo x z" if "?bo x y" "?bo y z" "x \<in> ?A" for x y z using that
      by(auto elim!: rel_prod.cases dest: a.trans b.trans)
    show "x = y" if "?bo x y" "?bo y x" "x \<in> ?A" for x y using that
      by(auto elim!: rel_prod.cases dest: a.antisym b.antisym)
  qed(rule blinding_of_prod_hash a.hash b.hash)+
qed

lemmas blinding_of_prod [locale_witness] = blinding_of_on_prod[where A=UNIV and B=UNIV, simplified]

(************************************************************)
subsubsection \<open> Merging \<close>
(************************************************************)

context
  fixes ma :: "'a\<^sub>m merge"
  fixes mb :: "'b\<^sub>m merge"
begin

fun merge_prod :: "('a\<^sub>m \<times>\<^sub>m 'b\<^sub>m) merge" where
  "merge_prod (x, y) (x', y') = Option.bind (ma x x') (\<lambda>x''. map_option (Pair x'') (mb y y'))"

lemma merge_on_prod [locale_witness]:
  assumes "merge_on A rha boa ma" "merge_on B rhb bob mb"
  shows "merge_on {x. fsts x \<subseteq> A \<and> snds x \<subseteq> B} (hash_prod rha rhb) (blinding_of_prod boa bob) merge_prod"
  (is "merge_on ?A ?h ?bo ?m")
proof -
  interpret a: merge_on A rha boa ma by fact
  interpret b: merge_on B rhb bob mb by fact
  show ?thesis
  proof
    show "\<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and> (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u)"
      if "?h a = ?h b" "a \<in> ?A" for a b using that
      by(cases "(a, b)" rule: merge_prod.cases)(auto dest!: a.join b.join)
    show "?m a b = None" if "?h a \<noteq> ?h b" "a \<in> ?A" for a b using that
      by(cases "(a, b)" rule: merge_prod.cases)(auto dest!: a.undefined b.undefined)
  qed
qed

lemmas merge_prod [locale_witness] = merge_on_prod[where A=UNIV and B=UNIV, simplified]

lemma merge_prod_alt_def:
  "merge_prod = (\<lambda>(x, y) (x', y'). Option.bind (ma x x') (\<lambda>x''. map_option (Pair x'') (mb y y')))"
  by(simp add: fun_eq_iff)

end

lemma merge_prod_cong[fundef_cong]:
  assumes "\<And>a b. \<lbrakk> a \<in> fsts p1; b \<in> fsts p2 \<rbrakk> \<Longrightarrow> ma a b = ma' a b"
    and "\<And>a b. \<lbrakk> a \<in> snds p1; b \<in> snds p2 \<rbrakk> \<Longrightarrow> mb a b = mb' a b" 
  shows "merge_prod ma mb p1 p2 = merge_prod ma' mb' p1 p2"
  using assms by(cases p1; cases p2) auto

parametric_constant merge_prod_parametric [transfer_rule]: merge_prod_alt_def

(************************************************************)
subsubsection \<open> Merkle Interface \<close>
(************************************************************)

lemma merkle_product [locale_witness]:
  assumes "merkle_interface rha boa ma" "merkle_interface rhb bob mb"
  shows "merkle_interface (hash_prod rha rhb) (blinding_of_prod boa bob) (merge_prod ma mb)"
proof -
  interpret a: merge_on UNIV rha boa ma unfolding merkle_interface_aux[symmetric] by fact
  interpret b: merge_on UNIV rhb bob mb unfolding merkle_interface_aux[symmetric] by fact
  show ?thesis unfolding merkle_interface_aux[symmetric] ..
qed


(************************************************************)
subsection \<open>Building Block: Lists\<close>
(************************************************************)

text \<open>The ADS construction on lists is done the easiest through a separate isomorphic datatype
  that has only a single constructor. We hide this construction in a locale. \<close>

locale list_R1 begin

type_synonym ('a, 'b) list_F = "unit + 'a \<times> 'b"

abbreviation (input) "set_base_F\<^sub>m \<equiv> \<lambda>x. setr x \<bind> fsts"
abbreviation (input) "set_rec_F\<^sub>m \<equiv> \<lambda>A. setr A \<bind> snds"
abbreviation (input) "map_F \<equiv> \<lambda>fb fr. map_sum id (map_prod fb fr)"

datatype 'a list_R1 = list_R1 (unR: "('a, 'a list_R1) list_F")

lemma list_R1_const_into_dest: "list_R1 F = l \<longleftrightarrow> F = unR l"
  by auto

declare list_R1.split[split]

lemma list_R1_induct[case_names list_R1]:
  assumes "\<And>F. \<lbrakk> \<And>l'. l' \<in> set_rec_F\<^sub>m F  \<Longrightarrow> P l' \<rbrakk> \<Longrightarrow> P (list_R1 F)"
  shows "P l"  
  apply(rule list_R1.induct)
  apply(auto intro!: assms)
  done

lemma set_list_R1_eq: 
  "{x. set_base_F\<^sub>m x \<subseteq> A \<and> set_rec_F\<^sub>m x \<subseteq> B} =
   {x. setl x \<subseteq> UNIV \<and> setr x \<subseteq> {x. fsts x \<subseteq> A \<and> snds x \<subseteq> B}}"
  by(auto simp add: bind_UNION)

(************************************************************)
subsubsection \<open> The Isomorphism \<close>
(************************************************************)

primrec (transfer) list_R1_to_list :: "'a list_R1 \<Rightarrow> 'a list" where
  "list_R1_to_list (list_R1 l) = (case map_sum id (map_prod id list_R1_to_list) l of Inl () \<Rightarrow> [] | Inr (x, xs) \<Rightarrow> x # xs)"

lemma list_R1_to_list_simps [simp]:
  "list_R1_to_list (list_R1 (Inl ())) = []"
  "list_R1_to_list (list_R1 (Inr (x, xs))) = x # list_R1_to_list xs"
  by(simp_all split: unit.split)

declare list_R1_to_list.simps [simp del]

primrec (transfer) list_to_list_R1 :: "'a list \<Rightarrow> 'a list_R1" where
  "list_to_list_R1 [] = list_R1 (Inl ())"
| "list_to_list_R1 (x#xs) = list_R1 (Inr (x, list_to_list_R1 xs))"

lemma R1_of_list: "list_R1_to_list (list_to_list_R1 x) = x"
  by(induct x) (auto)

lemma list_of_R1: "list_to_list_R1 (list_R1_to_list x) = x"
  apply(induct x)
  subgoal for x
    by(cases x) (auto)
  done

lemma list_R1_def: "type_definition list_to_list_R1 list_R1_to_list UNIV"
  by(unfold_locales)(auto intro: R1_of_list list_of_R1)

setup_lifting list_R1_def

lemma map_list_R1_list_to_list_R1: "map_list_R1 f (list_to_list_R1 xs) = list_to_list_R1 (map f xs)"
  by(induction xs) auto

lemma list_R1_map_trans [transfer_rule]: includes lifting_syntax shows
  "(((=) ===> (=)) ===> pcr_list (=) ===> pcr_list (=)) map_list_R1 map"
  by(auto 4 3 simp add: list.pcr_cr_eq rel_fun_eq cr_list_def map_list_R1_list_to_list_R1)

lemma set_list_R1_list_to_list_R1: "set_list_R1 (list_to_list_R1 xs) = set xs"
  by(induction xs) auto

lemma list_R1_set_trans [transfer_rule]: includes lifting_syntax shows
  "(pcr_list (=) ===> (=)) set_list_R1 set"
  by(auto simp add: list.pcr_cr_eq cr_list_def set_list_R1_list_to_list_R1)

lemma rel_list_R1_list_to_list_R1:
   "rel_list_R1 R (list_to_list_R1 xs) (list_to_list_R1 ys) \<longleftrightarrow> list_all2 R xs ys"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  define xs' and ys' where "xs' = list_to_list_R1 xs" and "ys' = list_to_list_R1 ys"
  assume "rel_list_R1 R xs' ys'"
  then have "list_all2 R (list_R1_to_list xs') (list_R1_to_list ys')"
    by induction(auto elim!: rel_sum.cases)
  thus ?rhs by(simp add: xs'_def ys'_def R1_of_list)
next
  show ?lhs if ?rhs using that by induction auto
qed

lemma list_R1_rel_trans[transfer_rule]: includes lifting_syntax shows
  "(((=) ===> (=) ===> (=)) ===> pcr_list (=) ===> pcr_list (=) ===> (=)) rel_list_R1 list_all2"
  by(auto 4 4 simp add: list.pcr_cr_eq rel_fun_eq cr_list_def rel_list_R1_list_to_list_R1)

(************************************************************)
subsubsection \<open> Hashes \<close>
(************************************************************)

type_synonym ('a\<^sub>h, 'b\<^sub>h) list_F\<^sub>h = "unit +\<^sub>h 'a\<^sub>h \<times>\<^sub>h 'b\<^sub>h"

type_synonym ('a\<^sub>m, 'b\<^sub>m) list_F\<^sub>m = "unit +\<^sub>m 'a\<^sub>m \<times>\<^sub>m 'b\<^sub>m"

type_synonym 'a\<^sub>h list_R1\<^sub>h = "'a\<^sub>h list_R1" 
  \<comment> \<open>In theory, we should define a separate datatype here of the functor @{typ "('a\<^sub>h, _) list_F\<^sub>h"}.
    We take a shortcut because they're isomorphic.\<close>

type_synonym 'a\<^sub>m list_R1\<^sub>m = "'a\<^sub>m list_R1"
  \<comment> \<open>In theory, we should define a separate datatype here of the functor @{typ "('a\<^sub>m, _) list_F\<^sub>m"}.
    We take a shortcut because they're isomorphic.\<close>

definition hash_F :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> ('b\<^sub>m, 'b\<^sub>h) hash \<Rightarrow> (('a\<^sub>m, 'b\<^sub>m) list_F\<^sub>m, ('a\<^sub>h, 'b\<^sub>h) list_F\<^sub>h) hash" where 
  "hash_F h rhL = hash_sum hash_unit (hash_prod h rhL)"

abbreviation (input) hash_R1 :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> ('a\<^sub>m list_R1\<^sub>m, 'a\<^sub>h list_R1\<^sub>h) hash" where
  "hash_R1 \<equiv> map_list_R1"

parametric_constant hash_F_parametric[transfer_rule]: hash_F_def

(************************************************************)
subsubsection \<open> Blinding \<close>
(************************************************************)

definition blinding_of_F :: "'a\<^sub>m blinding_of \<Rightarrow> 'b\<^sub>m blinding_of \<Rightarrow> ('a\<^sub>m, 'b\<^sub>m) list_F\<^sub>m blinding_of" where
  "blinding_of_F bo bL = blinding_of_sum blinding_of_unit (blinding_of_prod bo bL)"
 
abbreviation (input) blinding_of_R1 :: "'a blinding_of \<Rightarrow> 'a list_R1 blinding_of" where
  "blinding_of_R1 \<equiv> rel_list_R1"

lemma blinding_of_hash_R1:
  assumes "bo \<le> vimage2p h h (=)"
  shows "blinding_of_R1 bo \<le> vimage2p (hash_R1 h) (hash_R1 h) (=)"
  apply(rule predicate2I vimage2pI)+
  apply(auto simp add: predicate2D_vimage2p[OF assms] elim!: list_R1.rel_induct rel_sum.cases rel_prod.cases)
  done

lemma blinding_of_on_R1 [locale_witness]:
  assumes "blinding_of_on A h bo"
  shows "blinding_of_on {x. set_list_R1 x \<subseteq> A} (hash_R1 h) (blinding_of_R1 bo)"
  (is "blinding_of_on ?A ?h ?bo")
proof -
  interpret a: blinding_of_on A h bo by fact
  show ?thesis
  proof
    show hash: "?bo \<le> vimage2p ?h ?h (=)" using a.hash by(rule blinding_of_hash_R1)

    have "?bo x x \<and> (?bo x y \<longrightarrow> ?bo y z \<longrightarrow> ?bo x z) \<and> (?bo x y \<longrightarrow> ?bo y x \<longrightarrow> x = y)" if "x \<in> ?A" for x y z using that
    proof(induction x arbitrary: y z)
      case (list_R1 x y' z')
      from list_R1.prems have s1: "set_base_F\<^sub>m x \<subseteq> A" by(fastforce)
      from list_R1.prems have s3: "set_rec_F\<^sub>m x \<bind> set_list_R1 \<subseteq> A" by(fastforce intro: rev_bexI)
     
      interpret F: blinding_of_on "{y. set_base_F\<^sub>m y \<subseteq> A \<and> set_rec_F\<^sub>m y \<subseteq> set_rec_F\<^sub>m x}"
        "hash_F h (hash_R1 h)" "blinding_of_F bo (blinding_of_R1 bo)"
        unfolding hash_F_def blinding_of_F_def set_list_R1_eq
      proof
        let ?A' = "setr x \<bind> snds" and ?bo' = "rel_list_R1 bo"
        show "?bo' x x" if "x \<in> ?A'" for x using that list_R1 by(force simp add: eq_onp_def)
        show "?bo' x z" if "?bo' x y" "?bo' y z" "x \<in> ?A'" for x y z 
          using that list_R1.IH[of _ x y z] list_R1.prems
          by(force simp add: bind_UNION prod_set_defs)
        show "x = y" if "?bo' x y" "?bo' y x" "x \<in> ?A'" for x y
          using that list_R1.IH[of _ x y] list_R1.prems
          by(force simp add: prod_set_defs)
      qed(rule hash)
      show ?case using list_R1.prems
        apply(intro conjI)
        subgoal using F.refl[of x] s1 unfolding blinding_of_F_def by(auto intro: list_R1.rel_intros)
        subgoal using s1 by(auto elim!: list_R1.rel_cases F.trans[unfolded blinding_of_F_def] intro: list_R1.rel_intros)
        subgoal using s1 by(auto elim!: list_R1.rel_cases dest: F.antisym[unfolded blinding_of_F_def])
        done
    qed
    then show "x \<in> ?A \<Longrightarrow> ?bo x x" 
      and "\<lbrakk> ?bo x y; ?bo y z; x \<in> ?A \<rbrakk> \<Longrightarrow> ?bo x z"
      and "\<lbrakk> ?bo x y; ?bo y x; x \<in> ?A \<rbrakk> \<Longrightarrow> x = y"
      for x y z by blast+
  qed
qed

lemmas blinding_of_R1 [locale_witness] = blinding_of_on_R1[where A=UNIV, simplified]

parametric_constant blinding_of_F_parametric[transfer_rule]: blinding_of_F_def

(************************************************************)
subsubsection \<open> Merging \<close>
(************************************************************)

definition merge_F :: "'a\<^sub>m merge \<Rightarrow> 'b\<^sub>m merge \<Rightarrow> ('a\<^sub>m, 'b\<^sub>m) list_F\<^sub>m merge" where 
  "merge_F m mL = merge_sum merge_unit (merge_prod m mL)"

lemma merge_F_cong[fundef_cong]:
  assumes "\<And>a b. \<lbrakk> a \<in> set_base_F\<^sub>m x; b \<in> set_base_F\<^sub>m y \<rbrakk> \<Longrightarrow> m a b = m' a b"
    and "\<And>a b. \<lbrakk> a \<in> set_rec_F\<^sub>m x; b \<in> set_rec_F\<^sub>m y \<rbrakk> \<Longrightarrow> mL a b = mL' a b"
  shows "merge_F m mL x y = merge_F m' mL' x y"
  using assms
  apply(cases x; cases y)
     apply(simp_all add: merge_F_def)
  apply(rule arg_cong[where f="map_option _"])
  apply(blast intro: merge_prod_cong)
  done

context
  fixes m :: "'a\<^sub>m merge" 
  notes setr.simps[simp]
begin
fun merge_R1 :: "'a\<^sub>m list_R1\<^sub>m merge" where
  "merge_R1 (list_R1 l1) (list_R1 l2) = map_option list_R1 (merge_F m merge_R1 l1 l2)"
end

case_of_simps merge_cases [simp]: merge_R1.simps

lemma merge_on_R1:
  assumes "merge_on A h bo m"
  shows "merge_on {x. set_list_R1 x \<subseteq> A } (hash_R1 h) (blinding_of_R1 bo) (merge_R1 m)"
  (is "merge_on ?A ?h ?bo ?m")
proof -
  interpret a: merge_on A h bo m by fact
  show ?thesis
  proof
    have "(?h a = ?h b \<longrightarrow> (\<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and> (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u))) \<and>
      (?h a \<noteq> ?h b \<longrightarrow> ?m a b = None)"
      if "a \<in> ?A" for a b using that unfolding mem_Collect_eq
    proof(induction a arbitrary: b rule: list_R1_induct)
      case wfInd: (list_R1 l)
      interpret merge_on "{y. set_base_F\<^sub>m y \<subseteq> A \<and> set_rec_F\<^sub>m y \<subseteq> set_rec_F\<^sub>m l}"
        "hash_F h ?h" "blinding_of_F bo ?bo" "merge_F m ?m"
        unfolding set_list_R1_eq hash_F_def merge_F_def blinding_of_F_def
      proof
        fix a
        assume a: "a \<in> set_rec_F\<^sub>m l"
        with wfInd.prems have a': "set_list_R1 a \<subseteq> A"
          by fastforce

        show "hash_R1 h a = hash_R1 h b
           \<Longrightarrow> \<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and>
                    (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u)"
          and "?h a \<noteq> ?h b \<Longrightarrow> ?m a b = None" for b      
          using wfInd.IH[OF a a', rule_format, of b]
          by(auto dest: sym)
      qed
      show ?case using wfInd.prems
        apply(intro conjI strip)
        subgoal
          by(auto 4 4 dest!: join[unfolded hash_F_def]
              simp add: blinding_of_F_def UN_subset_iff list_R1.rel_sel)
        subgoal by(auto 4 3 intro!: undefined[simplified hash_F_def])
        done
    qed
    then show
      "?h a = ?h b \<Longrightarrow> \<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and> (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u)"
      "?h a \<noteq> ?h b \<Longrightarrow> ?m a b = None"
      if "a \<in> ?A" for a b using that by blast+
  qed
qed

lemmas merge_R1 [locale_witness] = merge_on_R1[where A=UNIV, simplified]

lemma merkle_list_R1 [locale_witness]:
  assumes "merkle_interface h bo m"
  shows "merkle_interface (hash_R1 h) (blinding_of_R1 bo) (merge_R1 m)"
proof -
  interpret merge_on UNIV h bo m using assms by(unfold merkle_interface_aux)
  show ?thesis unfolding merkle_interface_aux[symmetric] ..
qed

lemma merge_R1_cong [fundef_cong]:
  assumes "\<And>a b. \<lbrakk> a \<in> set_list_R1 x; b \<in> set_list_R1 y \<rbrakk> \<Longrightarrow> m a b = m' a b"
  shows "merge_R1 m x y = merge_R1 m' x y"
  using assms
  apply(induction x y rule: merge_R1.induct)
  apply(simp del: merge_cases)
  apply(rule arg_cong[where f="map_option _"])
  apply(blast intro: merge_F_cong[unfolded bind_UNION])
  done

parametric_constant merge_F_parametric[transfer_rule]: merge_F_def

lemma merge_R1_parametric [transfer_rule]:
  includes lifting_syntax 
  notes [simp del] = merge_cases
  assumes [transfer_rule]: "bi_unique A"
  shows "((A ===> A ===> rel_option A) ===> rel_list_R1 A ===> rel_list_R1 A ===> rel_option (rel_list_R1 A))
   merge_R1 merge_R1"
  apply(intro rel_funI)
  subgoal premises prems [transfer_rule] for m1 m2 xs1 xs2 ys1 ys2 using prems(2, 3)
    apply(induction xs1 ys1 arbitrary: xs2 ys2 rule: merge_R1.induct)
    apply(elim list_R1.rel_cases rel_sum.cases; clarsimp simp add: option.rel_map merge_F_def merge_discrete_def)
    apply(elim meta_allE; (erule meta_impE, simp)+)
    subgoal premises [transfer_rule] by transfer_prover
    done
  done

end

subsubsection \<open> Transferring the Constructions to Lists \<close>
type_synonym 'a\<^sub>h list\<^sub>h = "'a\<^sub>h list"
type_synonym 'a\<^sub>m list\<^sub>m = "'a\<^sub>m list"

context begin
interpretation list_R1 .

abbreviation (input) hash_list :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> ('a\<^sub>m list\<^sub>m, 'a\<^sub>h list\<^sub>h) hash"
  where "hash_list \<equiv> map"
abbreviation (input) blinding_of_list :: "'a\<^sub>m blinding_of \<Rightarrow> 'a\<^sub>m list\<^sub>m blinding_of"
  where "blinding_of_list \<equiv> list_all2"
lift_definition merge_list :: "'a\<^sub>m merge \<Rightarrow> 'a\<^sub>m list\<^sub>m merge" is merge_R1 .

lemma blinding_of_list_mono:
  "\<lbrakk> \<And>x y. bo x y \<longrightarrow> bo' x y \<rbrakk> \<Longrightarrow> 
  blinding_of_list bo x y \<longrightarrow> blinding_of_list bo' x y"
  by (transfer) (blast intro: list_R1.rel_mono_strong)

lemmas blinding_of_list_hash = blinding_of_hash_R1[Transfer.transferred]
  and blinding_of_on_list [locale_witness] = blinding_of_on_R1[Transfer.transferred]
  and blinding_of_list [locale_witness] = blinding_of_R1[Transfer.transferred]
  and merge_on_list [locale_witness] = merge_on_R1[Transfer.transferred]
  and merge_list [locale_witness] = merge_R1[Transfer.transferred]
  and merge_list_cong = merge_R1_cong[Transfer.transferred]

lemma blinding_of_list_mono_pred:
  "R \<le> R' \<Longrightarrow> blinding_of_list R \<le> blinding_of_list R'"
  by(transfer) (rule list_R1.rel_mono)

lemma blinding_of_list_simp: "blinding_of_list = list_all2"
  by(transfer) (rule refl)

lemma merkle_list [locale_witness]:
  assumes [locale_witness]: "merkle_interface h bo m"
  shows "merkle_interface (hash_list h) (blinding_of_list bo) (merge_list m)"
  by(transfer fixing: h bo m) unfold_locales

parametric_constant merge_list_parametric [transfer_rule]: merge_list_def

lifting_update list.lifting
lifting_forget list.lifting

end


(************************************************************)
subsection \<open>Building block: function space\<close>
(************************************************************)

text \<open> We prove that we can lift the ADS construction through functions.\<close>

type_synonym ('a, 'b\<^sub>h) fun\<^sub>h = "'a \<Rightarrow> 'b\<^sub>h"
type_notation fun\<^sub>h (infixr "\<Rightarrow>\<^sub>h" 0)

type_synonym ('a, 'b\<^sub>m) fun\<^sub>m = "'a \<Rightarrow> 'b\<^sub>m"
type_notation fun\<^sub>m (infixr "\<Rightarrow>\<^sub>m" 0)

(************************************************************)
subsubsection \<open> Hashes \<close>
(************************************************************)

text \<open> Only the range is live, the domain is dead like for BNFs. \<close>

abbreviation (input) hash_fun' :: "('a \<Rightarrow>\<^sub>m 'b\<^sub>h, 'a \<Rightarrow>\<^sub>h 'b\<^sub>h) hash" where
  "hash_fun' \<equiv> id"

abbreviation (input) hash_fun :: "('b\<^sub>m, 'b\<^sub>h) hash \<Rightarrow> ('a \<Rightarrow>\<^sub>m 'b\<^sub>m, 'a \<Rightarrow>\<^sub>h 'b\<^sub>h) hash"
  where "hash_fun \<equiv> comp"

(************************************************************)
subsubsection \<open> Blinding \<close>
(************************************************************)

abbreviation (input) blinding_of_fun :: "'b\<^sub>m blinding_of \<Rightarrow> ('a \<Rightarrow>\<^sub>m 'b\<^sub>m) blinding_of" where
  "blinding_of_fun \<equiv> rel_fun (=)"

lemmas blinding_of_fun_mono = fun.rel_mono

lemma blinding_of_fun_hash:
  assumes "bo \<le> vimage2p rh rh (=)"
  shows "blinding_of_fun bo \<le> vimage2p (hash_fun rh) (hash_fun rh) (=)"
  using assms by(auto simp add: vimage2p_def rel_fun_def le_fun_def)

lemma blinding_of_on_fun [locale_witness]:
  assumes "blinding_of_on A rh bo"
  shows "blinding_of_on {x. range x \<subseteq> A} (hash_fun rh) (blinding_of_fun bo)"
  (is "blinding_of_on ?A ?h ?bo")
proof -
  interpret a: blinding_of_on A rh bo by fact
  show ?thesis
  proof
    show "?bo x x" if "x \<in> ?A" for x using that by(auto simp add: rel_fun_def intro: a.refl)
    show "?bo x z" if "?bo x y" "?bo y z" "x \<in> ?A" for x y z using that
      by(auto 4 3 simp add: rel_fun_def intro: a.trans)
    show "x = y" if "?bo x y" "?bo y x" "x \<in> ?A" for x y using that
      by(fastforce simp add: fun_eq_iff rel_fun_def intro: a.antisym)
  qed(rule blinding_of_fun_hash a.hash)+
qed

lemmas blinding_of_fun [locale_witness] = blinding_of_on_fun[where A=UNIV, simplified]

(************************************************************)
subsubsection \<open> Merging \<close>
(************************************************************)

context
  fixes m :: "'b\<^sub>m merge"
begin

definition merge_fun :: "('a \<Rightarrow>\<^sub>m 'b\<^sub>m) merge" where
  "merge_fun f g = (if \<forall>x. m (f x) (g x) \<noteq> None then Some (\<lambda>x. the (m (f x) (g x))) else None)"

lemma merge_on_fun [locale_witness]:
  assumes "merge_on A rh bo m"
  shows "merge_on {x. range x \<subseteq> A} (hash_fun rh) (blinding_of_fun bo) merge_fun"
  (is "merge_on ?A ?h ?bo ?m")
proof -
  interpret a: merge_on A rh bo m by fact
  show ?thesis
  proof
    show "\<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and> (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u)"
      if "?h a = ?h b" "a \<in> ?A" for a b 
      using that(1)[THEN fun_cong, unfolded o_apply, THEN a.join, OF that(2)[unfolded mem_Collect_eq, THEN subsetD, OF rangeI]]
      by atomize(subst (asm) choice_iff; auto simp add: merge_fun_def rel_fun_def)
    show "?m a b = None" if "?h a \<noteq> ?h b" "a \<in> ?A" for a b using that
      by(auto simp add: merge_fun_def fun_eq_iff dest: a.undefined)
  qed
qed

lemmas merge_fun [locale_witness] = merge_on_fun[where A=UNIV, simplified]

end

lemma merge_fun_cong[fundef_cong]:
  assumes "\<And>a b. \<lbrakk> a \<in> range f; b \<in> range g \<rbrakk> \<Longrightarrow> m a b = m' a b"
  shows "merge_fun m f g = merge_fun m' f g"
  using assms[OF rangeI rangeI] by(clarsimp simp add: merge_fun_def)

lemma is_none_alt_def: "Option.is_none x \<longleftrightarrow> (case x of None \<Rightarrow> True | Some _ \<Rightarrow> False)"
  by(auto simp add: Option.is_none_def split: option.splits)

parametric_constant is_none_parametric [transfer_rule]: is_none_alt_def

lemma merge_fun_parametric [transfer_rule]: includes lifting_syntax shows
  "((A ===> B ===> rel_option C) ===> ((=) ===> A) ===> ((=) ===> B) ===> rel_option ((=) ===> C))
   merge_fun merge_fun"
proof(intro rel_funI)
  fix m :: "'a merge" and m' :: "'b merge" and f :: "'c \<Rightarrow> 'a" and f' :: "'c \<Rightarrow> 'b" and g :: "'c \<Rightarrow> 'a" and g' :: "'c \<Rightarrow> 'b"
  assume m: "(A ===> B ===> rel_option C) m m'"
    and f: "((=) ===> A) f f'" and g: "((=) ===> B) g g'"
  note [transfer_rule] = this
  have cond [unfolded Option.is_none_def]: "(\<forall>x. \<not> Option.is_none (m (f x) (g x))) \<longleftrightarrow> (\<forall>x. \<not> Option.is_none (m' (f' x) (g' x)))" 
    by transfer_prover
  moreover 
  have "((=) ===> C) (\<lambda>x. the (m (f x) (g x))) (\<lambda>x. the (m' (f' x) (g' x)))" if *: "\<forall>x. \<not> m (f x) (g x) = None"
  proof -
    obtain fg fg' where m: "m (f x) (g x) = Some (fg x)" and m': "m' (f' x) (g' x) = Some (fg' x)" for x
      using * *[simplified cond]
      by(simp)(subst (asm) (1 2) choice_iff; clarsimp)
    have "rel_option C (Some (fg x)) (Some (fg' x))" for x unfolding m[symmetric] m'[symmetric] by transfer_prover
    then show ?thesis by(simp add: rel_fun_def m m')
  qed
  ultimately show "rel_option ((=) ===> C) (merge_fun m f g) (merge_fun m' f' g')"
    unfolding merge_fun_def by(simp)
qed

(************************************************************)
subsubsection \<open> Merkle Interface \<close>
(************************************************************)

lemma merkle_fun [locale_witness]:
  assumes "merkle_interface rh bo m"
  shows "merkle_interface (hash_fun rh) (blinding_of_fun bo) (merge_fun m)"
proof -
  interpret a: merge_on UNIV rh bo m unfolding merkle_interface_aux[symmetric] by fact
  show ?thesis unfolding merkle_interface_aux[symmetric] ..
qed

(************************************************************)
subsection \<open>Rose trees\<close>
(************************************************************)

text \<open> 
We now define an ADS over rose trees, which is like a arbitrarily branching Merkle tree where each
node in the tree can be blinded, including the root. The number of children and the position of a
child among its siblings cannot be hidden. The construction allows to plug in further blindable
positions in the labels of the nodes.
\<close>

type_synonym ('a, 'b) rose_tree_F = "'a \<times> 'b list"

abbreviation (input) map_rose_tree_F where
  "map_rose_tree_F f1 f2 \<equiv> map_prod f1 (map f2)"
definition map_rose_tree_F_const where
  "map_rose_tree_F_const f1 f2 \<equiv> map_rose_tree_F f1 f2"

datatype 'a rose_tree = Tree "('a, 'a rose_tree) rose_tree_F"

type_synonym ('a\<^sub>h, 'b\<^sub>h) rose_tree_F\<^sub>h = "('a\<^sub>h \<times>\<^sub>h 'b\<^sub>h list\<^sub>h) blindable\<^sub>h"

datatype 'a\<^sub>h rose_tree\<^sub>h = Tree\<^sub>h "('a\<^sub>h, 'a\<^sub>h rose_tree\<^sub>h) rose_tree_F\<^sub>h"

type_synonym ('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) rose_tree_F\<^sub>m = "('a\<^sub>m \<times>\<^sub>m 'b\<^sub>m list\<^sub>m, 'a\<^sub>h \<times>\<^sub>h 'b\<^sub>h list\<^sub>h) blindable\<^sub>m"

datatype ('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m = Tree\<^sub>m "('a\<^sub>m, 'a\<^sub>h, ('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m, 'a\<^sub>h rose_tree\<^sub>h) rose_tree_F\<^sub>m"

abbreviation (input) map_rose_tree_F\<^sub>m
  :: "('ma \<Rightarrow> 'a) \<Rightarrow> ('mr \<Rightarrow> 'r) \<Rightarrow> ('ma, 'ha, 'mr, 'hr) rose_tree_F\<^sub>m \<Rightarrow> ('a, 'ha, 'r, 'hr) rose_tree_F\<^sub>m"
  where
  "map_rose_tree_F\<^sub>m f g \<equiv> map_blindable\<^sub>m (map_prod f (map g)) id"

(************************************************************)
subsubsection \<open> Hashes \<close>
(************************************************************)

abbreviation (input) hash_rt_F' 
  :: "(('a\<^sub>h, 'a\<^sub>h, 'b\<^sub>h, 'b\<^sub>h) rose_tree_F\<^sub>m, ('a\<^sub>h, 'b\<^sub>h) rose_tree_F\<^sub>h) hash"
  where
  "hash_rt_F' \<equiv> hash_blindable id"

definition hash_rt_F\<^sub>m
  :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> ('b\<^sub>m, 'b\<^sub>h) hash \<Rightarrow> 
    (('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) rose_tree_F\<^sub>m, ('a\<^sub>h, 'b\<^sub>h) rose_tree_F\<^sub>h) hash" where
  "hash_rt_F\<^sub>m h rhm \<equiv> hash_rt_F' o map_rose_tree_F\<^sub>m h rhm"

lemma hash_rt_F\<^sub>m_alt_def: "hash_rt_F\<^sub>m h rhm = hash_blindable (map_prod h (map rhm))"
  by(simp add: hash_rt_F\<^sub>m_def fun_eq_iff hash_map_blindable_simp)

primrec (transfer) hash_rt_tree'
  :: "(('a\<^sub>h, 'a\<^sub>h) rose_tree\<^sub>m, 'a\<^sub>h rose_tree\<^sub>h) hash" where
  "hash_rt_tree' (Tree\<^sub>m x) = Tree\<^sub>h (hash_rt_F' (map_rose_tree_F\<^sub>m id hash_rt_tree' x))"

definition hash_tree
  :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> (('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m, 'a\<^sub>h rose_tree\<^sub>h) hash" where
  "hash_tree h = hash_rt_tree' o map_rose_tree\<^sub>m h id"

lemma blindable\<^sub>m_map_compositionality:
  "map_blindable\<^sub>m f g o map_blindable\<^sub>m f' g' = map_blindable\<^sub>m (f o f') (g o g')"
  by(rule ext) (simp add: blindable\<^sub>m.map_comp)

lemma hash_tree_simps [simp]:
  "hash_tree h (Tree\<^sub>m x) = Tree\<^sub>h (hash_rt_F\<^sub>m h (hash_tree h) x)"
  by(simp add: hash_tree_def hash_rt_F\<^sub>m_def 
      map_prod.comp map_sum.comp rose_tree\<^sub>h.map_comp blindable\<^sub>m.map_comp
      prod.map_id0 rose_tree\<^sub>h.map_id0)

parametric_constant hash_rt_F\<^sub>m_parametric [transfer_rule]: hash_rt_F\<^sub>m_alt_def

parametric_constant hash_tree_parametric [transfer_rule]: hash_tree_def

(************************************************************)
subsubsection \<open> Blinding \<close>
(************************************************************)

abbreviation (input) blinding_of_rt_F\<^sub>m
  :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> 'a\<^sub>m blinding_of \<Rightarrow> ('b\<^sub>m, 'b\<^sub>h) hash \<Rightarrow> 'b\<^sub>m blinding_of
      \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) rose_tree_F\<^sub>m blinding_of" where
  "blinding_of_rt_F\<^sub>m ha boa hb bob \<equiv> blinding_of_blindable (hash_prod ha (map hb))
    (blinding_of_prod boa (blinding_of_list bob))"

lemma blinding_of_rt_F\<^sub>m_mono:
  "\<lbrakk> boa \<le> boa'; bob \<le> bob' \<rbrakk> \<Longrightarrow> blinding_of_rt_F\<^sub>m ha boa hb bob \<le> blinding_of_rt_F\<^sub>m ha boa' hb bob'"
  by(intro blinding_of_blindable_mono prod.rel_mono list.rel_mono)

lemma blinding_of_rt_F\<^sub>m_mono_inductive:
  assumes "\<And>x y. boa x y \<longrightarrow> boa' x y" "\<And>x y. bob x y \<longrightarrow> bob' x y"
  shows "blinding_of_rt_F\<^sub>m ha boa hb bob x y \<longrightarrow> blinding_of_rt_F\<^sub>m ha boa' hb bob' x y"
  apply(rule impI)
  apply(erule blinding_of_rt_F\<^sub>m_mono[THEN predicate2D, rotated -1])
  using assms by blast+

context
  fixes h :: "('a\<^sub>m, 'a\<^sub>h) hash" 
    and bo :: "'a\<^sub>m blinding_of"
begin

inductive blinding_of_tree :: "('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m blinding_of" where
  "blinding_of_tree (Tree\<^sub>m t1) (Tree\<^sub>m t2)" 
  if "blinding_of_rt_F\<^sub>m h bo (hash_tree h) blinding_of_tree t1 t2"
monos blinding_of_rt_F\<^sub>m_mono_inductive

end

inductive_simps blinding_of_tree_simps [simp]:
  "blinding_of_tree h bo (Tree\<^sub>m t1) (Tree\<^sub>m t2)"

lemma blinding_of_rt_F\<^sub>m_hash:
  assumes "boa \<le> vimage2p ha ha (=)" "bob \<le> vimage2p hb hb (=)"
  shows "blinding_of_rt_F\<^sub>m ha boa hb bob \<le> vimage2p (hash_rt_F\<^sub>m ha hb) (hash_rt_F\<^sub>m ha hb) (=)"
  apply(rule order_trans)
   apply(rule blinding_of_blindable_hash)
   apply(fold relator_eq)
   apply(unfold vimage2p_map_rel_prod vimage2p_map_list_all2)
   apply(rule prod.rel_mono assms list.rel_mono)+
  apply(simp only: hash_rt_F\<^sub>m_def vimage2p_comp o_apply hash_blindable_def blindable\<^sub>m.map_id0 id_def[symmetric] vimage2p_id id_apply)
  done

lemma blinding_of_tree_hash:
  assumes "bo \<le> vimage2p h h (=)"
  shows "blinding_of_tree h bo \<le> vimage2p (hash_tree h) (hash_tree h) (=)"
  apply(rule predicate2I vimage2pI)+
  apply(erule blinding_of_tree.induct)
  apply(simp)
  apply(erule blinding_of_rt_F\<^sub>m_hash[OF assms, THEN predicate2D_vimage2p, rotated 1])
  apply(blast intro: vimage2pI)
  done

abbreviation (input) set1_rt_F\<^sub>m :: "('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>h, 'b\<^sub>m) rose_tree_F\<^sub>m \<Rightarrow> 'a\<^sub>m set" where
  "set1_rt_F\<^sub>m x \<equiv> set1_blindable\<^sub>m x \<bind> fsts"

abbreviation (input) set3_rt_F\<^sub>m :: "('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) rose_tree_F\<^sub>m \<Rightarrow> 'b\<^sub>m set" where 
  "set3_rt_F\<^sub>m x \<equiv> (set1_blindable\<^sub>m x \<bind> snds) \<bind> set"

lemma set_rt_F\<^sub>m_eq: 
  "{x. set1_rt_F\<^sub>m x \<subseteq> A \<and> set3_rt_F\<^sub>m x \<subseteq> B} = 
   {x. set1_blindable\<^sub>m x \<subseteq> {x. fsts x \<subseteq> A \<and> snds x \<subseteq> {x. set x \<subseteq> B}}}"
  by force

lemma hash_blindable_map: "hash_blindable f \<circ> map_blindable\<^sub>m g id = hash_blindable (f \<circ> g)" 
  by(rule ext) (simp add: hash_blindable_def blindable\<^sub>m.map_comp)

lemma blinding_of_on_tree [locale_witness]:
  assumes "blinding_of_on A h bo"
  shows "blinding_of_on {x. set1_rose_tree\<^sub>m x \<subseteq> A} (hash_tree h) (blinding_of_tree h bo)"
  (is "blinding_of_on ?A ?h ?bo")
proof -
  interpret a: blinding_of_on A h bo by fact
  show ?thesis
  proof
    show "?bo \<le> vimage2p ?h ?h (=)" using a.hash by(rule blinding_of_tree_hash)
    have "?bo x x \<and> (?bo x y \<longrightarrow> ?bo y z \<longrightarrow> ?bo x z) \<and> (?bo x y \<longrightarrow> ?bo y x \<longrightarrow> x = y)" if "x \<in> ?A" for x y z using that
    proof(induction x arbitrary: y z)
      case (Tree\<^sub>m x)
      have [locale_witness]: "blinding_of_on (set3_rt_F\<^sub>m x) (hash_tree h) (blinding_of_tree h bo)"
        apply unfold_locales
        subgoal by(rule blinding_of_tree_hash)(rule a.hash)
        subgoal using Tree\<^sub>m.IH Tree\<^sub>m.prems by(fastforce simp add: eq_onp_def)
        subgoal for x y z using Tree\<^sub>m.IH[of _ _ x y z] Tree\<^sub>m.prems by fastforce
        subgoal for x y using Tree\<^sub>m.IH[of _ _ x y] Tree\<^sub>m.prems by fastforce
        done
      interpret blinding_of_on
        "{a. set1_rt_F\<^sub>m a \<subseteq> A \<and> set3_rt_F\<^sub>m a \<subseteq> set3_rt_F\<^sub>m x}"
        "hash_rt_F\<^sub>m h ?h" "blinding_of_rt_F\<^sub>m h bo ?h ?bo" 
        unfolding set_rt_F\<^sub>m_eq hash_rt_F\<^sub>m_alt_def ..
      from Tree\<^sub>m.prems show ?case
        apply(intro conjI)
        subgoal by(fastforce intro!: blinding_of_tree.intros refl[unfolded hash_rt_F\<^sub>m_alt_def])
        subgoal by(fastforce elim!: blinding_of_tree.cases trans[unfolded hash_rt_F\<^sub>m_alt_def] 
                    intro!: blinding_of_tree.intros)
        subgoal by(fastforce elim!: blinding_of_tree.cases antisym[unfolded hash_rt_F\<^sub>m_alt_def])
        done
    qed
    then show "x \<in> ?A \<Longrightarrow> ?bo x x"
      and "\<lbrakk> ?bo x y; ?bo y z; x \<in> ?A \<rbrakk> \<Longrightarrow> ?bo x z"
      and "\<lbrakk> ?bo x y; ?bo y x; x \<in> ?A \<rbrakk> \<Longrightarrow> x = y"
      for x y z by blast+
  qed
qed

lemmas blinding_of_tree [locale_witness] = blinding_of_on_tree[where A=UNIV, simplified]

lemma blinding_of_tree_mono:
  "bo \<le> bo' \<Longrightarrow> blinding_of_tree h bo \<le> blinding_of_tree h bo'"
  apply(rule predicate2I)
  apply(erule blinding_of_tree.induct)
  apply(rule blinding_of_tree.intros)
  apply(erule blinding_of_rt_F\<^sub>m_mono[THEN predicate2D, rotated -1])
  apply(blast)+
  done

(************************************************************)
subsubsection \<open> Merging \<close>
(************************************************************)

definition merge_rt_F\<^sub>m 
  :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> 'a\<^sub>m merge \<Rightarrow> ('b\<^sub>m, 'b\<^sub>h) hash \<Rightarrow> 'b\<^sub>m merge \<Rightarrow>
      ('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) rose_tree_F\<^sub>m merge"
  where
  "merge_rt_F\<^sub>m ha ma hr mr \<equiv> merge_blindable (hash_prod ha (hash_list hr)) (merge_prod ma (merge_list mr))"

lemma merge_rt_F\<^sub>m_cong [fundef_cong]:
  assumes "\<And>a b. \<lbrakk> a \<in> set1_rt_F\<^sub>m x; b \<in> set1_rt_F\<^sub>m y \<rbrakk> \<Longrightarrow> ma a b = ma' a b"
    and "\<And>a b. \<lbrakk> a \<in> set3_rt_F\<^sub>m x; b \<in> set3_rt_F\<^sub>m y \<rbrakk> \<Longrightarrow> mm a b = mm' a b"
  shows "merge_rt_F\<^sub>m ha ma hm mm x y = merge_rt_F\<^sub>m ha ma' hm mm' x y"
  using assms
  apply(cases x; cases y; simp add: merge_rt_F\<^sub>m_def bind_UNION)
  apply(rule arg_cong[where f="map_option _"])
  apply(blast intro: merge_prod_cong merge_list_cong)
  done

lemma in_set1_blindable\<^sub>m_iff: "x \<in> set1_blindable\<^sub>m y \<longleftrightarrow> y = Unblinded x"
  by(cases y) auto

context 
  fixes h :: "('a\<^sub>m, 'a\<^sub>h) hash"
    and ma :: "'a\<^sub>m merge"
  notes in_set1_blindable\<^sub>m_iff[simp]
begin
fun merge_tree :: "('a\<^sub>m, 'a\<^sub>h) rose_tree\<^sub>m merge" where
  "merge_tree (Tree\<^sub>m x) (Tree\<^sub>m y) = map_option Tree\<^sub>m (
    merge_rt_F\<^sub>m h ma (hash_tree h) merge_tree x y)"
end

lemma merge_on_tree [locale_witness]:
  assumes "merge_on A h bo m"
  shows "merge_on {x. set1_rose_tree\<^sub>m x \<subseteq> A} (hash_tree h) (blinding_of_tree h bo) (merge_tree h m)"
  (is "merge_on ?A ?h ?bo ?m")
proof -
  interpret a: merge_on A h bo m by fact
  show ?thesis 
  proof
    have "(?h a = ?h b \<longrightarrow> (\<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and> (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u))) \<and>
      (?h a \<noteq> ?h b \<longrightarrow> ?m a b = None)"
      if "a \<in> ?A" for a b using that unfolding mem_Collect_eq
    proof(induction a arbitrary: b rule: rose_tree\<^sub>m.induct)
      case (Tree\<^sub>m x y)
      interpret merge_on 
        "{y. set1_rt_F\<^sub>m y \<subseteq> A \<and> set3_rt_F\<^sub>m y \<subseteq> set3_rt_F\<^sub>m x}"
        "hash_rt_F\<^sub>m h ?h"
        "blinding_of_rt_F\<^sub>m h bo ?h ?bo"
        "merge_rt_F\<^sub>m h m ?h ?m"
        unfolding set_rt_F\<^sub>m_eq hash_rt_F\<^sub>m_alt_def merge_rt_F\<^sub>m_def
      proof
        fix a
        assume a: "a \<in> set3_rt_F\<^sub>m x"
        with Tree\<^sub>m.prems have a': "set1_rose_tree\<^sub>m a \<subseteq> A"
          by(force simp add: bind_UNION)

        from a obtain l and ab where a'': "ab \<in> set1_blindable\<^sub>m x" "l \<in> snds ab" "a \<in> set l" 
          by(clarsimp simp add: bind_UNION)

        fix b
        from Tree\<^sub>m.IH[OF a'' a', rule_format, of b]
        show "hash_tree h a = hash_tree h b
           \<Longrightarrow> \<exists>ab. merge_tree h m a b = Some ab \<and> blinding_of_tree h bo a ab \<and> blinding_of_tree h bo b ab \<and>
                    (\<forall>u. blinding_of_tree h bo a u \<longrightarrow> blinding_of_tree h bo b u \<longrightarrow> blinding_of_tree h bo ab u)"
          and "hash_tree h a \<noteq> hash_tree h b \<Longrightarrow> merge_tree h m a b = None"
          by(auto dest: sym)
      qed
      show ?case using Tree\<^sub>m.prems
        apply(intro conjI strip)
        subgoal by(cases y)(fastforce dest!: join simp add: blinding_of_tree.simps)
        subgoal by (cases y) (fastforce dest!: undefined)
        done
    qed
    then show
      "?h a = ?h b \<Longrightarrow> \<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and> (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u)"
      "?h a \<noteq> ?h b \<Longrightarrow> ?m a b = None"
      if "a \<in> ?A" for a b using that by blast+
  qed
qed

lemmas merge_tree [locale_witness] = merge_on_tree[where A=UNIV, simplified]

lemma option_bind_comm:
 "((x :: 'a option) \<bind> (\<lambda>y. c \<bind> (\<lambda>z. f y z))) = (c \<bind> (\<lambda>y. x \<bind> (\<lambda>z. f z y)))"
  by(cases x; cases c; auto)

parametric_constant merge_rt_F\<^sub>m_parametric [transfer_rule]: merge_rt_F\<^sub>m_def

(************************************************************) 
subsubsection \<open>Merkle interface\<close>
(************************************************************)

lemma merkle_tree [locale_witness]:
  assumes "merkle_interface h bo m"
  shows "merkle_interface (hash_tree h) (blinding_of_tree h bo) (merge_tree h m)"
proof -
  interpret merge_on UNIV h bo m using assms unfolding merkle_interface_aux .
  show ?thesis unfolding merkle_interface_aux[symmetric] ..
qed

lemma merge_tree_cong [fundef_cong]:
  assumes "\<And>a b. \<lbrakk> a \<in> set1_rose_tree\<^sub>m x; b \<in> set1_rose_tree\<^sub>m y \<rbrakk> \<Longrightarrow> m a b = m' a b"
  shows "merge_tree h m x y = merge_tree h m' x y"
  using assms
  apply(induction x y rule: merge_tree.induct)
  apply(simp add: bind_UNION)
  apply(rule arg_cong[where f="map_option _"])
  apply(rule merge_rt_F\<^sub>m_cong; simp add: bind_UNION; blast)
  done

end
