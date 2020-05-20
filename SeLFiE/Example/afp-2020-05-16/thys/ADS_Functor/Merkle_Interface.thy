(* Author: Andreas Lochbihler, Digital Asset
   Author: Ognjen Maric, Digital Asset *)

theory Merkle_Interface
imports
  Main
  "HOL-Library.Conditional_Parametricity"
  "HOL-Library.Monad_Syntax"
begin

alias vimage2p = BNF_Def.vimage2p
alias Grp = BNF_Def.Grp
alias setl = Basic_BNFs.setl
alias setr = Basic_BNFs.setr
alias fsts = Basic_BNFs.fsts
alias snds = Basic_BNFs.snds

attribute_setup locale_witness = \<open>Scan.succeed Locale.witness_add\<close>

lemma vimage2p_mono': "R \<le> S \<Longrightarrow> vimage2p f g R \<le> vimage2p f g S"
  by(auto simp add: vimage2p_def le_fun_def)

lemma vimage2p_map_rel_prod: 
  "vimage2p (map_prod f g) (map_prod f' g') (rel_prod A B) = rel_prod (vimage2p f f' A) (vimage2p g g' B)"
  by(simp add: vimage2p_def prod.rel_map)

lemma vimage2p_map_list_all2:
  "vimage2p (map f) (map g) (list_all2 A) = list_all2 (vimage2p f g A)"
  by(simp add: vimage2p_def list.rel_map)

lemma equivclp_least:
  assumes le: "r \<le> s" and s: "equivp s"
  shows "equivclp r \<le> s"
  apply(rule predicate2I)
  subgoal by(induction rule: equivclp_induct)(auto 4 3 intro: equivp_reflp[OF s] equivp_transp[OF s] equivp_symp[OF s] le[THEN predicate2D])
  done

lemma reflp_eq_onp: "reflp R \<longleftrightarrow> eq_onp (\<lambda>x. True) \<le> R"
  by(auto simp add: reflp_def eq_onp_def)

lemma eq_onpE:
  assumes "eq_onp P x y"
  obtains "x = y" "P y"
  using assms by(auto simp add: eq_onp_def)

lemma case_unit_parametric [transfer_rule]: "rel_fun A (rel_fun (=) A) case_unit case_unit"
  by(simp add: rel_fun_def split: unit.split)


(************************************************************)
section \<open>Authenticated Data Structures\<close>
(************************************************************)

(************************************************************)
subsection \<open>Interface\<close>
(************************************************************)

(************************************************************)
subsubsection \<open> Types \<close>
(************************************************************)

type_synonym ('a\<^sub>m, 'a\<^sub>h) hash = "'a\<^sub>m \<Rightarrow> 'a\<^sub>h" \<comment> \<open>Type of hash operation\<close>
type_synonym 'a\<^sub>m blinding_of = "'a\<^sub>m \<Rightarrow> 'a\<^sub>m \<Rightarrow> bool"
type_synonym 'a\<^sub>m merge = "'a\<^sub>m \<Rightarrow> 'a\<^sub>m \<Rightarrow> 'a\<^sub>m option" \<comment> \<open> merging that can fail for values with different hashes\<close>

(************************************************************)
subsubsection \<open> Properties \<close>
(************************************************************)

locale merkle_interface =
  fixes h :: "('a\<^sub>m, 'a\<^sub>h) hash"
    and bo :: "'a\<^sub>m blinding_of"
    and m :: "'a\<^sub>m merge"
  assumes merge_respects_hashes: "h a = h b \<longleftrightarrow> (\<exists>ab. m a b = Some ab)"
    and idem: "m a a = Some a"
    and commute: "m a b = m b a"
    and assoc: "m a b \<bind> m c = m b c \<bind> m a"
    and bo_def: "bo a b \<longleftrightarrow> m a b = Some b"
begin

lemma reflp: "reflp bo"
  unfolding bo_def by(rule reflpI)(simp add: idem)

lemma antisymp: "antisymp bo"
  unfolding bo_def by(rule antisympI)(simp add: commute)

lemma transp: "transp bo"
  apply(rule transpI)
  subgoal for x y z using assoc[of x y z] by(simp add: commute bo_def)
  done

lemma hash: "bo \<le> vimage2p h h (=)"
  unfolding bo_def by(auto simp add: vimage2p_def merge_respects_hashes)

lemma join: "m a b = Some ab \<longleftrightarrow> bo a ab \<and> bo b ab \<and> (\<forall>u. bo a u \<longrightarrow> bo b u \<longrightarrow> bo ab u)"
  unfolding bo_def
  by (smt Option.bind_cong bind.bind_lunit commute idem merkle_interface.assoc merkle_interface_axioms)

text \<open>The equivalence closure of the blinding relation are the equivalence classes of the hash function (the kernel).\<close>

lemma equivclp_blinding_of: "equivclp bo = vimage2p h h (=)" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs" by(rule equivclp_least[OF hash])(rule equivp_vimage2p[OF identity_equivp])
  show "?rhs \<le> ?lhs" unfolding vimage2p_def
  proof(rule predicate2I)
    fix x y
    assume "h x = h y"
    then obtain xy where "m x y = Some xy" unfolding merge_respects_hashes ..
    hence "bo x xy" "bo y xy" unfolding join by blast+
    hence "equivclp bo x xy" "equivclp bo xy y" by(blast)+
    thus "equivclp bo x y" by(rule equivclp_trans)
  qed
qed

end

(************************************************************)
subsection \<open> Auxiliary definitions \<close>
(************************************************************)

text \<open> Directly proving that an interface satisfies the specification of a Merkle interface as given
above is difficult. Instead, we provide several layers of auxiliary definitions that can easily be
proved layer-by-layer. 

In particular, proving that an interface on recursive datatypes is a Merkle interface requires
induction. As the induction hypothesis only applies to a subset of values of a type, we add
auxiliary definitions equipped with an explicit set @{term A} of values to which the definition
applies. Once the induction proof is complete, we can typically instantiate @{term A} with @{term
UNIV}. In particular, in the induction proof for a layer, we can assume that properties for the
earlier layers hold for \<^emph>\<open>all\<close> values, not just those in the induction hypothesis.
\<close>

(************************************************************)
subsubsection \<open> Blinding \<close>
(************************************************************)
locale blinding_respects_hashes =
  fixes h :: "('a\<^sub>m, 'a\<^sub>h) hash"
    and bo :: "'a\<^sub>m blinding_of"
  assumes hash: "bo \<le> vimage2p h h (=)"
begin

lemma blinding_hash_eq: "bo x y \<Longrightarrow> h x = h y"
  by(drule hash[THEN predicate2D])(simp add: vimage2p_def)

end

locale blinding_of_on =
  blinding_respects_hashes h bo
    for A :: "'a\<^sub>m set"
    and h :: "('a\<^sub>m, 'a\<^sub>h) hash"
    and bo :: "'a\<^sub>m blinding_of"
  + assumes refl: "x \<in> A \<Longrightarrow> bo x x"
    and trans: "\<lbrakk> bo x y; bo y z; x \<in> A \<rbrakk> \<Longrightarrow> bo x z"
    and antisym: "\<lbrakk> bo x y; bo y x; x \<in> A \<rbrakk> \<Longrightarrow> x = y"
begin

lemma refl_pointfree: "eq_onp (\<lambda>x. x \<in> A) \<le> bo"
  by(auto elim!: eq_onpE intro: refl)

lemma blinding_respects_hashes: "blinding_respects_hashes h bo" ..
lemmas hash = hash

lemma trans_pointfree: "eq_onp (\<lambda>x. x \<in> A) OO bo OO bo \<le> bo"
  by(auto elim!: eq_onpE intro: trans)

lemma antisym_pointfree: "inf (eq_onp (\<lambda>x. x \<in> A) OO bo) bo\<inverse>\<inverse> \<le> (=)"
  by(auto elim!: eq_onpE dest: antisym)

end

(************************************************************)
subsubsection \<open> Merging \<close>
(************************************************************)

text \<open> In general, we prove the properties of blinding before the properties of merging. Thus,
  in the following definitions we assume that the blinding properties already hold on @{term UNIV}.
  The @{term Ball} restricts the argument of the merge operation on which induction will be done. \<close>

locale merge_on =
  blinding_of_on UNIV h bo
    for A :: "'a\<^sub>m set"
    and h :: "('a\<^sub>m, 'a\<^sub>h) hash"
    and bo :: "'a\<^sub>m blinding_of" 
    and m :: "'a\<^sub>m merge" +
  assumes join: "\<lbrakk> h a = h b; a \<in> A \<rbrakk> 
      \<Longrightarrow> \<exists>ab. m a b = Some ab \<and> bo a ab \<and> bo b ab \<and> (\<forall>u. bo a u \<longrightarrow> bo b u \<longrightarrow> bo ab u)"
    and undefined: "\<lbrakk> h a \<noteq> h b; a \<in> A \<rbrakk> \<Longrightarrow> m a b = None"
begin

lemma same: "a \<in> A \<Longrightarrow> m a a = Some a"
  using join[of a a] refl[of a] by(auto 4 3 intro: antisym)

lemma blinding_of_antisym_on: "blinding_of_on UNIV h bo" ..

lemma transp: "transp bo"
  by(auto intro: transpI trans)

lemmas hash = hash
  and refl = refl
  and antisym = antisym[OF _ _ UNIV_I]

lemma respects_hashes:
  "a \<in> A \<Longrightarrow> h a = h b \<longleftrightarrow> (\<exists>ab. m a b = Some ab)"
  using join undefined
  by fastforce

lemma join':
  "a \<in> A \<Longrightarrow> \<forall>ab. m a b = Some ab \<longleftrightarrow> bo a ab \<and> bo b ab \<and> (\<forall>u. bo a u \<longrightarrow> bo b u \<longrightarrow> bo ab u)"
  using join undefined
  by (metis (full_types) hash local.antisym option.distinct(1) option.sel predicate2D vimage2p_def)

lemma merge_on_subset:
  "B \<subseteq> A \<Longrightarrow> merge_on B h bo m"
  by unfold_locales (auto dest: same join undefined)

end

subsection \<open> Interface equality \<close>

text \<open> Here, we prove that the auxiliary definitions specify the same interface as the original ones.\<close>

lemma merkle_interface_aux: "merkle_interface h bo m = merge_on UNIV h bo m" 
  (is "?lhs = ?rhs")
proof
  show ?rhs if ?lhs
  proof
    interpret merkle_interface h bo m by(fact that)
    show "bo \<le> vimage2p h h (=)" by(fact hash)
    show "bo x x" for x using reflp by(simp add: reflp_def)
    show "bo x z" if "bo x y" "bo y z" for x y z using transp that by(rule transpD)
    show "x = y" if "bo x y" "bo y x" for x y using antisymp that by(rule antisympD)
    show "\<exists>ab. m a b = Some ab \<and> bo a ab \<and> bo b ab \<and> (\<forall>u. bo a u \<longrightarrow> bo b u \<longrightarrow> bo ab u)" if "h a = h b" for a b
      using that by(simp add: merge_respects_hashes join)
    show "m a b = None" if "h a \<noteq> h b" for a b using that by(simp add: merge_respects_hashes)
  qed

  show ?lhs if ?rhs
  proof
    interpret merge_on UNIV h bo m by(fact that)
    show eq: "h a = h b \<longleftrightarrow> (\<exists>ab. m a b = Some ab)" for a b by(simp add: respects_hashes)
    show idem: "m a a = Some a" for a by(simp add: same)
    show commute: "m a b = m b a" for a b 
      using join[of a b] join[of b a] undefined antisym by(cases "m a b") force+
    have undefined_partitioned: "m a c = None" if "m a b = None" "m b c = Some bc" for a b c bc
      using that eq by (metis option.distinct(1) option.exhaust)
    have merge_twice: "m a b = Some c \<Longrightarrow> m a c = Some c" for a b c by (simp add: join')
    show "m a b \<bind> m c = m b c \<bind> m a" for a b c
    proof(simp split: Option.bind_split; safe)
      show "None = m a d" if "m a b = None" "m b c = Some d" for d using that
        by(metis undefined_partitioned merge_twice)
      show "m c d = None" if "m a b = Some d" "m b c = None" for d using that
        by(metis commute merge_twice undefined_partitioned)
    next
      fix ab bc
      assume assms: "m a b = Some ab" "m b c = Some bc"
      then obtain cab and abc where cab: "m c ab = Some cab" and abc: "m a bc = Some abc"
        using eq[THEN iffD2, OF exI] eq[THEN iffD1] by (metis merge_twice)
      thus "m c ab = m a bc" using assms
        by(clarsimp simp add: join')(metis UNIV_I abc cab local.antisym local.trans)
    qed
    show "bo a b \<longleftrightarrow> m a b = Some b" for a b using idem join' by auto
  qed
qed

lemma merkle_interfaceI [locale_witness]:
  assumes "merge_on UNIV h bo m"
  shows "merkle_interface h bo m"
  using assms unfolding merkle_interface_aux by auto

lemma (in merkle_interface) merkle_interfaceD: "merge_on UNIV h bo m"
  using merkle_interface_aux[of h bo m, symmetric]
  by simp unfold_locales

subsection \<open> Parametricity rules \<close>

context includes lifting_syntax begin
parametric_constant le_fun_parametric[transfer_rule]: le_fun_def
parametric_constant vimage2p_parametric[transfer_rule]: vimage2p_def
parametric_constant blinding_respects_hashes_parametric_aux: blinding_respects_hashes_def

lemma blinding_respects_hashes_parametric [transfer_rule]:
  "((A1 ===> A2) ===> (A1 ===> A1 ===> (\<longleftrightarrow>)) ===> (\<longleftrightarrow>))
   blinding_respects_hashes blinding_respects_hashes"
  if [transfer_rule]: "bi_unique A2" "bi_total A1"
  by(rule blinding_respects_hashes_parametric_aux that le_fun_parametric | simp add: rel_fun_eq)+

parametric_constant blinding_of_on_axioms_parametric [transfer_rule]:
  blinding_of_on_axioms_def[folded Ball_def, unfolded le_fun_def le_bool_def eq_onp_def relcompp.simps, simplified]
parametric_constant blinding_of_on_parametric [transfer_rule]: blinding_of_on_def
parametric_constant antisymp_parametric[transfer_rule]: antisymp_def
parametric_constant transp_parametric[transfer_rule]: transp_def

parametric_constant merge_on_axioms_parametric [transfer_rule]: merge_on_axioms_def
parametric_constant merge_on_parametric[transfer_rule]: merge_on_def

parametric_constant merkle_interface_parametric[transfer_rule]: merkle_interface_def
end

end