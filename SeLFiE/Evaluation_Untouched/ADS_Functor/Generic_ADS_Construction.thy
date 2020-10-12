(* Author: Andreas Lochbihler, Digital Asset
   Author: Ognjen Maric, Digital Asset *)

theory Generic_ADS_Construction imports
  "Merkle_Interface"
  "HOL-Library.BNF_Axiomatization"
begin

section \<open>Generic construction of authenticated data structures\<close>

subsection \<open>Functors\<close>

subsubsection \<open>Source functor\<close>

text \<open>

We want to allow ADSs of arbitrary ADTs, which we call "source trees". The ADTs we are interested in can
in general be represented as the least fixpoints of some bounded natural (bi-)functor (BNF) \<open>('a, 'b) F\<close>, where
@{typ 'a} is the type of "source" data, and @{typ 'b} is a recursion "handle".
However, Isabelle's type system does not support higher kinds, necessary to parameterize our definitions
over functors.
Instead, we first develop a general theory of ADSs over an arbitrary, but fixed functor,
and its least fixpoint. We show that the theory is compositional, in that the functor's least fixed point
can then be reused as the "source" data of another functor.

We start by defining the arbitrary fixed functor, its fixpoints, and showing how composition can be
done. A higher-level explanation is found in the paper.
\<close>


bnf_axiomatization ('a, 'b) F [wits: "'a \<Rightarrow> ('a, 'b) F"]

context notes [[typedef_overloaded]] begin
datatype 'a T = T "('a, 'a T) F"
end

subsubsection \<open>Base Merkle functor\<close>

text \<open>
This type captures the ADS hashes.
\<close>

bnf_axiomatization ('a, 'b) F\<^sub>h [wits: "'a \<Rightarrow> ('a, 'b) F\<^sub>h"]

text \<open>
It intuitively contains mixed garbage and source values.
The functor's recursive handle @{typ 'b} might contain partial garbage.
\<close>


text \<open>
This type captures the ADS inclusion proofs.
The functor \<open>('a, 'a', 'b, 'b') F\<^sub>m\<close> has all type variables doubled.
This type represents all values including the information which parts are blinded.
The original type variable @{typ 'a} now represents the source data, which for compositionality can contain blindable positions.
The type @{typ 'b} is a recursive handle to inclusion sub-proofs (which can be partialy blinded). 
The type @{typ 'a'} represent "hashes" of the source data in @{typ 'a}, i.e., a mix of source values and garbage.
The type @{typ 'b'} is a recursive handle to ADS hashes of subtrees.

The corresponding type of recursive authenticated trees is then a fixpoint of this functor.
\<close>

bnf_axiomatization ('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) F\<^sub>m [wits: "'a\<^sub>m \<Rightarrow> 'a\<^sub>h \<Rightarrow> 'b\<^sub>h \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) F\<^sub>m"]

subsubsection \<open>Least fixpoint\<close>

context notes [[typedef_overloaded]] begin
datatype 'a\<^sub>h T\<^sub>h = T\<^sub>h "('a\<^sub>h, 'a\<^sub>h T\<^sub>h) F\<^sub>h"
end

context notes [[typedef_overloaded]] begin
datatype ('a\<^sub>m, 'a\<^sub>h) T\<^sub>m = T\<^sub>m (the_T\<^sub>m: "('a\<^sub>m, 'a\<^sub>h, ('a\<^sub>m, 'a\<^sub>h) T\<^sub>m, 'a\<^sub>h T\<^sub>h) F\<^sub>m")
end


subsubsection \<open> Composition \<close>

text \<open>
Finally, we show how to compose two Merkle functors.
For simplicity, we reuse @{typ \<open>('a, 'b) F\<close>} and @{typ \<open>'a T\<close>}.
\<close>

context notes [[typedef_overloaded]] begin

datatype ('a, 'b) G = G "('a T, 'b) F"

datatype ('a\<^sub>h, 'b\<^sub>h) G\<^sub>h = G\<^sub>h (the_G\<^sub>h: "('a\<^sub>h T\<^sub>h, 'b\<^sub>h) F\<^sub>h")

datatype ('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) G\<^sub>m = G\<^sub>m (the_G\<^sub>m: "(('a\<^sub>m, 'a\<^sub>h) T\<^sub>m, 'a\<^sub>h T\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) F\<^sub>m")

end


subsection \<open>Root hash\<close>

subsubsection \<open>Base functor\<close>

text \<open>
The root hash of an authenticated value is modelled as a blindable value of type @{typ "('a', 'b') F\<^sub>h"}.
(Actually, we want to use an abstract datatype for root hashes, but we omit this distinction here for simplicity.)
\<close>

consts root_hash_F' :: "(('a\<^sub>h, 'a\<^sub>h, 'b\<^sub>h, 'b\<^sub>h) F\<^sub>m, ('a\<^sub>h, 'b\<^sub>h) F\<^sub>h) hash"
  \<comment> \<open>Root hash operation where we assume that all atoms have already been replaced by root hashes.
     This assumption is reflected in the equality of the type parameters of @{type F\<^sub>m} \<close>

type_synonym ('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) hash_F =
  "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> ('b\<^sub>m, 'b\<^sub>h) hash \<Rightarrow> (('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) F\<^sub>m, ('a\<^sub>h, 'b\<^sub>h) F\<^sub>h) hash"
definition root_hash_F :: "('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) hash_F" where
  "root_hash_F rha rhb = root_hash_F' \<circ> map_F\<^sub>m rha id rhb id"

subsubsection \<open>Least fixpoint\<close>

primrec root_hash_T' :: "(('a\<^sub>h, 'a\<^sub>h) T\<^sub>m, 'a\<^sub>h T\<^sub>h) hash" where
  "root_hash_T' (T\<^sub>m x) = T\<^sub>h (root_hash_F' (map_F\<^sub>m id id root_hash_T' id x))"

definition root_hash_T :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> (('a\<^sub>m, 'a\<^sub>h) T\<^sub>m, 'a\<^sub>h T\<^sub>h) hash" where
  "root_hash_T rha = root_hash_T' \<circ> map_T\<^sub>m rha id"

lemma root_hash_T_simps [simp]:
  "root_hash_T rha (T\<^sub>m x) = T\<^sub>h (root_hash_F rha (root_hash_T rha) x)"
  by(simp add: root_hash_T_def F\<^sub>m.map_comp root_hash_F_def T\<^sub>h.map_id0)

subsubsection \<open>Composition\<close>

primrec root_hash_G' :: "(('a\<^sub>h, 'a\<^sub>h, 'b\<^sub>h, 'b\<^sub>h) G\<^sub>m, ('a\<^sub>h, 'b\<^sub>h) G\<^sub>h) hash" where
  "root_hash_G' (G\<^sub>m x) = G\<^sub>h (root_hash_F' (map_F\<^sub>m root_hash_T' id id id x))"

definition root_hash_G :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> ('b\<^sub>m, 'b\<^sub>h) hash \<Rightarrow> (('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) G\<^sub>m, ('a\<^sub>h, 'b\<^sub>h) G\<^sub>h) hash" where
  "root_hash_G rha rhb = root_hash_G' \<circ> map_G\<^sub>m rha id rhb id"

lemma root_hash_G_unfold:
  "root_hash_G rha rhb = G\<^sub>h \<circ> root_hash_F (root_hash_T rha) rhb \<circ> the_G\<^sub>m"
  apply(rule ext)
  subgoal for x
    by(cases x)(simp add: root_hash_G_def fun_eq_iff root_hash_F_def root_hash_T_def F\<^sub>m.map_comp T\<^sub>m.map_comp o_def T\<^sub>h.map_id id_def[symmetric])
  done

lemma root_hash_G_simps [simp]:
  "root_hash_G rha rhb (G\<^sub>m x) = G\<^sub>h (root_hash_F (root_hash_T rha) rhb x)"
  by(simp add: root_hash_G_def root_hash_T_def F\<^sub>m.map_comp root_hash_F_def T\<^sub>h.map_id0)


subsection \<open>Blinding relation\<close>

text \<open>
The blinding relation determines whether one ADS value is a blinding of another.
\<close>

subsubsection \<open> Blinding on the base functor (@{type F\<^sub>m}) \<close>

type_synonym ('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) blinding_of_F =
  "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> 'a\<^sub>m blinding_of \<Rightarrow> ('b\<^sub>m, 'b\<^sub>h) hash \<Rightarrow> 'b\<^sub>m blinding_of \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) F\<^sub>m blinding_of"

\<comment> \<open> Computes whether a partially blinded ADS is a blinding of another one \<close>
axiomatization blinding_of_F :: "('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) blinding_of_F" where
  blinding_of_F_mono: "\<lbrakk> boa \<le> boa'; bob \<le> bob' \<rbrakk>
    \<Longrightarrow> blinding_of_F rha boa rhb bob \<le> blinding_of_F rha boa' rhb bob'"
    \<comment> \<open> Monotonicity must be unconditional (without the assumption @{text "blinding_of_on"}) 
         such that we can justify the recursive definition for the least fixpoint. \<close>
  and blinding_respects_hashes_F [locale_witness]:
  "\<lbrakk> blinding_respects_hashes rha boa; blinding_respects_hashes rhb bob \<rbrakk>
   \<Longrightarrow> blinding_respects_hashes (root_hash_F rha rhb) (blinding_of_F rha boa rhb bob)"
  and blinding_of_on_F [locale_witness]:
  "\<lbrakk> blinding_of_on A rha boa; blinding_of_on B rhb bob \<rbrakk>
   \<Longrightarrow> blinding_of_on {x. set1_F\<^sub>m x \<subseteq> A \<and> set3_F\<^sub>m x \<subseteq> B} (root_hash_F rha rhb) (blinding_of_F rha boa rhb bob)"

lemma blinding_of_F_mono_inductive:
  assumes a: "\<And>x y. boa x y \<longrightarrow> boa' x y"
    and b: "\<And>x y. bob x y \<longrightarrow> bob' x y"
  shows "blinding_of_F rha boa rhb bob x y \<longrightarrow> blinding_of_F rha boa' rhb bob' x y"
  using assms by(blast intro: blinding_of_F_mono[THEN predicate2D, OF predicate2I predicate2I])

subsubsection \<open> Blinding on least fixpoints \<close>

context
  fixes rh :: "('a\<^sub>m, 'a\<^sub>h) hash"
    and bo :: "'a\<^sub>m blinding_of"
begin

inductive blinding_of_T :: "('a\<^sub>m, 'a\<^sub>h) T\<^sub>m blinding_of" where
  "blinding_of_T (T\<^sub>m x) (T\<^sub>m y)" if 
  "blinding_of_F rh bo (root_hash_T rh) blinding_of_T x y"
monos blinding_of_F_mono_inductive

end

lemma blinding_of_T_mono:
  assumes "bo \<le> bo'"
  shows "blinding_of_T rh bo \<le> blinding_of_T rh bo'"
  by(rule predicate2I; erule blinding_of_T.induct)
    (blast intro: blinding_of_T.intros blinding_of_F_mono[THEN predicate2D, OF assms, rotated -1])

lemma blinding_of_T_root_hash:
  assumes "bo \<le> vimage2p rh rh (=)"
  shows "blinding_of_T rh bo \<le> vimage2p (root_hash_T rh) (root_hash_T rh) (=)"
  apply(rule predicate2I vimage2pI)+
  apply(erule blinding_of_T.induct)
  apply simp
  apply(drule blinding_respects_hashes_F[unfolded blinding_respects_hashes_def, THEN predicate2D, rotated -1])
    apply(rule assms)
   apply(blast intro: vimage2pI)
  apply(simp add: vimage2p_def)
  done

lemma blinding_respects_hashes_T [locale_witness]:
  "blinding_respects_hashes rh bo \<Longrightarrow> blinding_respects_hashes (root_hash_T rh) (blinding_of_T rh bo)"
  unfolding blinding_respects_hashes_def by(rule blinding_of_T_root_hash)

lemma blinding_of_on_T [locale_witness]:
  assumes "blinding_of_on A rh bo"
  shows "blinding_of_on {x. set1_T\<^sub>m x \<subseteq> A} (root_hash_T rh) (blinding_of_T rh bo)"
  (is "blinding_of_on ?A ?h ?bo")
proof -
  interpret a: blinding_of_on A rh bo by fact
  show ?thesis
  proof
    have "?bo x x \<and> (?bo x y \<longrightarrow> ?bo y z \<longrightarrow> ?bo x z) \<and> (?bo x y \<longrightarrow> ?bo y x \<longrightarrow> x = y)" 
      if "x \<in> ?A" for x y z using that
    proof(induction x arbitrary: y z)
      case (T\<^sub>m x)
      interpret blinding_of_on 
        "{a. set1_F\<^sub>m a \<subseteq> A \<and> set3_F\<^sub>m a \<subseteq> set3_F\<^sub>m x}" 
        "root_hash_F rh ?h" 
        "blinding_of_F rh bo ?h ?bo"
        apply(rule blinding_of_on_F[OF assms])
        apply unfold_locales
        subgoal using T\<^sub>m.IH T\<^sub>m.prems by(force simp add: eq_onp_def)
        subgoal for a b c using T\<^sub>m.IH[of a b c] T\<^sub>m.prems by auto
        subgoal for a b using T\<^sub>m.IH[of a b] T\<^sub>m.prems by auto
        done
      show ?case using T\<^sub>m.prems
        apply(intro conjI)
        subgoal by(auto intro: blinding_of_T.intros refl)
        subgoal by(auto elim!: blinding_of_T.cases trans intro!: blinding_of_T.intros)
        subgoal by(auto elim!: blinding_of_T.cases dest: antisym)
        done
    qed
    then show "x \<in> ?A \<Longrightarrow> ?bo x x" 
      and "\<lbrakk> ?bo x y; ?bo y z; x \<in> ?A \<rbrakk> \<Longrightarrow> ?bo x z"
      and "\<lbrakk> ?bo x y; ?bo y x; x \<in> ?A \<rbrakk> \<Longrightarrow> x = y"
      for x y z by blast+
  qed
qed

lemmas blinding_of_T [locale_witness] = blinding_of_on_T[where A=UNIV, simplified]

subsubsection \<open> Blinding on composition \<close>

context
  fixes rha :: "('a\<^sub>m, 'a\<^sub>h) hash"
    and boa :: "'a\<^sub>m blinding_of"
    and rhb :: "('b\<^sub>m, 'b\<^sub>h) hash"
    and bob :: "'b\<^sub>m blinding_of"
begin

inductive blinding_of_G :: "('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) G\<^sub>m blinding_of" where
  "blinding_of_G (G\<^sub>m x) (G\<^sub>m y)" if 
  "blinding_of_F (root_hash_T rha) (blinding_of_T rha boa) rhb bob x y"

lemma blinding_of_G_unfold:
  "blinding_of_G = vimage2p the_G\<^sub>m the_G\<^sub>m (blinding_of_F (root_hash_T rha) (blinding_of_T rha boa) rhb bob)"
  apply(rule ext)+
  subgoal for x y by(cases x; cases y)(simp_all add: blinding_of_G.simps fun_eq_iff vimage2p_def)
  done

end

lemma blinding_of_G_mono:
  assumes "boa \<le> boa'" "bob \<le> bob'"
  shows "blinding_of_G rha boa rhb bob \<le> blinding_of_G rha boa' rhb bob'"
  unfolding blinding_of_G_unfold
  by(rule vimage2p_mono' blinding_of_F_mono blinding_of_T_mono assms)+

lemma blinding_of_G_root_hash:
  assumes "boa \<le> vimage2p rha rha (=)" and "bob \<le> vimage2p rhb rhb (=)"
  shows "blinding_of_G rha boa rhb bob \<le> vimage2p (root_hash_G rha rhb) (root_hash_G rha rhb) (=)"
  unfolding blinding_of_G_unfold root_hash_G_unfold vimage2p_comp o_apply
  apply(rule vimage2p_mono')
  apply(rule order_trans)
   apply(rule blinding_respects_hashes_F[unfolded blinding_respects_hashes_def])
    apply(rule blinding_of_T_root_hash)
    apply(rule assms)+
  apply(rule vimage2p_mono')
  apply(simp add: vimage2p_def)
  done

lemma blinding_of_on_G [locale_witness]:
  assumes "blinding_of_on A rha boa" "blinding_of_on B rhb bob"
  shows "blinding_of_on {x. set1_G\<^sub>m x \<subseteq> A \<and> set3_G\<^sub>m x \<subseteq> B} (root_hash_G rha rhb) (blinding_of_G rha boa rhb bob)"
  (is "blinding_of_on ?A ?h ?bo")
proof -
  interpret a: blinding_of_on A rha boa by fact
  interpret b: blinding_of_on B rhb bob by fact
  interpret FT: blinding_of_on 
    "{x. set1_F\<^sub>m x \<subseteq> {x. set1_T\<^sub>m x \<subseteq> A} \<and> set3_F\<^sub>m x \<subseteq> B}" 
    "root_hash_F (root_hash_T rha) rhb"
    "blinding_of_F (root_hash_T rha) (blinding_of_T rha boa) rhb bob"
    ..
  show ?thesis
  proof
    show "?bo \<le> vimage2p ?h ?h (=)"
      using a.hash b.hash
      by(rule blinding_of_G_root_hash)
    show "?bo x x" if "x \<in> ?A" for x using that
      by(cases x; hypsubst)(rule blinding_of_G.intros; rule FT.refl; auto)
    show "?bo x z" if "?bo x y" "?bo y z" "x \<in> ?A" for x y z using that
      by(fastforce elim!: blinding_of_G.cases intro!: blinding_of_G.intros elim!: FT.trans)
    show "x = y" if "?bo x y" "?bo y x" "x \<in> ?A" for x y using that
      by(clarsimp elim!: blinding_of_G.cases)(erule (1) FT.antisym; auto)
  qed
qed

lemmas blinding_of_G [locale_witness] = blinding_of_on_G[where A=UNIV and B=UNIV, simplified]

subsection \<open>Merging\<close>

text \<open>Two Merkle values with the same root hash can be merged into a less blinded Merkle value.
The operation is unspecified for trees with different root hashes.
\<close>

subsubsection \<open> Merging on the base functor \<close>

axiomatization merge_F :: "('a\<^sub>m, 'a\<^sub>h) hash \<Rightarrow> 'a\<^sub>m merge \<Rightarrow> ('b\<^sub>m, 'b\<^sub>h) hash \<Rightarrow> 'b\<^sub>m merge 
  \<Rightarrow> ('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) F\<^sub>m merge" where
  merge_F_cong [fundef_cong]: 
  "\<lbrakk> \<And>a b. a \<in> set1_F\<^sub>m x \<Longrightarrow> ma a b = ma' a b; \<And>a b. a \<in> set3_F\<^sub>m x \<Longrightarrow> mb a b = mb' a b \<rbrakk>
   \<Longrightarrow> merge_F rha ma rhb mb x y = merge_F rha ma' rhb mb' x y"
  and
  merge_on_F [locale_witness]:
  "\<lbrakk> merge_on A rha boa ma; merge_on B rhb bob mb \<rbrakk>
  \<Longrightarrow> merge_on {x. set1_F\<^sub>m x \<subseteq> A \<and> set3_F\<^sub>m x \<subseteq> B} (root_hash_F rha rhb) (blinding_of_F rha boa rhb bob) (merge_F rha ma rhb mb)"

lemmas merge_F [locale_witness] = merge_on_F[where A=UNIV and B=UNIV, simplified]

subsubsection \<open> Merging on the least fixpoint \<close>

lemma wfP_subterm_T: "wfP (\<lambda>x y. x \<in> set3_F\<^sub>m (the_T\<^sub>m y))"
  apply(rule wfPUNIVI)
  subgoal premises IH[rule_format] for P x
    by(induct x)(auto intro: IH)
  done

context
  fixes rh :: "('a\<^sub>m, 'a\<^sub>h) hash"
  fixes m :: "'a\<^sub>m merge"
begin

function merge_T :: "('a\<^sub>m, 'a\<^sub>h) T\<^sub>m merge" where
  "merge_T (T\<^sub>m x) (T\<^sub>m y) = map_option T\<^sub>m (merge_F rh m (root_hash_T rh) merge_T x y)"
  by pat_completeness auto
termination
  apply(relation "{(x, y). x \<in> set3_F\<^sub>m (the_T\<^sub>m y)} <*lex*> {(x, y). x \<in> set3_F\<^sub>m (the_T\<^sub>m y)}")
   apply(auto simp add: wfP_def[symmetric] wfP_subterm_T)
  done

lemma merge_on_T [locale_witness]:
  assumes "merge_on A rh bo m"
  shows "merge_on {x. set1_T\<^sub>m x \<subseteq> A} (root_hash_T rh) (blinding_of_T rh bo) merge_T"
  (is "merge_on ?A ?h ?bo ?m")
proof -
  interpret a: merge_on A rh bo m by fact
  show ?thesis
  proof
    have "(?h a = ?h b \<longrightarrow> (\<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and> (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u))) \<and>
      (?h a \<noteq> ?h b \<longrightarrow> ?m a b = None)"
      if "a \<in> ?A" for a b using that unfolding mem_Collect_eq
    proof(induction a arbitrary: b)
      case (T\<^sub>m x y)
      interpret merge_on "{y. set1_F\<^sub>m y \<subseteq> A \<and> set3_F\<^sub>m y \<subseteq> set3_F\<^sub>m x}"
        "root_hash_F rh ?h" "blinding_of_F rh bo ?h ?bo" "merge_F rh m ?h ?m"
      proof
        fix a
        assume a: "a \<in> set3_F\<^sub>m x"
        with T\<^sub>m.prems have a': "set1_T\<^sub>m a \<subseteq> A" by auto

        fix b
        from T\<^sub>m.IH[OF a a', rule_format, of b]
        show "root_hash_T rh a = root_hash_T rh b
           \<Longrightarrow> \<exists>ab. merge_T a b = Some ab \<and> blinding_of_T rh bo a ab \<and> blinding_of_T rh bo b ab \<and>
                    (\<forall>u. blinding_of_T rh bo a u \<longrightarrow> blinding_of_T rh bo b u \<longrightarrow> blinding_of_T rh bo ab u)"
          and "root_hash_T rh a \<noteq> root_hash_T rh b \<Longrightarrow> merge_T a b = None"
          by(auto dest: sym)
      qed
      show ?case using T\<^sub>m.prems
        apply(intro conjI strip)
        subgoal by(cases y)(auto dest!: join simp add: blinding_of_T.simps)
        subgoal by(cases y)(auto dest!: undefined)
        done
    qed
    then show
      "?h a = ?h b \<Longrightarrow> \<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and> (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u)"
      "?h a \<noteq> ?h b \<Longrightarrow> ?m a b = None"
      if "a \<in> ?A" for a b using that by blast+
  qed
qed

lemmas merge_T [locale_witness] = merge_on_T[where A=UNIV, simplified]

end

lemma merge_T_cong [fundef_cong]:
  assumes "\<And>a b. a \<in> set1_T\<^sub>m x \<Longrightarrow> m a b = m' a b"
  shows "merge_T rh m x y = merge_T rh m' x y"
  using assms
  apply(induction x y rule: merge_T.induct)
  apply simp
  apply(rule arg_cong[where f="map_option _"])
  apply(blast intro: merge_F_cong)
  done

subsubsection \<open> Merging and composition \<close>

context
  fixes rha :: "('a\<^sub>m, 'a\<^sub>h) hash"
  fixes ma :: "'a\<^sub>m merge"
  fixes rhb :: "('b\<^sub>m, 'b\<^sub>h) hash"
  fixes mb :: "'b\<^sub>m merge"
begin

primrec merge_G :: "('a\<^sub>m, 'a\<^sub>h, 'b\<^sub>m, 'b\<^sub>h) G\<^sub>m merge" where
  "merge_G (G\<^sub>m x) y' = (case y' of G\<^sub>m y \<Rightarrow>
    map_option G\<^sub>m (merge_F (root_hash_T rha) (merge_T rha ma) rhb mb x y))"

lemma merge_G_simps [simp]:
  "merge_G (G\<^sub>m x) (G\<^sub>m y) = map_option G\<^sub>m (merge_F (root_hash_T rha) (merge_T rha ma) rhb mb x y)"
  by(simp)

declare merge_G.simps [simp del]

lemma merge_on_G:
  assumes a: "merge_on A rha boa ma" and b: "merge_on B rhb bob mb"
  shows "merge_on {x. set1_G\<^sub>m x \<subseteq> A \<and> set3_G\<^sub>m x \<subseteq> B} (root_hash_G rha rhb) (blinding_of_G rha boa rhb bob) merge_G"
  (is "merge_on ?A ?h ?bo ?m")
proof -
  interpret a: merge_on A rha boa ma by fact
  interpret b: merge_on B rhb bob mb by fact
  interpret F: merge_on 
    "{x. set1_F\<^sub>m x \<subseteq> {x. set1_T\<^sub>m x \<subseteq> A} \<and> set3_F\<^sub>m x \<subseteq> B}"
    "root_hash_F (root_hash_T rha) rhb"
    "blinding_of_F (root_hash_T rha) (blinding_of_T rha boa) rhb bob"
    "merge_F (root_hash_T rha) (merge_T rha ma) rhb mb"
    ..
  show ?thesis
  proof
    show "\<exists>ab. ?m a b = Some ab \<and> ?bo a ab \<and> ?bo b ab \<and> (\<forall>u. ?bo a u \<longrightarrow> ?bo b u \<longrightarrow> ?bo ab u)"
      if "?h a = ?h b" "a \<in> ?A" for a b using that
      by(cases a; cases b)(auto dest!: F.join simp add: blinding_of_G.simps)
    show "?m a b = None" if "?h a \<noteq> ?h b" "a \<in> ?A" for a b using that
      by(cases a; cases b)(auto dest!: F.undefined)
  qed
qed

lemmas merge_G [locale_witness] = merge_on_G[where A=UNIV and B=UNIV, simplified]

end

lemma merge_G_cong [fundef_cong]: 
  "\<lbrakk> \<And>a b. a \<in> set1_G\<^sub>m x \<Longrightarrow> ma a b = ma' a b; \<And>a b. a \<in> set3_G\<^sub>m x \<Longrightarrow> mb a b = mb' a b \<rbrakk>
   \<Longrightarrow> merge_G rha ma rhb mb x y = merge_G rha ma' rhb mb' x y"
  apply(cases x; cases y; simp)
  apply(rule arg_cong[where f="map_option _"])
  apply(blast intro: merge_F_cong merge_T_cong)
  done

end
