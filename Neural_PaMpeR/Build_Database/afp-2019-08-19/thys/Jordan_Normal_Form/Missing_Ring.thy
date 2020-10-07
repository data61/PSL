(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Missing Ring\<close>

text \<open>This theory contains several lemmas which might be of interest to the Isabelle distribution.\<close>

theory Missing_Ring
imports
  "HOL-Algebra.Ring"
begin

context comm_monoid
begin

lemma finprod_reindex_bij_betw: "bij_betw h S T 
  \<Longrightarrow> g \<in> h ` S \<rightarrow> carrier G 
  \<Longrightarrow> finprod G (\<lambda>x. g (h x)) S = finprod G g T"
  using finprod_reindex[of g h S] unfolding bij_betw_def by auto

lemma finprod_reindex_bij_witness:
  assumes witness:
    "\<And>a. a \<in> S \<Longrightarrow> i (j a) = a"
    "\<And>a. a \<in> S \<Longrightarrow> j a \<in> T"
    "\<And>b. b \<in> T \<Longrightarrow> j (i b) = b"
    "\<And>b. b \<in> T \<Longrightarrow> i b \<in> S"
  assumes eq:
    "\<And>a. a \<in> S \<Longrightarrow> h (j a) = g a"
  assumes g: "g \<in> S \<rightarrow> carrier G"
  and h: "h \<in> j ` S \<rightarrow> carrier G"
  shows "finprod G g S = finprod G h T"
proof -
  have b: "bij_betw j S T"
    using bij_betw_byWitness[where A=S and f=j and f'=i and A'=T] witness by auto
  have fp: "finprod G g S = finprod G (\<lambda>x. h (j x)) S"
    by (rule finprod_cong, insert eq g, auto)
  show ?thesis
    using finprod_reindex_bij_betw[OF b h] unfolding fp .
qed
end

lemmas (in abelian_monoid) finsum_reindex_bij_witness = add.finprod_reindex_bij_witness

locale csemiring = semiring + comm_monoid R

context cring
begin
sublocale csemiring ..
end

lemma (in comm_monoid) finprod_one': 
  "(\<And> a. a \<in> A \<Longrightarrow> f a = \<one>) \<Longrightarrow> finprod G f A = \<one>"
  by (induct A rule: infinite_finite_induct, auto)

lemma (in comm_monoid) finprod_split: 
  "finite A \<Longrightarrow> f ` A \<subseteq> carrier G \<Longrightarrow> a \<in> A \<Longrightarrow> finprod G f A = f a \<otimes> finprod G f (A - {a})"
  by (rule trans[OF trans[OF _ finprod_Un_disjoint[of "{a}" "A - {a}" f]]], auto,
  rule arg_cong[of _ _ "finprod G f"], auto)

lemma (in comm_monoid) finprod_finprod:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> (\<And> a b. a \<in> A  \<Longrightarrow> b \<in> B \<Longrightarrow> g a b \<in> carrier G) \<Longrightarrow>
  finprod G (\<lambda> a. finprod G (g a) B) A = finprod G (\<lambda> (a,b). g a b) (A \<times> B)"
proof (induct A rule: finite_induct)
  case (insert a' A)
  note IH = this
  let ?l = "(\<Otimes>a\<in>insert a' A. finprod G (g a) B)"
  let ?r = "(\<Otimes>a\<in>insert a' A \<times> B. case a of (a, b) \<Rightarrow> g a b)"
  have "?l = finprod G (g a') B \<otimes> (\<Otimes>a\<in>A. finprod G (g a) B)"
    using IH by simp
  also have "(\<Otimes>a\<in>A. finprod G (g a) B) = finprod G (\<lambda> (a,b). g a b) (A \<times> B)"
    by (rule IH(3), insert IH, auto)
  finally have idl: "?l = finprod G (g a') B \<otimes> finprod G (\<lambda> (a,b). g a b) (A \<times> B)" .
  from IH(2) have "insert a' A \<times> B = {a'} \<times> B \<union> A \<times> B" by auto
  hence "?r = (\<Otimes>a\<in>{a'} \<times> B \<union> A \<times> B. case a of (a, b) \<Rightarrow> g a b)" by simp
  also have "\<dots> = (\<Otimes>a\<in>{a'} \<times> B. case a of (a, b) \<Rightarrow> g a b) \<otimes> (\<Otimes>a\<in> A \<times> B. case a of (a, b) \<Rightarrow> g a b)"
    by (rule finprod_Un_disjoint, insert IH, auto)
  also have "(\<Otimes>a\<in>{a'} \<times> B. case a of (a, b) \<Rightarrow> g a b) = finprod G (g a') B"
    using IH(4) IH(5)
  proof (induct B rule: finite_induct)
    case (insert b' B)
    note IH = this
    have id: "(\<Otimes>a\<in>{a'} \<times> B. case a of (a, b) \<Rightarrow> g a b) = finprod G (g a') B"
      by (rule IH(3)[OF IH(4)], auto)
    have id2: "\<And> x F. {a'} \<times> insert x F = insert (a',x) ({a'} \<times> F)" by auto
    have id3: "(\<Otimes>a\<in>insert (a', b') ({a'} \<times> B). case a of (a, b) \<Rightarrow> g a b)
      = g a' b' \<otimes> (\<Otimes>a\<in>({a'} \<times> B). case a of (a, b) \<Rightarrow> g a b)"
      by (rule trans[OF finprod_insert], insert IH, auto)
    show ?case unfolding id2 id3 id
      by (rule sym, rule finprod_insert, insert IH, auto)
  qed simp
  finally have idr: "?r = finprod G (g a') B \<otimes> (\<Otimes>a\<in>A \<times> B. case a of (a, b) \<Rightarrow> g a b)" .
  show ?case unfolding idl idr ..
qed simp

lemma (in comm_monoid) finprod_swap:
  assumes "finite A" "finite B" "\<And> a b. a \<in> A  \<Longrightarrow> b \<in> B \<Longrightarrow> g a b \<in> carrier G"
  shows "finprod G (\<lambda> (b,a). g a b) (B \<times> A) = finprod G (\<lambda> (a,b). g a b) (A \<times> B)"
proof -
  have [simp]: "(\<lambda>(a, b). (b, a)) ` (A \<times> B) = B \<times> A" by auto
  have [simp]: "(\<lambda> x. case case x of (a, b) \<Rightarrow> (b, a) of (a, b) \<Rightarrow> g b a) = (\<lambda> (a,b). g a b)"
    by (intro ext, auto)
  show ?thesis 
    by (rule trans[OF trans[OF _ finprod_reindex[of "\<lambda> (a,b). g b a" "\<lambda> (a,b). (b,a)"]]],
    insert assms, auto simp: inj_on_def)
qed

lemma (in comm_monoid) finprod_finprod_swap:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> (\<And> a b. a \<in> A  \<Longrightarrow> b \<in> B \<Longrightarrow> g a b \<in> carrier G) \<Longrightarrow>
  finprod G (\<lambda> a. finprod G (g a) B) A = finprod G (\<lambda> b. finprod G (\<lambda> a. g a b) A) B"
  using finprod_finprod[of A B] finprod_finprod[of B A] finprod_swap[of A B]
  by simp



lemmas (in semiring) finsum_zero' = add.finprod_one' 
lemmas (in semiring) finsum_split = add.finprod_split 
lemmas (in semiring) finsum_finsum_swap = add.finprod_finprod_swap


lemma (in csemiring) finprod_zero: 
  "finite A \<Longrightarrow> f \<in> A \<rightarrow> carrier R \<Longrightarrow> \<exists>a\<in>A. f a = \<zero>
   \<Longrightarrow> finprod R f A = \<zero>"
proof (induct A rule: finite_induct)
  case (insert a A)
  from finprod_insert[OF insert(1-2), of f] insert(4)
  have ins: "finprod R f (insert a A) = f a \<otimes> finprod R f A" by simp
  have fA: "finprod R f A \<in> carrier R"
    by (rule finprod_closed, insert insert, auto)
  show ?case
  proof (cases "f a = \<zero>")
    case True
    with fA show ?thesis unfolding ins by simp
  next
    case False
    with insert(5) have "\<exists> a \<in> A. f a = \<zero>" by auto
    from insert(3)[OF _ this] insert have "finprod R f A = \<zero>" by auto
    with insert show ?thesis unfolding ins by auto
  qed
qed simp

lemma (in semiring) finsum_product:
  assumes A: "finite A" and B: "finite B"
  and f: "f \<in> A \<rightarrow> carrier R" and g: "g \<in> B \<rightarrow> carrier R" 
  shows "finsum R f A \<otimes> finsum R g B = (\<Oplus>i\<in>A. \<Oplus>j\<in>B. f i \<otimes> g j)"
  unfolding finsum_ldistr[OF A finsum_closed[OF g] f]
proof (rule finsum_cong'[OF refl])
  fix a
  assume a: "a \<in> A"
  show "f a \<otimes> finsum R g B = (\<Oplus>j\<in>B. f a \<otimes> g j)"
  by (rule finsum_rdistr[OF B _ g], insert a f, auto)
qed (insert f g B, auto intro: finsum_closed)
    
lemma (in semiring) Units_one_side_I: 
  "a \<in> carrier R \<Longrightarrow> p \<in> Units R \<Longrightarrow> p \<otimes> a = \<one> \<Longrightarrow> a \<in> Units R"
  "a \<in> carrier R \<Longrightarrow> p \<in> Units R \<Longrightarrow> a \<otimes> p = \<one> \<Longrightarrow> a \<in> Units R"
  by (metis Units_closed Units_inv_Units Units_l_inv inv_unique)+

context ordered_cancel_semiring begin
subclass ordered_cancel_ab_semigroup_add ..
end

text \<open>partially ordered variant\<close>
class ordered_semiring_strict = semiring + comm_monoid_add + ordered_cancel_ab_semigroup_add +
  assumes mult_strict_left_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> c * a < c * b"
  assumes mult_strict_right_mono: "a < b \<Longrightarrow> 0 < c \<Longrightarrow> a * c < b * c"
begin

subclass semiring_0_cancel ..

subclass ordered_semiring
proof
  fix a b c :: 'a
  assume A: "a \<le> b" "0 \<le> c"
  from A show "c * a \<le> c * b"
    unfolding le_less
    using mult_strict_left_mono by (cases "c = 0") auto
  from A show "a * c \<le> b * c"
    unfolding le_less
    using mult_strict_right_mono by (cases "c = 0") auto
qed

lemma mult_pos_pos[simp]: "0 < a \<Longrightarrow> 0 < b \<Longrightarrow> 0 < a * b"
using mult_strict_left_mono [of 0 b a] by simp

lemma mult_pos_neg: "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> a * b < 0"
using mult_strict_left_mono [of b 0 a] by simp

lemma mult_neg_pos: "a < 0 \<Longrightarrow> 0 < b \<Longrightarrow> a * b < 0"
using mult_strict_right_mono [of a 0 b] by simp

text \<open>Legacy - use \<open>mult_neg_pos\<close>\<close>
lemma mult_pos_neg2: "0 < a \<Longrightarrow> b < 0 \<Longrightarrow> b * a < 0" 
by (drule mult_strict_right_mono [of b 0], auto)

text\<open>Strict monotonicity in both arguments\<close>
lemma mult_strict_mono:
  assumes "a < b" and "c < d" and "0 < b" and "0 \<le> c"
  shows "a * c < b * d"
  using assms apply (cases "c=0")
  apply (simp)
  apply (erule mult_strict_right_mono [THEN less_trans])
  apply (force simp add: le_less)
  apply (erule mult_strict_left_mono, assumption)
  done

text\<open>This weaker variant has more natural premises\<close>
lemma mult_strict_mono':
  assumes "a < b" and "c < d" and "0 \<le> a" and "0 \<le> c"
  shows "a * c < b * d"
by (rule mult_strict_mono) (insert assms, auto)

lemma mult_less_le_imp_less:
  assumes "a < b" and "c \<le> d" and "0 \<le> a" and "0 < c"
  shows "a * c < b * d"
  using assms apply (subgoal_tac "a * c < b * c")
  apply (erule less_le_trans)
  apply (erule mult_left_mono)
  apply simp
  apply (erule mult_strict_right_mono)
  apply assumption
  done

lemma mult_le_less_imp_less:
  assumes "a \<le> b" and "c < d" and "0 < a" and "0 \<le> c"
  shows "a * c < b * d"
  using assms apply (subgoal_tac "a * c \<le> b * c")
  apply (erule le_less_trans)
  apply (erule mult_strict_left_mono)
  apply simp
  apply (erule mult_right_mono)
  apply simp
  done

end

class ordered_idom = idom + ordered_semiring_strict +
  assumes zero_less_one [simp]: "0 < 1" begin

subclass semiring_1 ..
subclass comm_ring_1 ..
subclass ordered_ring ..
subclass ordered_comm_semiring by(unfold_locales, fact mult_left_mono)
subclass ordered_ab_semigroup_add ..

lemma of_nat_ge_0[simp]: "of_nat x \<ge> 0"
proof (induct x)
  case 0 thus ?case by auto
  next case (Suc x)
    hence "0 \<le> of_nat x" by auto
    also have "of_nat x < of_nat (Suc x)" by auto
    finally show ?case by auto
qed

lemma of_nat_eq_0[simp]: "of_nat x = 0 \<longleftrightarrow> x = 0"
proof(induct x,simp)
  case (Suc x)
    have "of_nat (Suc x) > 0" apply(rule le_less_trans[of _ "of_nat x"]) by auto
    thus ?case by auto
qed

lemma inj_of_nat: "inj (of_nat :: nat \<Rightarrow> 'a)"
proof(rule injI)
  fix x y show "of_nat x = of_nat y \<Longrightarrow> x = y"
  proof (induct x arbitrary: y)
    case 0 thus ?case
      proof (induct y)
        case 0 thus ?case by auto
        next case (Suc y)
          hence "of_nat (Suc y) = 0" by auto
          hence "Suc y = 0" unfolding of_nat_eq_0 by auto
          hence False by auto
          thus ?case by auto
      qed
    next case (Suc x)
      thus ?case
      proof (induct y)
        case 0
          hence "of_nat (Suc x) = 0" by auto
          hence "Suc x = 0" unfolding of_nat_eq_0 by auto
          hence False by auto
          thus ?case by auto
        next case (Suc y) thus ?case by auto
      qed
  qed
qed

subclass ring_char_0 by(unfold_locales, fact inj_of_nat)

end

(*
instance linordered_idom \<subseteq> ordered_semiring_strict by (intro_classes,auto)
instance linordered_idom \<subseteq> ordered_idom by (intro_classes, auto)
*)

end
