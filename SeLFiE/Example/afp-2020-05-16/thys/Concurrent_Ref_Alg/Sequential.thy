section \<open>Sequential Operator \label{S:sequential}\<close>


theory Sequential
imports Refinement_Lattice
begin

subsection \<open>Basic sequential\<close>

text \<open>
  The sequential composition operator ``$;$'' is associative and 
  has identity nil but it is not commutative. 
  It has $\bot$ as a left annihilator.
\<close>

locale seq =
  fixes seq :: "'a::refinement_lattice \<Rightarrow> 'a \<Rightarrow> 'a" (infixl ";" 90)
  assumes seq_bot [simp]: "\<bottom> ; c = \<bottom>"   (* 35 *)

locale nil =
  fixes nil :: "'a::refinement_lattice" ("nil")

text \<open>
  The monoid axioms imply ``;'' is associative and has identity nil.
  Abort is a left annihilator of sequential composition.
\<close>
locale sequential = seq + nil + seq: monoid seq nil
begin

declare seq.assoc [algebra_simps, field_simps]

lemmas seq_assoc = seq.assoc             (* 30 *)
lemmas seq_nil_right = seq.right_neutral (* 31 *)
lemmas seq_nil_left = seq.left_neutral   (* 32 *)

end

subsection \<open>Distributed sequential\<close>

text \<open>
  Sequential composition distributes across arbitrary infima 
  from the right but only across the binary (finite) infima from the left
  and hence it is monotonic in both arguments. 
  We consider left distribution first.
  Note that Section \ref{S:conjunctive-sequential} considers the
  case in which the weak-seq-inf-distrib axiom is strengthened to
  an equality.
\<close>

locale seq_distrib_left = sequential +
  assumes weak_seq_inf_distrib: 
    "(c::'a::refinement_lattice);(d\<^sub>0 \<sqinter> d\<^sub>1) \<sqsubseteq> (c;d\<^sub>0 \<sqinter> c;d\<^sub>1)"  (* 33 *)
begin

text \<open>Left distribution implies sequential composition is monotonic is its right argument\<close>
lemma seq_mono_right: "c\<^sub>0 \<sqsubseteq> c\<^sub>1 \<Longrightarrow> d ; c\<^sub>0 \<sqsubseteq> d ; c\<^sub>1"
  by (metis inf.absorb_iff2 le_inf_iff weak_seq_inf_distrib)

(* Nec? *)
lemma seq_bot_right [simp]: "c;\<bottom> \<sqsubseteq> c"
   by (metis bot.extremum seq.right_neutral seq_mono_right)

end

locale seq_distrib_right = sequential +
  assumes Inf_seq_distrib: 
    "(\<Sqinter> C) ; d = (\<Sqinter>(c::'a::refinement_lattice)\<in>C. c ; d)" (* 34 *)
begin

lemma INF_seq_distrib: "(\<Sqinter>c\<in>C. f c) ; d = (\<Sqinter>c\<in>C. f c ; d)"
  using Inf_seq_distrib by (auto simp add: image_comp)

lemma inf_seq_distrib: "(c\<^sub>0 \<sqinter> c\<^sub>1) ; d = (c\<^sub>0 ; d \<sqinter> c\<^sub>1 ; d)"
proof -
  have "(c\<^sub>0 \<sqinter> c\<^sub>1) ; d = (\<Sqinter> {c\<^sub>0, c\<^sub>1}) ; d" by simp
  also have "... = (\<Sqinter>c\<in>{c\<^sub>0, c\<^sub>1}. c ; d)" by (fact Inf_seq_distrib)
  also have "... = (c\<^sub>0 ; d) \<sqinter> (c\<^sub>1 ; d)" by simp
  finally show ?thesis .
qed

lemma seq_mono_left: "c\<^sub>0 \<sqsubseteq> c\<^sub>1 \<Longrightarrow> c\<^sub>0 ; d \<sqsubseteq> c\<^sub>1 ; d"
  by (metis inf.absorb_iff2 inf_seq_distrib)

lemma seq_top [simp]: "\<top> ; c = \<top>"
proof -
  have "\<top> ; c = (\<Sqinter>a\<in>{}. a ; c)"
    by (metis Inf_empty Inf_seq_distrib)
  thus ?thesis
    by simp
qed

primrec seq_power :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infixr "\<^sup>;^" 80) where
    seq_power_0: "a \<^sup>;^ 0 = nil"
  | seq_power_Suc: "a \<^sup>;^ Suc n = a ; (a \<^sup>;^ n)"

notation (latex output)
  seq_power ("(_\<^bsup>_\<^esup>)" [1000] 1000)

notation (HTML output)
  seq_power ("(_\<^bsup>_\<^esup>)" [1000] 1000)


lemma seq_power_front: "(a \<^sup>;^ n) ; a = a ; (a \<^sup>;^ n)"
  by (induct n, simp_all add: seq_assoc)

lemma seq_power_split_less: "i < j \<Longrightarrow> (b \<^sup>;^ j) = (b \<^sup>;^ i) ; (b \<^sup>;^ (j - i))"
proof (induct j arbitrary: i type: nat)
  case 0
  thus ?case by simp
next
  case (Suc j)
  have "b \<^sup>;^ Suc j = b ; (b \<^sup>;^ i) ; (b \<^sup>;^ (j - i))"
    using Suc.hyps Suc.prems less_Suc_eq seq_assoc by auto
  also have "... = (b \<^sup>;^ i) ; b ; (b \<^sup>;^ (j - i))" by (simp add: seq_power_front)
  also have "... = (b \<^sup>;^ i) ; (b \<^sup>;^ (Suc j - i))"
    using Suc.prems Suc_diff_le seq_assoc by force
  finally show ?case .
qed

end

locale seq_distrib = seq_distrib_right + seq_distrib_left
begin

lemma seq_mono: "c\<^sub>1 \<sqsubseteq> d\<^sub>1 \<Longrightarrow> c\<^sub>2 \<sqsubseteq> d\<^sub>2 \<Longrightarrow> c\<^sub>1;c\<^sub>2 \<sqsubseteq> d\<^sub>1;d\<^sub>2"
  using seq_mono_left seq_mono_right by (metis inf.orderE le_infI2) 

end

end
