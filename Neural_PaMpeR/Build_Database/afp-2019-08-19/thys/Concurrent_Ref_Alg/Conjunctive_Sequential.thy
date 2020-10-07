section \<open>Sequential composition for conjunctive models \label{S:conjunctive-sequential}\<close>

theory Conjunctive_Sequential
imports Sequential
begin

text \<open>
  Sequential left-distributivity is only supported by conjunctive models
  but does not apply in general. The relational model is one such example.
\<close>

locale seq_finite_conjunctive = seq_distrib_right + 
  assumes seq_inf_distrib: "c;(d\<^sub>0 \<sqinter> d\<^sub>1) = c;d\<^sub>0 \<sqinter> c;d\<^sub>1"
begin

sublocale seq_distrib_left
    by (simp add: seq_distrib_left.intro seq_distrib_left_axioms.intro 
        seq_inf_distrib sequential_axioms) 
end


locale seq_infinite_conjunctive = seq_distrib_right +
  assumes seq_Inf_distrib: "D \<noteq> {} \<Longrightarrow> c ; \<Sqinter>D = (\<Sqinter>d\<in>D. c ; d)"
begin

sublocale seq_distrib
proof unfold_locales
  fix c::'a and d\<^sub>0::'a and d\<^sub>1::'a
  have "{d\<^sub>0, d\<^sub>1} \<noteq> {}" by simp
  then have "c ; \<Sqinter>{d\<^sub>0, d\<^sub>1} = \<Sqinter>{c ; d |d. d \<in> {d\<^sub>0, d\<^sub>1}}" using seq_Inf_distrib
  proof -
    have "\<Sqinter> ((;) c ` {d\<^sub>0, d\<^sub>1}) = \<Sqinter>{c ; a |a. a \<in> {d\<^sub>0, d\<^sub>1}}"
      using INF_Inf by blast
    then show ?thesis
      using \<open>\<And>(c::'a::refinement_lattice) D::'a::refinement_lattice set. D \<noteq> {} \<Longrightarrow> c ; \<Sqinter>D = (\<Sqinter>d::'a::refinement_lattice\<in>D. c ; d)\<close> \<open>{d\<^sub>0::'a::refinement_lattice, d\<^sub>1::'a::refinement_lattice} \<noteq> {}\<close> by presburger
  qed
  also have "... = c ; d\<^sub>0 \<sqinter> c ; d\<^sub>1" by (simp only: Inf2_inf)
  finally show "c ; (d\<^sub>0 \<sqinter> d\<^sub>1) \<sqsubseteq> c ; d\<^sub>0 \<sqinter> c ; d\<^sub>1" by simp
qed


lemma seq_INF_distrib: "X \<noteq> {} \<Longrightarrow> c ; (\<Sqinter>x\<in>X. d x) = (\<Sqinter>x\<in>X. c ; d x)"
proof -
  assume xne: "X \<noteq> {}"
  have a: "c ; (\<Sqinter>x\<in>X. d x) = c ; \<Sqinter>(d ` X)" by auto
  also have b: "... = (\<Sqinter>d\<in>(d ` X). c ; d)" by (meson image_is_empty seq_Inf_distrib xne)
  also have c: "... = (\<Sqinter>x\<in>X. c ; d x)" by (simp add: image_comp)
  finally show ?thesis by (simp add: b image_comp)
qed

lemma seq_INF_distrib_UNIV: "c ; (\<Sqinter>x. d x) = (\<Sqinter>x. c ; d x)"
  by (simp add: seq_INF_distrib)

lemma INF_INF_seq_distrib: "Y \<noteq> {} \<Longrightarrow> (\<Sqinter>x\<in>X. c x) ; (\<Sqinter>y\<in>Y. d y) = (\<Sqinter>x\<in>X. \<Sqinter>y\<in>Y. c x ; d y)"
  by (simp add: INF_seq_distrib seq_INF_distrib)

lemma INF_INF_seq_distrib_UNIV: "(\<Sqinter>x. c x) ; (\<Sqinter>y. d y) = (\<Sqinter>x. \<Sqinter>y. c x ; d y)"
  by (simp add: INF_INF_seq_distrib)

end

end

