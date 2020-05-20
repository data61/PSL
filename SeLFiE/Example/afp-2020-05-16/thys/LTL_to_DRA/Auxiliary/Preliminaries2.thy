(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Auxiliary Facts\<close>

theory Preliminaries2
  imports Main "HOL-Library.Infinite_Set"
begin

subsection \<open>Finite and Infinite Sets\<close>

lemma finite_product:
  assumes fst: "finite (fst ` A)"
  and     snd: "finite (snd ` A)"
  shows   "finite A"
proof -
  have "A \<subseteq> (fst ` A) \<times> (snd ` A)"
    by force
  thus ?thesis
    using snd fst finite_subset by blast
qed

subsection \<open>Cofinite Filters\<close>

lemma almost_all_commutative:
  "finite S \<Longrightarrow> (\<forall>x \<in> S. \<forall>\<^sub>\<infinity>i. P x (i::nat)) = (\<forall>\<^sub>\<infinity>i. \<forall>x \<in> S. P x i)"
proof (induction rule: finite_induct) 
  case (insert x S)
    {
      assume "\<forall>x \<in> insert x S. \<forall>\<^sub>\<infinity>i. P x i"
      hence "\<forall>\<^sub>\<infinity>i. \<forall>x \<in> S. P x i" and "\<forall>\<^sub>\<infinity>i. P x i"
        using insert by simp+
      then obtain i\<^sub>1 i\<^sub>2 where "\<And>j. j \<ge> i\<^sub>1 \<Longrightarrow> \<forall>x \<in> S. P x j"
        and "\<And>j. j \<ge> i\<^sub>2 \<Longrightarrow> P x j"
        unfolding MOST_nat_le by auto
      hence "\<And>j. j \<ge> max i\<^sub>1 i\<^sub>2 \<Longrightarrow> \<forall>x \<in> S \<union> {x}. P x j"
        by simp
      hence "\<forall>\<^sub>\<infinity>i. \<forall>x \<in> insert x S. P x i"
        unfolding MOST_nat_le by blast
    }
    moreover
    have "\<forall>\<^sub>\<infinity>i. \<forall>x \<in> insert x S. P x i \<Longrightarrow> \<forall>x \<in> insert x S. \<forall>\<^sub>\<infinity>i. P x i"
      unfolding MOST_nat_le by auto
    ultimately
    show ?case 
      by blast
qed simp

lemma almost_all_commutative':
  "finite S \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> \<forall>\<^sub>\<infinity>i. P x (i::nat)) \<Longrightarrow> (\<forall>\<^sub>\<infinity>i. \<forall>x \<in> S. P x i)"
  using almost_all_commutative by blast

fun index
where
  "index P = (if \<forall>\<^sub>\<infinity>i. P i then Some (LEAST i. \<forall>j \<ge> i. P j) else None)"

lemma index_properties: 
  fixes i :: nat
  shows "index P = Some i \<Longrightarrow> 0 < i \<Longrightarrow> \<not> P (i - 1)"
    and "index P = Some i \<Longrightarrow> j \<ge> i \<Longrightarrow> P j"
proof -
  assume "index P = Some i"
  moreover
  hence i_def: "i = (LEAST i. \<forall>j \<ge> i. P j)" and "\<forall>\<^sub>\<infinity>i. P i"
    unfolding index.simps using option.distinct(2) option.sel 
    by (metis (erased, lifting))+
  then obtain i' where "\<forall>j \<ge> i'.  P j"
    unfolding MOST_nat_le by blast
  ultimately
  show "\<And>j. j \<ge> i \<Longrightarrow> P j"
    using LeastI[of "\<lambda>i. \<forall>j \<ge> i. P j"] by (metis i_def) 
  {
    assume "0 < i"
    then obtain j where "i = Suc j" and "j < i"
      using lessE by blast
    hence "\<And>j'. j' > j \<Longrightarrow> P j'"
      using \<open>\<And>j. j \<ge> i \<Longrightarrow> P j\<close> by force
    hence "\<not> P j"
      using not_less_Least[OF \<open>j < i\<close>[unfolded i_def]] by (metis leI le_antisym)
    thus "\<not> P (i - 1)"
      unfolding \<open>i = Suc j\<close> by simp
  }
qed

end
