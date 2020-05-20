theory Bondy
imports Main
begin

lemma card_less_if_surj_not_inj:
  "\<lbrakk> finite A; f ` A = B; \<not> inj_on f A \<rbrakk> \<Longrightarrow> card B < card A"
by (metis card_image_le inj_on_iff_eq_card order_le_neq_trans)

theorem Bondy : 
  assumes "\<forall>A \<in> F. A \<subseteq> X" and "card X \<ge> 1" and "card F = card X"
  shows "\<exists>D. D \<subseteq> X & card D < card X & card (inter D ` F) = card F"
proof -
  from assms(2,3) have "finite F" and "finite X"
    by (metis card_infinite not_one_le_zero)+
  { fix m
    have "m < card F \<Longrightarrow> \<exists>D. D \<subseteq> X & card D \<le> m & card (inter D ` F) \<ge> m + 1"
    proof (induction m)
      case 0
      hence "{} \<subseteq> X & card {} \<le> 0 & card (inter {} ` F) \<ge> 0 + 1"
        by auto (metis Suc_leI card_eq_0_iff empty_is_image finite_imageI gr0I)
      thus "\<exists>D. (D \<subseteq> X & card D \<le> 0 & card (inter D ` F) \<ge> 0 + 1)" by blast
    next
      case (Suc m)
      hence "m < card F" by arith
      with Suc.IH obtain D
        where D: "D \<subseteq> X \<and> card D \<le> m \<and> m + 1 \<le> card (inter D ` F)" by auto
      with \<open>finite X\<close> have "finite D" by (auto intro: finite_subset)
      show ?case
      proof (cases "card (inter D ` F) = card F")
        case True
        hence "D \<subseteq> X \<and> card D \<le> Suc m \<and> Suc m + 1 \<le> card(inter D ` F)"
          using D Suc.prems by auto
        thus ?thesis by blast
      next
        case False
        hence "~ inj_on (inter D) F" by (auto simp: card_image)
        then obtain A1 A2 where "A1 \<in> F" and "A2 \<in> F" and 
          "D \<inter> A1 = D \<inter> A2" and "A1 \<noteq> A2"  by (auto simp: inj_on_def)
        then obtain x where x: "x : (A1 - A2) \<union> (A2 - A1)" by auto
        from \<open>\<forall>A \<in> F. A \<subseteq> X\<close> \<open>A1 \<in> F\<close> \<open>A2 \<in> F\<close> x have "x : X" by auto
        let ?E = "insert x D"
        from D \<open>finite D\<close> have "card ?E \<le> Suc m"
          by (metis (full_types) Suc_le_mono card_insert_if le_Suc_eq)
        moreover with D \<open>x:X\<close> have "?E \<subseteq> X" by auto
        moreover have "Suc m < card (inter ?E ` F)"
        proof -
          from \<open>D \<inter> A1 = D \<inter> A2\<close> have 1: "(D \<inter> (?E \<inter> A1)) = (D \<inter> (?E \<inter> A2))"
            by auto
          from x have 2: "?E Int A1 \<noteq> ?E Int A2" by auto
          have 3: "inter D \<circ> inter ?E = inter D" by auto
          have 4: "~ inj_on (inter D) (inter ?E ` F)"
            unfolding inj_on_def using 1 2 \<open>A1 \<in> F\<close> \<open>A2 \<in> F\<close> by blast
          from D have "Suc m \<le> card (inter D ` F)" by auto
          also have "... < card (inter ?E ` F)"
            by (rule card_less_if_surj_not_inj[of _ "inter D"])
              (auto simp add: image_image 3 4 \<open>finite F\<close>)
          finally show ?thesis .
        qed
        ultimately have "?E\<subseteq>X \<and> card ?E \<le> Suc m \<and> Suc m + 1 \<le> card (inter ?E ` F)" 
          by auto
        thus "\<exists>D\<subseteq>X. card D \<le> Suc m \<and> Suc m + 1 \<le> card (inter D ` F)" by blast
      qed
    qed
  }
  moreover from assms(2,3) have "card X - 1 < card F" by auto
  ultimately obtain D where 
    "D \<subseteq> X & card D \<le> card X - 1 & card (inter D ` F) \<ge> (card X - 1) + 1"
    by auto
  moreover with \<open>finite F\<close> have "card (inter D ` F) \<le> card F"
    by (elim card_image_le)
  ultimately have "D \<subseteq> X & card D < card X & card (inter D ` F) = card F"
    using \<open>card F = card X\<close> by auto
  thus ?thesis by auto
qed

end

