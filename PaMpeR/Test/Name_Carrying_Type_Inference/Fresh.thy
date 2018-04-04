theory Fresh
imports Main
begin

class fresh =
  fixes fresh_in :: "'a set \<Rightarrow> 'a"
  assumes "finite S \<Longrightarrow> fresh_in S \<notin> S"

instantiation nat :: fresh
begin
  definition fresh_in_nat :: "nat set \<Rightarrow> nat" where
    [code]: "fresh_in_nat S \<equiv> (if Set.is_empty S then 0 else Max S + 1)"

  instance proof
    fix S :: "nat set"
    assume "finite S"
    consider "Set.is_empty S" | "\<not>Set.is_empty S" by auto
    thus "fresh_in S \<notin> S" unfolding fresh_in_nat_def
    proof(cases)
      case 1
        hence "S = {}" using Set.is_empty_def by metis
        hence "0 \<notin> S" by auto
        thus "(if Set.is_empty S then 0 else Max S + 1) \<notin> S" using 1 by auto
      next
      case 2
        have "Max S + 1 \<notin> S"
          using `finite S` Max.coboundedI add_le_same_cancel1 not_one_le_zero
          by blast
        thus "(if Set.is_empty S then 0 else Max S + 1) \<notin> S" using 2 by auto
      next
    qed
  qed
end

end