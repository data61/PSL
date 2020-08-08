theory Test_Base
imports Main "PSL.PSL"
begin

strategy DIndTac = Thens [Dynamic (InductTac), Auto, IsSolved]
strategy DInd = Thens [Dynamic (Induct), Auto, IsSolved]
strategy DIndHams = Thens [Dynamic (Induct), RepeatN (Hammer), IsSolved]
strategy Test = Thens [RepeatN (Hammer), IsSolved]

lemma meta_allI: "\<forall> x. P x \<Longrightarrow> (\<And>x. P x)"
  apply auto done

end