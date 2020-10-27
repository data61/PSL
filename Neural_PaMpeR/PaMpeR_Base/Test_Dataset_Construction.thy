theory Test_Dataset_Construction
imports "PaMpeR_Base" Main
begin

lemma test:
  assumes fst_assm:"x = x"
   and    snd_assm:"y = z \<or> y"
  shows "z \<Longrightarrow> True \<and> (False \<or> (y \<longrightarrow> y))"
  using assms apply2 auto
  done

end