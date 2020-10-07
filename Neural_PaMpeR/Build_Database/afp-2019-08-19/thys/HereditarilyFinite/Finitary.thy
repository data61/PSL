theory Finitary
imports Ordinal
begin

class finitary =
  fixes hf_of :: "'a \<Rightarrow> hf"
  assumes inj: "inj hf_of"
begin
  lemma hf_of_eq_iff [simp]: "hf_of x = hf_of y \<longleftrightarrow> x=y"
    using inj by (auto simp: inj_on_def)
end

instantiation unit :: finitary
begin
  definition hf_of_unit_def: "hf_of (u::unit) \<equiv> 0"
  instance
    by intro_classes (auto simp: inj_on_def hf_of_unit_def)
end

instantiation bool :: finitary
begin
  definition hf_of_bool_def: "hf_of b \<equiv> if b then 1 else 0"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_bool_def)
end

instantiation nat :: finitary
begin
  definition hf_of_nat_def: "hf_of \<equiv> ord_of"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_nat_def)
end

instantiation int :: finitary
begin
  definition hf_of_int_def: 
    "hf_of i \<equiv> if i\<ge>(0::int) then \<langle>0, hf_of (nat i)\<rangle> else \<langle>1, hf_of (nat (-i))\<rangle>"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_int_def)
end

text \<open>Strings are char lists, and are not considered separately.\<close>
instantiation char :: finitary
begin
  definition hf_of_char_def: 
    "hf_of x \<equiv> hf_of (of_char x :: nat)"
  instance 
    by standard (auto simp: inj_on_def hf_of_char_def)
end

instantiation prod :: (finitary,finitary) finitary
begin
  definition hf_of_prod_def: 
    "hf_of \<equiv> \<lambda>(x,y). \<langle>hf_of x, hf_of y\<rangle>"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_prod_def)
end

instantiation sum :: (finitary,finitary) finitary
begin
  definition hf_of_sum_def: 
    "hf_of \<equiv> case_sum (HF.Inl o hf_of) (HF.Inr o hf_of)"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_sum_def split: sum.split_asm)
end

instantiation option :: (finitary) finitary
begin
  definition hf_of_option_def: 
    "hf_of \<equiv> case_option 0 (\<lambda>x. \<lbrace>hf_of x\<rbrace>)"
  instance 
    by intro_classes (auto simp: inj_on_def hf_of_option_def split: option.split_asm)
end

instantiation list :: (finitary) finitary
begin
  primrec hf_of_list where
    "hf_of_list Nil = 0"
  | "hf_of_list (x#xs) = \<langle>hf_of x, hf_of_list xs\<rangle>"
  lemma [simp]: fixes x :: "'a list" shows "hf_of x = hf_of y \<Longrightarrow> x = y"
    apply (induct x arbitrary: y, auto)
    apply (metis (mono_tags) hf_of_list.simps(2) hpair_nonzero neq_Nil_conv)
    apply (rename_tac y)
    apply (case_tac y, auto)
    done
  instance 
    by intro_classes (auto simp: inj_on_def)
end

end
