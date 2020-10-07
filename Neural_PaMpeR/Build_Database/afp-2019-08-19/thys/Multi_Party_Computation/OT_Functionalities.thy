subsection \<open>Oblivious Transfer functionalities\<close> 

text\<open>Here we define the functionalities for 1-out-of-2 and 1-out-of-4 OT.\<close>

theory OT_Functionalities imports
  CryptHOL.CryptHOL
begin

definition funct_OT_12 :: "('a \<times>  'a) \<Rightarrow> bool \<Rightarrow> (unit \<times> 'a) spmf"
  where "funct_OT_12 input\<^sub>1 \<sigma> = return_spmf (() , if \<sigma> then (snd input\<^sub>1) else (fst input\<^sub>1))"

lemma lossless_funct_OT_12: "lossless_spmf (funct_OT_12 msgs \<sigma>)"
  by(simp add: funct_OT_12_def)

definition funct_OT_14 :: "('a \<times> 'a \<times> 'a \<times> 'a) \<Rightarrow> (bool \<times> bool) \<Rightarrow> (unit \<times> 'a) spmf"
  where "funct_OT_14 M C = do {
    let (c0,c1) = C;
    let (m00, m01, m10, m11) = M;
    return_spmf ((),if c0 then (if c1 then m11 else m10) else (if c1 then m01 else m00))}"

lemma lossless_funct_14_OT: "lossless_spmf (funct_OT_14 M C)"
  by(simp add: funct_OT_14_def split_def)

end