(*  Title:      Code_Symbolic_Bits_Int.thy
    Author:     Andreas Lochbihler, ETH Zurich
*)

chapter \<open>Symbolic implementation of bit operations on int\<close>

theory Code_Symbolic_Bits_Int
imports
  More_Bits_Int
begin

section \<open>Implementations of bit operations on \<^typ>\<open>int\<close> operating on symbolic representation\<close>

lemma Bit_code [code]:
  "0 BIT b = of_bool b"
  "Int.Pos n BIT False = Int.Pos (num.Bit0 n)"
  "Int.Pos n BIT True = Int.Pos (num.Bit1 n)"
  "Int.Neg n BIT False = Int.Neg (num.Bit0 n)"
  "Int.Neg n BIT True = Int.Neg (Num.BitM n)"
by(cases b)(simp_all)

lemma bin_last_code [code]: 
  "bin_last 0 \<longleftrightarrow> False"
  "bin_last (Int.Pos num.One) \<longleftrightarrow> True"
  "bin_last (Int.Pos (num.Bit0 n)) \<longleftrightarrow> False"
  "bin_last (Int.Pos (num.Bit1 n)) \<longleftrightarrow> True"
  "bin_last (Int.Neg num.One) \<longleftrightarrow> True"
  "bin_last (Int.Neg (num.Bit0 n)) \<longleftrightarrow> False"
  "bin_last (Int.Neg (num.Bit1 n)) \<longleftrightarrow> True"
by(simp_all)

lemma bin_nth_code [code]:
  "bin_nth 0                 n = False"
  "bin_nth (Int.Neg num.One) n = True"
  "bin_nth (Int.Pos num.One)      0 = True"
  "bin_nth (Int.Pos (num.Bit0 m)) 0 = False"
  "bin_nth (Int.Pos (num.Bit1 m)) 0 = True"
  "bin_nth (Int.Neg (num.Bit0 m)) 0 = False"
  "bin_nth (Int.Neg (num.Bit1 m)) 0 = True"
  "bin_nth (Int.Pos num.One)      (Suc n) = False"
  "bin_nth (Int.Pos (num.Bit0 m)) (Suc n) = bin_nth (Int.Pos m) n"
  "bin_nth (Int.Pos (num.Bit1 m)) (Suc n) = bin_nth (Int.Pos m) n"
  "bin_nth (Int.Neg (num.Bit0 m)) (Suc n) = bin_nth (Int.Neg m) n"
  "bin_nth (Int.Neg (num.Bit1 m)) (Suc n) = bin_nth (Int.Neg (Num.inc m)) n"
by(simp_all add: Num.add_One)

lemma int_not_code [code]:
  "NOT (0 :: int) = -1"
  "NOT (Int.Pos n) = Int.Neg (Num.inc n)"
  "NOT (Int.Neg n) = Num.sub n num.One"
by(simp_all add: Num.add_One int_not_def)

lemma int_and_code [code]: fixes i j :: int shows
  "0 AND j = 0"
  "i AND 0 = 0"
  "Int.Pos n AND Int.Pos m = (case bitAND_num n m of None \<Rightarrow> 0 | Some n' \<Rightarrow> Int.Pos n')"
  "Int.Neg n AND Int.Neg m = NOT (Num.sub n num.One OR Num.sub m num.One)"
  "Int.Pos n AND Int.Neg num.One = Int.Pos n"
  "Int.Pos n AND Int.Neg (num.Bit0 m) = Num.sub (bitORN_num (Num.BitM m) n) num.One"
  "Int.Pos n AND Int.Neg (num.Bit1 m) = Num.sub (bitORN_num (num.Bit0 m) n) num.One"
  "Int.Neg num.One AND Int.Pos m = Int.Pos m"
  "Int.Neg (num.Bit0 n) AND Int.Pos m = Num.sub (bitORN_num (Num.BitM n) m) num.One"
  "Int.Neg (num.Bit1 n) AND Int.Pos m = Num.sub (bitORN_num (num.Bit0 n) m) num.One"
           apply (fold int_not_neg_numeral)
           apply (simp_all add: int_numeral_bitAND_num int_or_not_bitORN_num[symmetric] bbw_not_dist Num.add_One int_not_neg_numeral sub_inc_One inc_BitM cong: option.case_cong)
    apply (simp_all add: int_and_comm int_not_neg_numeral [symmetric])
  done

lemma int_or_code [code]: fixes i j :: int shows
  "0 OR j = j"
  "i OR 0 = i"
  "Int.Pos n OR Int.Pos m = Int.Pos (bitOR_num n m)"
  "Int.Neg n OR Int.Neg m = NOT (Num.sub n num.One AND Num.sub m num.One)"
  "Int.Pos n OR Int.Neg num.One = Int.Neg num.One"
  "Int.Pos n OR Int.Neg (num.Bit0 m) = (case bitANDN_num (Num.BitM m) n of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Pos n OR Int.Neg (num.Bit1 m) = (case bitANDN_num (num.Bit0 m) n of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Neg num.One OR Int.Pos m = Int.Neg num.One"
  "Int.Neg (num.Bit0 n) OR Int.Pos m = (case bitANDN_num (Num.BitM n) m of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
  "Int.Neg (num.Bit1 n) OR Int.Pos m = (case bitANDN_num (num.Bit0 n) m of None \<Rightarrow> -1 | Some n' \<Rightarrow> Int.Neg (Num.inc n'))"
           apply (simp_all add: int_numeral_bitOR_num)
      apply (simp_all add: int_or_def int_not_neg_numeral int_and_comm int_not_and_bitANDN_num del: int_not_simps(4) split: option.split)
  apply (simp_all add: Num.add_One)
  done

lemma int_xor_code [code]: fixes i j :: int shows
  "0 XOR j = j"
  "i XOR 0 = i"
  "Int.Pos n XOR Int.Pos m = (case bitXOR_num n m of None \<Rightarrow> 0 | Some n' \<Rightarrow> Int.Pos n')"
  "Int.Neg n XOR Int.Neg m = Num.sub n num.One XOR Num.sub m num.One"
  "Int.Neg n XOR Int.Pos m = NOT (Num.sub n num.One XOR Int.Pos m)"
  "Int.Pos n XOR Int.Neg m = NOT (Int.Pos n XOR Num.sub m num.One)"
  by(fold int_not_neg_numeral)(simp_all add: int_numeral_bitXOR_num int_xor_not cong: option.case_cong)

lemma bin_rest_code [code]: "bin_rest i = i >> 1"
by(simp add: bin_rest_def shiftr_int_def)

lemma sbintrunc_code [code]:
  "sbintrunc n bin =
  (let bin' = bin AND bin_mask (n + 1)
   in if bin' !! n then bin' - (2 << n) else bin')"
proof (induct n arbitrary: bin)
  case 0
  then show ?case
    by (simp add: bitval_bin_last [symmetric])
next
  case (Suc n)
  thus ?case by(cases bin rule: bin_exhaust)(simp add: Let_def minus_BIT_0)
qed

lemma set_bits_code [code]: 
  "set_bits = Code.abort (STR ''set_bits is unsupported on type int'') (\<lambda>_. set_bits :: _ \<Rightarrow> int)"
by simp

lemma fixes i :: int 
  shows int_set_bit_True_conv_OR [code]: "set_bit i n True = i OR (1 << n)"
  and int_set_bit_False_conv_NAND [code]: "set_bit i n False = i AND NOT (1 << n)"
  and int_set_bit_conv_ops: "set_bit i n b = (if b then i OR (1 << n) else i AND NOT (1 << n))"
by(simp_all add: set_bit_int_def bin_set_conv_OR bin_clr_conv_NAND)

lemma int_shiftr_code [code]: fixes i :: int shows
  "i >> 0 = i"
  "0 >> Suc n = (0 :: int)"
  "Int.Pos num.One >> Suc n = 0"
  "Int.Pos (num.Bit0 m) >> Suc n = Int.Pos m >> n"
  "Int.Pos (num.Bit1 m) >> Suc n = Int.Pos m >> n"
  "Int.Neg num.One >> Suc n = -1"
  "Int.Neg (num.Bit0 m) >> Suc n = Int.Neg m >> n"
  "Int.Neg (num.Bit1 m) >> Suc n = Int.Neg (Num.inc m) >> n"
  by (simp_all only: BIT_special_simps(2 )[symmetric] int_shiftr0 int_0shiftr numeral_One int_minus1_shiftr Int.Pos_def Int.Neg_def expand_BIT int_shiftr_Suc Num.add_One uminus_Bit_eq)
    (simp_all add: add_One)

lemma int_shiftl_code [code]:
  "i << 0 = i"
  "i << Suc n = Int.dup i << n"
by(simp_all add: shiftl_int_def)

lemma int_lsb_code [code]:
  "lsb (0 :: int) = False"
  "lsb (Int.Pos num.One) = True"
  "lsb (Int.Pos (num.Bit0 w)) = False"
  "lsb (Int.Pos (num.Bit1 w)) = True"
  "lsb (Int.Neg num.One) = True"
  "lsb (Int.Neg (num.Bit0 w)) = False"
  "lsb (Int.Neg (num.Bit1 w)) = True"
by simp_all

end
