(*  Title:      RSAPSS/EMSAPSS.thy
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

section "EMSA-PSS encoding and decoding operation" 

theory EMSAPSS 
imports SHA1 Wordarith
begin

text \<open>We define the encoding and decoding operations for the probabilistic
 signature scheme. Finally we show, that encoded messages always can be 
 verified\<close>

definition show_rightmost_bits:: "bv \<Rightarrow> nat \<Rightarrow> bv" (* extract n rightmost bits of a bit string*)
  where "show_rightmost_bits bvec n = rev (take n (rev bvec))"

definition BC:: "bv" (* 0xbc *)
  where "BC = [One, Zero, One, One, One, One, Zero, Zero]"

definition salt:: "bv"
  where "salt = []"

definition sLen:: "nat" (* length of salt *)
  where "sLen = length salt"

definition generate_M':: "bv \<Rightarrow> bv \<Rightarrow> bv" (* generate_M' outputs "M'" a bit string of length "64 + length(sha1 _ ) + sLen" with 64 initial zero bits *)
  where "generate_M' mHash salt_new = bv_prepend 64 \<zero> [] @ mHash @ salt_new"

definition generate_PS:: "nat \<Rightarrow> nat \<Rightarrow> bv" (* generate_PS outputs "PS" a bit string consisting of "nat (roundup emBits 8) * 8 - sLen - length (sha1 _ ) - 16" zero bits *)
  where "generate_PS emBits hLen = bv_prepend ((roundup emBits 8)*8 - sLen - hLen - 16) \<zero> []"

definition generate_DB:: "bv \<Rightarrow> bv" (* generate_DB outputs the bit string DB="PS#(0x01)#salt" of length "nat (roundup emBits 8) * 8 - length (sha1 _ ) - 8" *)
  where "generate_DB PS = PS @ [Zero, Zero, Zero, Zero, Zero, Zero, Zero, One] @ salt"

definition maskedDB_zero:: "bv \<Rightarrow> nat \<Rightarrow> bv" (* sets "roundup emBits 8 * 8 - emBits" bits of maskedDB to zero *)
  where "maskedDB_zero maskedDB emBits = bv_prepend ((roundup emBits 8) * 8 - emBits)  \<zero> (drop ((roundup emBits 8)*8 - emBits) maskedDB)"

definition generate_H:: "bv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bv" (* generate_H returns a bit string of length (sha1 _) *)
  where "generate_H EM emBits hLen = take hLen (drop ((roundup emBits 8)*8 - hLen - 8) EM)"

definition generate_maskedDB:: "bv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bv " (* outputs a bit string of length "nat (roundup emBits 8) * 8 - length (sha1 _) - 8" *)
  where "generate_maskedDB EM emBits hLen = take ((roundup emBits 8)*8 - hLen - 8) EM"

definition generate_salt:: "bv \<Rightarrow> bv" (* outputs a bit string of length sLen *)
  where "generate_salt DB_zero = show_rightmost_bits DB_zero sLen"

primrec MGF2:: "bv \<Rightarrow> nat \<Rightarrow> bv" (* help function for MGF1 *)
where
  "MGF2 Z 0 = sha1 (Z@(nat_to_bv_length 0 32))"
| "MGF2 Z (Suc n) = (MGF2 Z n)@(sha1 (Z@(nat_to_bv_length (Suc n) 32)))"

definition MGF1:: "bv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bv" (* help function for MGF *)
  where "MGF1 Z n l = take l (MGF2 Z n)"

definition MGF:: "bv \<Rightarrow> nat \<Rightarrow> bv" (* mask generation function *)
where
  "MGF Z l = (if l = 0 \<or> 2^32*(length (sha1 Z)) < l
              then []
              else MGF1 Z ( roundup l (length (sha1 Z))  - 1 ) l)"


definition emsapss_encode_help8:: "bv \<Rightarrow> bv \<Rightarrow> bv"
  where "emsapss_encode_help8 DBzero H = DBzero @ H @ BC"

definition emsapss_encode_help7:: "bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bv"
  where "emsapss_encode_help7 maskedDB H emBits =
    emsapss_encode_help8 (maskedDB_zero maskedDB emBits) H"

definition emsapss_encode_help6:: "bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bv"
  where "emsapss_encode_help6 DB dbMask H emBits =
    (if dbMask = []
     then []
     else emsapss_encode_help7 (bvxor DB dbMask) H emBits)"

definition emsapss_encode_help5:: "bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bv"
  where "emsapss_encode_help5 DB H emBits =
    emsapss_encode_help6 DB (MGF H (length DB)) H emBits"

definition emsapss_encode_help4:: "bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bv"
  where "emsapss_encode_help4 PS H emBits =
    emsapss_encode_help5 (generate_DB PS) H emBits"

definition emsapss_encode_help3:: "bv \<Rightarrow> nat \<Rightarrow> bv"
  where "emsapss_encode_help3 H emBits =
    emsapss_encode_help4 (generate_PS emBits (length H)) H emBits"

definition emsapss_encode_help2:: "bv \<Rightarrow> nat \<Rightarrow> bv"
  where "emsapss_encode_help2 M' emBits = emsapss_encode_help3 (sha1 M') emBits"

definition emsapss_encode_help1:: "bv \<Rightarrow> nat \<Rightarrow> bv"
  where "emsapss_encode_help1 mHash emBits =
    (if emBits  < length (mHash) + sLen + 16
     then []
     else emsapss_encode_help2 (generate_M' mHash salt) emBits)"

definition emsapss_encode:: "bv \<Rightarrow> nat \<Rightarrow> bv" (* outputs the encoded message of length emBits *)
  where "emsapss_encode M emBits =
    (if (2^64 \<le> length M \<or> 2^32 * 160 < emBits)
     then []
     else emsapss_encode_help1 (sha1 M) emBits)"


definition emsapss_decode_help11:: "bv \<Rightarrow> bv \<Rightarrow> bool"
  where "emsapss_decode_help11 H' H = (if H' \<noteq> H then False else True)"

definition emsapss_decode_help10:: "bv \<Rightarrow> bv \<Rightarrow> bool"
  where "emsapss_decode_help10 M' H = emsapss_decode_help11 (sha1 M') H"

definition emsapss_decode_help9:: "bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bool"
  where "emsapss_decode_help9 mHash salt_new H =
    emsapss_decode_help10 (generate_M' mHash salt_new) H"

definition emsapss_decode_help8:: "bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bool"
  where "emsapss_decode_help8 mHash DB_zero H =
    emsapss_decode_help9 mHash (generate_salt DB_zero) H"

definition emsapss_decode_help7:: "bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bool"
  where "emsapss_decode_help7 mHash DB_zero H emBits =
   (if (take ( (roundup emBits 8)*8 - (length mHash) - sLen - 16) DB_zero \<noteq> bv_prepend ( (roundup emBits 8)*8 - (length mHash) - sLen - 16) \<zero> []) \<or> (take 8 ( drop ((roundup emBits 8)*8 - (length mHash) - sLen - 16 ) DB_zero ) \<noteq> [Zero, Zero, Zero, Zero, Zero, Zero, Zero, One])
    then False
    else emsapss_decode_help8 mHash DB_zero H)"

definition emsapss_decode_help6:: "bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bool"
  where "emsapss_decode_help6 mHash DB H emBits =
    emsapss_decode_help7 mHash (maskedDB_zero DB emBits) H emBits"

definition emsapss_decode_help5:: "bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bool"
  where "emsapss_decode_help5 mHash maskedDB dbMask H emBits =
    emsapss_decode_help6 mHash (bvxor maskedDB dbMask) H emBits"

definition emsapss_decode_help4:: "bv \<Rightarrow> bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bool"
  where "emsapss_decode_help4 mHash maskedDB H emBits =
   (if take ((roundup emBits 8)*8 - emBits) maskedDB \<noteq> bv_prepend ((roundup emBits 8)*8 - emBits) \<zero> []
    then False
    else emsapss_decode_help5 mHash maskedDB (MGF H ((roundup emBits 8)*8 - (length mHash) - 8)) H emBits)"

definition emsapss_decode_help3:: "bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bool"
  where "emsapss_decode_help3 mHash EM emBits =
    emsapss_decode_help4 mHash (generate_maskedDB EM emBits (length mHash)) (generate_H EM emBits (length mHash)) emBits"

definition emsapss_decode_help2:: "bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bool"
  where "emsapss_decode_help2 mHash EM emBits =
   (if show_rightmost_bits EM 8 \<noteq> BC
    then False
    else emsapss_decode_help3 mHash EM emBits)"

definition emsapss_decode_help1:: "bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bool"
  where "emsapss_decode_help1 mHash EM emBits =
    (if emBits < length (mHash) + sLen + 16
     then False 
     else emsapss_decode_help2 mHash EM emBits)"

definition emsapss_decode:: "bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> bool" (* outputs "true" if EM is encoding of M *)
  where "emsapss_decode M EM emBits =
    (if (2^64 \<le> length M \<or> 2^32*160<emBits)
     then False
     else emsapss_decode_help1 (sha1 M) EM emBits)"

lemma roundup_positiv: "0 < emBits \<Longrightarrow> 0 < roundup emBits 160"
  by (auto simp add: roundup)

lemma roundup_ge_emBits:" 0 < emBits \<Longrightarrow> 0 < x \<Longrightarrow> emBits \<le> (roundup emBits x) * x"
  apply (simp add: roundup mult.commute)
  apply (safe)
  apply (simp)
  apply (simp add: add.commute [of x "x*(emBits div x)" ])
  apply (insert mult_div_mod_eq [of x emBits])
  apply (subgoal_tac "emBits mod x < x")
  apply (arith)
  apply (simp only: mod_less_divisor)
  done

lemma roundup_ge_0: "0 < emBits \<Longrightarrow> 0 < x \<Longrightarrow> 0 \<le> roundup emBits x * x - emBits"
  by (simp add: roundup)

lemma roundup_le_7: "0 < emBits \<Longrightarrow> roundup emBits 8 * 8 - emBits \<le>  7"
  by (auto simp add: roundup) arith

lemma roundup_nat_ge_8_help:
  "length (sha1 M) + sLen + 16 \<le> emBits \<Longrightarrow> 8 \<le> roundup emBits 8 * 8 - (length (sha1 M) + 8)"
  apply (insert roundup_ge_emBits [of emBits 8])
  apply (simp add: roundup sha1len sLen_def)
  done

lemma roundup_nat_ge_8:
  "length (sha1 M) + sLen + 16 \<le> emBits \<Longrightarrow> 8 \<le> roundup emBits 8 * 8 - (length (sha1 M) + 8)"
  apply (insert roundup_nat_ge_8_help [of M emBits])
  apply arith
  done

lemma roundup_le_ub:
  "\<lbrakk> 176 + sLen \<le> emBits; emBits \<le> 2^32 * 160\<rbrakk> \<Longrightarrow> (roundup emBits 8) * 8 - 168 \<le> 2^32 * 160"
  apply (simp add: roundup)
  apply (safe)
  apply (simp)
  apply (arith)+
  done
 
lemma modify_roundup_ge1: "\<lbrakk>8 \<le> roundup emBits 8 * 8 - 168\<rbrakk> \<Longrightarrow> 176 \<le>  roundup emBits 8 * 8"
  by arith

lemma modify_roundup_ge2: "\<lbrakk> 176 \<le> roundup emBits 8 * 8\<rbrakk> \<Longrightarrow> 21 < roundup emBits 8"
  by simp

lemma roundup_help1: "\<lbrakk> 0 < roundup l 160\<rbrakk> \<Longrightarrow> (roundup l 160 - 1) + 1 = (roundup l 160)"
  by arith

lemma roundup_help1_new: "\<lbrakk> 0 < l\<rbrakk> \<Longrightarrow> (roundup l 160 - 1) + 1 = (roundup l 160)"
  apply (drule roundup_positiv [of l])
  apply arith
  done

lemma roundup_help2: "\<lbrakk>176 + sLen \<le> emBits\<rbrakk> \<Longrightarrow> roundup emBits 8 * 8 - emBits <=  roundup emBits 8 * 8 - 160 - sLen - 16"
  by (simp add: sLen_def)

lemma bv_prepend_equal: "bv_prepend (Suc n) b l = b#bv_prepend n b l" 
  by (simp add: bv_prepend)

lemma length_bv_prepend: "length (bv_prepend n b l) = n+length l"
  by (induct n) (simp_all add: bv_prepend)

lemma length_bv_prepend_drop: "a <= length xs \<longrightarrow> length (bv_prepend a b (drop a xs)) = length xs"
  by (simp add:length_bv_prepend)

lemma take_bv_prepend: "take n (bv_prepend n b x) = bv_prepend n b []"
  by (induct n) (simp add: bv_prepend)+

lemma take_bv_prepend2: "take n (bv_prepend n b xs@ys@zs) = bv_prepend n b []"
  by (induct n) (simp add: bv_prepend)+

lemma bv_prepend_append: "bv_prepend a b x = bv_prepend a b [] @ x"
  by (induct a) (simp add: bv_prepend, simp add: bv_prepend_equal)

lemma bv_prepend_append2:
  "x < y \<Longrightarrow> bv_prepend y b xs = (bv_prepend x b [])@(bv_prepend (y-x) b [])@xs"
  by (simp add: bv_prepend replicate_add [symmetric])

lemma drop_bv_prepend_help2: "\<lbrakk>x < y\<rbrakk> \<Longrightarrow> drop x (bv_prepend y b []) = bv_prepend (y-x) b []"
  apply (insert bv_prepend_append2 [of "x" "y" b "[]"])
  by (simp add: length_bv_prepend)

lemma drop_bv_prepend_help3: "\<lbrakk>x = y\<rbrakk> \<Longrightarrow> drop x (bv_prepend y b []) = bv_prepend (y-x) b []"
  apply (insert length_bv_prepend [of y b "[]"])
  by (simp add: bv_prepend)

lemma drop_bv_prepend_help4: "\<lbrakk>x \<le> y\<rbrakk> \<Longrightarrow> drop x (bv_prepend y b []) = bv_prepend (y-x) b []"
  apply (insert drop_bv_prepend_help2 [of x y b] drop_bv_prepend_help3 [of x y b])
  by (arith)

lemma bv_prepend_add: "bv_prepend x b [] @ bv_prepend y b [] = bv_prepend (x + y) b []"
  by (induct x) (simp add: bv_prepend)+

lemma bv_prepend_drop: "x \<le> y \<longrightarrow> bv_prepend x b (drop x (bv_prepend y b [])) = bv_prepend y b []"
  apply (simp add: drop_bv_prepend_help4 [of x y b])
  by (simp add: bv_prepend_append [of "x" b "(bv_prepend (y - x) b [])"] bv_prepend_add)

lemma bv_prepend_split: "bv_prepend x b (left @ right) = bv_prepend x b left @ right"
  by (induct x) (simp add: bv_prepend)+

lemma length_generate_DB: "length (generate_DB PS) = length PS + 8 + sLen"
  by (simp add: generate_DB_def sLen_def)

lemma length_generate_PS: "length (generate_PS emBits 160) = (roundup emBits 8)*8 - sLen - 160 - 16"
  by (simp add: generate_PS_def length_bv_prepend)

lemma length_bvxor: "length a = length b \<Longrightarrow> length (bvxor a b) = length a"
  by (simp add: bvxor)

lemma length_MGF2: "length (MGF2 Z m) = Suc m * length (sha1 (Z @ nat_to_bv_length m 32))"
  by (induct m) (simp+, simp add: sha1len)

lemma length_MGF1: "l \<le> (Suc n) * 160 \<Longrightarrow> length (MGF1 Z n l) = l"
  by (simp add: MGF1_def length_MGF2 sha1len)

lemma length_MGF: "0 < l \<Longrightarrow> l \<le>  2^32 * length (sha1 x) \<Longrightarrow> length (MGF x l) = l"
  apply (simp add: MGF_def sha1len)
  apply (insert roundup_help1_new [of l])
  apply (rule length_MGF1)
  apply (simp)
  apply (insert roundup_ge_emBits [of l 160])
  apply (arith)
  done

lemma solve_length_generate_DB:
  "\<lbrakk> 0 < emBits; length (sha1 M) + sLen + 16 \<le> emBits\<rbrakk>
  \<Longrightarrow> length (generate_DB (generate_PS emBits (length (sha1 x)) )) = (roundup emBits 8) * 8 - 168"
  apply (insert roundup_ge_emBits [of emBits 8])
  apply (simp add: length_generate_DB length_generate_PS sha1len)
  done

lemma length_maskedDB_zero:
  "\<lbrakk> roundup emBits 8 * 8 - emBits \<le> length maskedDB\<rbrakk>
  \<Longrightarrow> length (maskedDB_zero maskedDB emBits) = length maskedDB"
  by (simp add: maskedDB_zero_def length_bv_prepend)

lemma take_equal_bv_prepend:
  "\<lbrakk> 176 + sLen \<le> emBits; roundup emBits 8 * 8 - emBits \<le> 7\<rbrakk>
  \<Longrightarrow> take (roundup emBits 8 * 8 - length (sha1 M) - sLen - 16) (maskedDB_zero (generate_DB (generate_PS emBits 160)) emBits) =
    bv_prepend (roundup emBits 8 * 8 - length (sha1 M) - sLen - 16) \<zero> []"
  apply (insert roundup_help2 [of emBits] length_generate_PS [of emBits])
  apply (simp add: sha1len maskedDB_zero_def generate_DB_def generate_PS_def
    bv_prepend_split bv_prepend_drop)
  done

lemma lastbits_BC: "BC = show_rightmost_bits (xs @ ys @ BC) 8"
  by (simp add: show_rightmost_bits_def BC_def)

lemma equal_zero:
  "176 + sLen \<le> emBits \<Longrightarrow> roundup emBits 8 * 8 - emBits \<le> roundup emBits 8 * 8 - (176 + sLen)
  \<Longrightarrow> 0 = roundup emBits 8 * 8 - emBits - (roundup emBits 8 * 8 - (176 + sLen))"
  by arith

lemma get_salt: "\<lbrakk> 176 + sLen \<le> emBits; roundup emBits 8 * 8 - emBits \<le> 7\<rbrakk> \<Longrightarrow> (generate_salt (maskedDB_zero (generate_DB (generate_PS emBits 160)) emBits)) = salt"
  apply (insert roundup_help2 [of emBits] length_generate_PS [of emBits] equal_zero [of emBits])
  apply (simp add: generate_DB_def generate_PS_def maskedDB_zero_def)
  apply (simp add: bv_prepend_split bv_prepend_drop generate_salt_def
    show_rightmost_bits_def sLen_def)
  done

lemma generate_maskedDB_elim: "\<lbrakk>roundup emBits 8 * 8 - emBits \<le> length x; ( roundup emBits 8) * 8 - (length (sha1 M)) - 8 = length (maskedDB_zero x emBits)\<rbrakk> \<Longrightarrow> generate_maskedDB (maskedDB_zero x emBits @ y @ z) emBits (length(sha1 M)) = maskedDB_zero x emBits"
  apply (simp add: maskedDB_zero_def)
  apply (insert length_bv_prepend_drop [of "(roundup emBits 8 * 8 - emBits)" "x"])
  apply (simp add: generate_maskedDB_def)
  done

lemma generate_H_elim: "\<lbrakk> roundup emBits 8 * 8 - emBits \<le> length x; length (maskedDB_zero x emBits) =  (roundup emBits 8) * 8 - 168; length y = 160\<rbrakk> \<Longrightarrow> generate_H (maskedDB_zero x emBits @ y @ z) emBits 160 = y"
  apply (simp add: maskedDB_zero_def)
  apply (insert length_bv_prepend_drop [of "roundup emBits 8 * 8 - emBits" "x"])
  apply (simp add: generate_H_def)
  done

lemma length_bv_prepend_drop_special: "[|roundup emBits 8 * 8 - emBits <= roundup emBits 8 * 8 - (176 + sLen); length (generate_PS emBits 160) = roundup emBits 8 * 8 - (176 + sLen)|] ==> length ( bv_prepend (roundup emBits 8 * 8 - emBits) \<zero> (drop (roundup emBits 8 * 8 - emBits) (generate_PS emBits 160))) = length (generate_PS emBits 160)"
  by (simp add: length_bv_prepend_drop)

lemma x01_elim: "\<lbrakk>176 + sLen \<le> emBits; roundup emBits 8 * 8 - emBits \<le> 7\<rbrakk> \<Longrightarrow> take 8 (drop (roundup emBits 8 * 8 - (length (sha1 M) + sLen + 16))(maskedDB_zero (generate_DB (generate_PS emBits 160)) emBits)) = [\<zero>, \<zero>, \<zero>, \<zero>, \<zero>, \<zero>, \<zero>, \<one>]"
  apply (insert roundup_help2 [of emBits] length_generate_PS [of emBits] equal_zero [of emBits])
  apply (simp add: sha1len maskedDB_zero_def generate_DB_def generate_PS_def
    bv_prepend_split bv_prepend_drop)
  done

lemma drop_bv_mapzip:
  assumes "n <= length x" "length x = length y"
  shows "drop n (bv_mapzip f x y) = bv_mapzip f (drop n x) (drop n y)"
proof -
  have "\<And>x y. n <= length x \<Longrightarrow> length x = length y \<Longrightarrow>
      drop n (bv_mapzip f x y) = bv_mapzip f (drop n x) (drop n y)"
    apply (induct n)
    apply simp
    apply (case_tac x, case_tac[!] y, auto)
    done
  with assms show ?thesis by simp
qed

lemma [simp]:
  assumes "length a = length b"
  shows "bvxor (bvxor a b) b = a"
proof -
  have "\<And>b. length a = length b \<Longrightarrow> bvxor (bvxor a b) b = a"
    apply (induct a)
    apply (auto simp add: bvxor)
    apply (case_tac b)
    apply (simp)+
    apply (case_tac a1)
    apply (case_tac a)
    apply (safe)
    apply (simp)+
    apply (case_tac a)
    apply (simp)+
    done
  with assms show ?thesis by simp
qed

lemma bvxorxor_elim_help:
  assumes "x <= length a" and "length a = length b"
  shows "bv_prepend x \<zero> (drop x (bvxor (bv_prepend x \<zero> (drop x (bvxor a b))) b)) =
    bv_prepend x \<zero> (drop x a)"
proof -
  have "drop x (bvxor (bv_prepend x \<zero> (drop x (bvxor a b))) b) = drop x a"
    apply (unfold bvxor bv_prepend)
    apply (cut_tac assms)
    apply (insert length_replicate [of x \<zero> ])
    apply (insert length_drop [of x a])
    apply (insert length_drop [of x b])
    apply (insert length_bvxor [of "drop x a" "drop x b"])
    apply (subgoal_tac "length (replicate x \<zero> @ drop x (bv_mapzip (\<oplus>\<^sub>b) a b)) = length b")
    apply (subgoal_tac "b = (take x b)@(drop x b)")
    apply (insert drop_bv_mapzip [of x "(replicate x \<zero> @ drop x (bv_mapzip (\<oplus>\<^sub>b) a b))" b "(\<oplus>\<^sub>b)"])
    apply (simp)
    apply (insert drop_bv_mapzip [of x a b "(\<oplus>\<^sub>b)"])
    apply (simp)
    apply (fold bvxor)
    apply (simp_all)
    done
  with assms show ?thesis by simp
qed

lemma bvxorxor_elim: "\<lbrakk> roundup emBits 8 * 8 - emBits \<le> length a; length a = length b\<rbrakk> \<Longrightarrow> (maskedDB_zero (bvxor (maskedDB_zero (bvxor a b) emBits)b) emBits) = bv_prepend (roundup emBits 8 * 8 - emBits) \<zero> (drop (roundup emBits 8 * 8 - emBits) a)"
  by (simp add: maskedDB_zero_def bvxorxor_elim_help)

lemma verify: "\<lbrakk>(emsapss_encode M emBits) \<noteq> []; EM=(emsapss_encode M emBits)\<rbrakk> \<Longrightarrow> emsapss_decode M EM emBits = True"
  apply (simp add: emsapss_decode_def emsapss_encode_def)
  apply (safe, simp+)
  apply (simp add: emsapss_decode_help1_def emsapss_encode_help1_def)
  apply (safe, simp+)
  apply (simp add: emsapss_decode_help2_def emsapss_encode_help2_def)
  apply (safe)
  apply (simp add: emsapss_encode_help3_def emsapss_encode_help4_def
    emsapss_encode_help5_def emsapss_encode_help6_def)
  apply (safe)
  apply (simp add: emsapss_encode_help7_def emsapss_encode_help8_def lastbits_BC [symmetric])+
  apply (simp add: emsapss_decode_help3_def emsapss_encode_help3_def
    emsapss_decode_help4_def emsapss_encode_help4_def)
  apply (safe)
  apply (insert roundup_le_7 [of emBits] roundup_ge_0 [of emBits 8] roundup_nat_ge_8 [of M emBits])
  apply (simp add: generate_maskedDB_def emsapss_encode_help5_def emsapss_encode_help6_def)
  apply (safe)
  apply (simp)
  apply (simp add: emsapss_encode_help7_def)
  apply (simp only: emsapss_encode_help8_def)
  apply (simp only: maskedDB_zero_def)
  apply (simp only: take_bv_prepend2 min.absorb1)
  apply (simp)
  apply (simp add: emsapss_encode_help5_def emsapss_encode_help6_def)
  apply (safe)
  apply (simp)+
  apply (insert solve_length_generate_DB [of emBits M "generate_M' (sha1 M) salt"] roundup_le_ub [of emBits])
  apply (insert length_MGF [of "(roundup emBits 8) * 8 - 168" "(sha1 (generate_M' (sha1 M) salt))"])
  apply (insert modify_roundup_ge1 [of emBits] modify_roundup_ge2 [of emBits])
  apply (simp add: sha1len emsapss_encode_help7_def emsapss_encode_help8_def)
  apply (insert length_bvxor [of "(generate_DB (generate_PS emBits 160))" "(MGF (sha1 (generate_M' (sha1 M) salt)) ((roundup emBits 8) * 8 - 168))"])
  apply (insert generate_maskedDB_elim [of emBits "(bvxor (generate_DB (generate_PS emBits 160))(MGF (sha1 (generate_M' (sha1 M) salt)) ((roundup emBits 8) * 8 - 168)))" M "sha1 (generate_M' (sha1 M) salt)" BC])
  apply (insert length_maskedDB_zero [of emBits "(bvxor (generate_DB (generate_PS emBits 160))(MGF (sha1 (generate_M' (sha1 M) salt)) ((roundup emBits 8) * 8 - 168)))"])
  apply (insert generate_H_elim [of emBits "(bvxor (generate_DB (generate_PS emBits 160))(MGF (sha1 (generate_M' (sha1 M) salt)) (roundup emBits 8 * 8 - 168)))" "sha1 (generate_M' (sha1 M) salt)" BC])
  apply (simp add: sha1len emsapss_decode_help5_def)
  apply (simp only: emsapss_decode_help6_def emsapss_decode_help7_def)
  apply (insert bvxorxor_elim [of emBits "(generate_DB (generate_PS emBits 160))" "(MGF (sha1 (generate_M' (sha1 M) salt)) ((roundup emBits 8) * 8 - 168))"])
  apply (fold maskedDB_zero_def)
  apply (insert take_equal_bv_prepend [of emBits M] x01_elim [of emBits M] get_salt [of emBits])
  apply (simp add: emsapss_decode_help8_def emsapss_decode_help9_def emsapss_decode_help10_def emsapss_decode_help11_def) 
  done

end
