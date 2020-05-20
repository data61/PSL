(*  Title:      RSAPSS/RSAPSS.thy
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt 
*)

section "RSS-PSS encoding and decoding operation" 

theory RSAPSS
imports EMSAPSS Cryptinverts
begin

text \<open>We define the RSA-PSS signature and verification operations. Moreover we
  show, that messages signed with RSA-PSS can always be verified
\<close>

definition rsapss_sign_help1:: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bv"
  where "rsapss_sign_help1 em_nat e n =
    nat_to_bv_length (rsa_crypt em_nat e n) (length (nat_to_bv n))"

definition rsapss_sign:: "bv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bv" (* Input: message (an bv), private key, RSA modulus; Output: signature (an bv)*)
  where "rsapss_sign m e n =
   (if (emsapss_encode m (length (nat_to_bv n) - 1)) = [] 
    then []
    else (rsapss_sign_help1 (bv_to_nat (emsapss_encode m (length (nat_to_bv n) - 1)) ) e n))"

definition rsapss_verify:: "bv \<Rightarrow> bv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" (* Input:  Message, Signature to be verified (an bv), public key, RSA modulus; Output: valid or invalid signature *)
  where "rsapss_verify m s d n =
   (if (length s) \<noteq> length(nat_to_bv n)
    then False
    else let em = nat_to_bv_length (rsa_crypt (bv_to_nat s) d n) ((roundup (length(nat_to_bv n) - 1) 8) * 8) in emsapss_decode m em (length(nat_to_bv n) - 1))"

lemma length_emsapss_encode:
  "emsapss_encode m x \<noteq> [] \<Longrightarrow> length (emsapss_encode m x) = roundup x 8 * 8"
  apply (atomize (full))
  apply (simp add: emsapss_encode_def)
  apply (simp add: emsapss_encode_help1_def)
  apply (simp add: emsapss_encode_help2_def)
  apply (simp add: emsapss_encode_help3_def)
  apply (simp add: emsapss_encode_help4_def)
  apply (simp add: emsapss_encode_help5_def)
  apply (simp add: emsapss_encode_help6_def)
  apply (simp add: emsapss_encode_help7_def)
  apply (simp add: emsapss_encode_help8_def)
  apply (simp add: maskedDB_zero_def)
  apply (simp add: length_generate_DB)
  apply (simp add: sha1len)
  apply (simp add: bvxor)
  apply (simp add: length_generate_PS)
  apply (simp add: length_bv_prepend)
  apply (simp add: MGF_def)
  apply (simp add: MGF1_def)
  apply (simp add: length_MGF2)
  apply (simp add: sha1len)
  apply (simp add: length_generate_DB)
  apply (simp add: length_generate_PS)
  apply (simp add: BC_def)
  apply (insert roundup_ge_emBits [of x 8])
  apply safe
  apply (simp add: max.absorb1)
  done

lemma bv_to_nat_emsapss_encode_le: "emsapss_encode m x \<noteq> [] \<Longrightarrow> bv_to_nat (emsapss_encode m x) < 2^(roundup x 8 * 8)" 
  apply (insert length_emsapss_encode [of m x])
  apply (insert bv_to_nat_upper_range [of "emsapss_encode m x"])
by (simp)

lemma length_helper1: shows "length
  (bvxor
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))
  (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))))@
  sha1 (generate_M' (sha1 m) salt) @ BC)
  = length 
  (bvxor
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))
  (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))))) + 168"
proof -
  have a: "length BC = 8" by (simp add: BC_def)
  have b: "length (sha1 (generate_M' (sha1 m) salt)) = 160" by (simp add: sha1len)
  have c: "\<And> a b c. length (a@b@c) = length a + length b + length c" by simp
  from a and b show ?thesis using c by simp 
qed

lemma MGFLen_helper: "MGF z l ~= [] \<Longrightarrow> l <= 2^32*(length (sha1 z))"
proof (cases "2^32*length (sha1 z) < l")
  assume x: "MGF z l ~= []"
  assume a: "2 ^ 32 * length (sha1 z) < l" 
  then have "MGF z l = []" 
  proof (cases "l=0")
    assume "l=0"
    then show "MGF z l = []" by (simp add: MGF_def)
  next
    assume "l~=0"
    then have "(l = 0 \<or> 2^32*length(sha1 z) < l) = True" using a by fast
    then show "MGF z l = []" apply (simp only: MGF_def) by simp
  qed
  then show ?thesis using x by simp
next
  assume "\<not> 2 ^ 32 * length (sha1 z) < l" 
  then show ?thesis by simp
qed

lemma length_helper2: assumes p: "prime p" and q: "prime q" 
                      and mgf: "(MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))) ~= []" 
  and len: "length (sha1 M) + sLen + 16 \<le> (length (nat_to_bv (p * q))) - Suc 0"
  shows "length
  (
  (bvxor
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))
  (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))))
  ) = (roundup (length (nat_to_bv (p * q)) - Suc 0) 8) * 8 - 168"
proof -
  have a: "length (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))) = (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))"
  proof -
    have "0 < (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))" by (simp add: generate_DB_def)
    moreover have "(length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))) \<le> 2^32 * length (sha1 (sha1 (generate_M' (sha1 m) salt)))" using mgf and MGFLen_helper by simp
    ultimately show ?thesis using length_MGF by simp
  qed
  have b: "length (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))) = ((roundup ((length (nat_to_bv (p * q))) - Suc 0) 8) * 8 - 168)"
  proof -
    have "0 <= (length (nat_to_bv (p * q))) - Suc 0" 
    proof -
      from p have p2: "1<p" by (simp add: prime_nat_iff)
      moreover from q have "1<q" by (simp add: prime_nat_iff)
      ultimately have "p<p*q" by simp
      then have "1<p*q" using p2 by arith
      then show ?thesis using len_nat_to_bv_pos by simp
    qed  
    then show ?thesis using solve_length_generate_DB using len by simp
  qed
  have c: "length (bvxor
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt)))))
    (MGF (sha1 (generate_M' (sha1 m) salt))
    (length
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt)))))))) =
    roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8 - 168" using a and b and length_bvxor by simp
 then show ?thesis by simp
qed

lemma emBits_roundup_cancel: "emBits mod 8 ~= 0 \<Longrightarrow> (roundup emBits 8)*8 - emBits = 8-(emBits mod 8)"
apply (auto simp add: roundup)
by (arith)

lemma emBits_roundup_cancel2: "emBits mod 8 ~=0 \<Longrightarrow> (roundup emBits 8) * 8 - (8-(emBits mod 8)) = emBits"
by (auto simp add: roundup)

lemma length_bound: "\<lbrakk>emBits mod 8 ~=0; 8 <= (length maskedDB)\<rbrakk> \<Longrightarrow> length (remzero ((maskedDB_zero maskedDB emBits)@a@b)) <= length (maskedDB@a@b) - (8-(emBits mod 8))"
proof -
  assume a: "emBits mod 8 ~=0"
  assume len: "8 <= (length maskedDB)"
  have b:" \<And> a. length (remzero a) <= length a"
  proof -
    fix a
    show "length (remzero a) <= length a"
    proof (induct a)
      show "(length (remzero [])) <= length []" by (simp)
    next
      case (Cons hd tl)
      show "(length (remzero (hd#tl))) <= length (hd#tl)"
      proof (cases hd)
        assume "hd=\<zero>"
        then have "remzero (hd#tl) = remzero tl" by simp
        then show ?thesis using Cons by simp
      next
        assume "hd=\<one>"
        then have "remzero (hd#tl) = hd#tl" by simp
        then show ?thesis by simp
      qed
    qed
  qed
  from len show "length (remzero (maskedDB_zero maskedDB emBits @ a @ b)) \<le> length (maskedDB @ a @ b) - (8 - emBits mod 8)"
  proof -
    have "remzero(bv_prepend ((roundup emBits 8) * 8 - emBits)
      \<zero> (drop ((roundup emBits 8)*8 - emBits) maskedDB)@a@b) = remzero ((drop ((roundup emBits 8)*8 -emBits) maskedDB)@a@b)" using remzero_replicate by (simp add: bv_prepend)
    moreover from emBits_roundup_cancel have "roundup emBits 8 * 8 - emBits = 8 - emBits mod 8" using a by simp
    moreover have "length ((drop (8-emBits mod 8) maskedDB)@a@b) = length (maskedDB@a@b) - (8-emBits mod 8)" 
    proof -
      show ?thesis using length_drop[of "(8-emBits mod 8)" maskedDB] 
      proof (simp)
        have "0 <= emBits mod 8" by simp
        then have "8-(emBits mod 8) <= 8" by simp
        then show  "length maskedDB + emBits mod 8 - 8 + (length a + length b) =
          length maskedDB + (length a + length b) + emBits mod 8 - 8" using len by arith
      qed
    qed
    ultimately show ?thesis using b[of "(drop ((roundup emBits 8)*8 - emBits) maskedDB)@a@b"]
      by (simp add: maskedDB_zero_def)
  qed
qed

lemma length_bound2: "8<=length ( (bvxor
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))
  (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))))))" 
proof -
  have "8 <= length (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))" by (simp add: generate_DB_def)
  then show ?thesis using length_bvxor_bound by simp
qed

lemma length_helper: assumes p: "prime p" and q: "prime q" and x: "(length (nat_to_bv (p * q)) - Suc 0) mod 8 ~= 0" and mgf: "(MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))) ~= []"  
  and len: "length (sha1 M) + sLen + 16 \<le> (length (nat_to_bv (p * q))) - Suc 0"
  shows "length
  (remzero
  (maskedDB_zero
  (bvxor
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt)))))
  (MGF (sha1 (generate_M' (sha1 m) salt))
  (length
  (generate_DB
  (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
  (length (sha1 (generate_M' (sha1 m) salt))))))))
  (length (nat_to_bv (p * q)) - Suc 0) @
  sha1 (generate_M' (sha1 m) salt) @ BC))
  < length (nat_to_bv (p * q))"
proof -
  from mgf have round: "168 <= roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8"
  proof (simp only: sha1len sLen_def)
    from len have "160 + sLen +16 \<le> length (nat_to_bv (p * q)) - Suc 0" by (simp add: sha1len)
    then have len1: "176 <= length (nat_to_bv (p * q)) - Suc 0" by simp
    have "length (nat_to_bv (p*q)) - Suc 0 <= (roundup (length (nat_to_bv (p * q)) - Suc 0) 8) * 8"
      unfolding roundup
    proof (cases "(length (nat_to_bv (p*q)) - Suc 0) mod 8 = 0")
      assume len2: "(length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0" 
      then have "(if (length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0 then (length (nat_to_bv (p * q)) - Suc 0) div 8 else (length (nat_to_bv (p * q)) - Suc 0) div 8 + 1) * 8 = (length (nat_to_bv (p * q)) - Suc 0) div 8 * 8" by simp
      moreover have "(length (nat_to_bv (p * q)) - Suc 0) div 8 * 8 = (length (nat_to_bv (p * q)) - Suc 0)" using len2
        by auto
      ultimately show "length (nat_to_bv (p * q)) - Suc 0
        \<le> (if (length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0 then (length (nat_to_bv (p * q)) - Suc 0) div 8 else (length (nat_to_bv (p * q)) - Suc 0) div 8 + 1) * 8" by simp
    next
      assume len2: "(length (nat_to_bv (p*q)) - Suc 0) mod 8 ~= 0"
      then have "(if (length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0 then (length (nat_to_bv (p * q)) - Suc 0) div 8 else (length (nat_to_bv (p * q)) - Suc 0) div 8 + 1) * 8 = ((length (nat_to_bv (p * q)) - Suc 0) div 8 + 1) * 8" by simp
      moreover have "length (nat_to_bv (p*q)) - Suc 0 <= ((length (nat_to_bv (p*q)) - Suc 0) div 8 + 1)*8" by auto
      ultimately show "length (nat_to_bv (p * q)) - Suc 0
        \<le> (if (length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0 then (length (nat_to_bv (p * q)) - Suc 0) div 8 else (length (nat_to_bv (p * q)) - Suc 0) div 8 + 1) * 8" by simp
    qed
    then show "168 \<le> roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8" using len1 by simp
  qed
  from x have a: "length
    (remzero
    (maskedDB_zero
    (bvxor
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt)))))
    (MGF (sha1 (generate_M' (sha1 m) salt))
    (length
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt))))))))
    (length (nat_to_bv (p * q)) - Suc 0) @
    sha1 (generate_M' (sha1 m) salt) @ BC)) <= length ((bvxor
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt)))))
    (MGF (sha1 (generate_M' (sha1 m) salt))
    (length
    (generate_DB
    (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
    (length (sha1 (generate_M' (sha1 m) salt)))))))) @
    sha1 (generate_M' (sha1 m) salt) @ BC) - (8 - (length (nat_to_bv (p*q)) - Suc 0) mod 8)" using length_bound and length_bound2 by simp
  have b: " length (bvxor (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))
             (MGF (sha1 (generate_M' (sha1 m) salt)) (length (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt))))))) @
            sha1 (generate_M' (sha1 m) salt) @ BC) =  length (bvxor (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))
             (MGF (sha1 (generate_M' (sha1 m) salt)) (length (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))))) +168" using length_helper1 by simp
  have c: "length (bvxor (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))
           (MGF (sha1 (generate_M' (sha1 m) salt)) (length (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))))) = 
            (roundup (length (nat_to_bv (p * q)) - Suc 0) 8) * 8 - 168" using p and q and length_helper2 and mgf and len by simp
  from a and b and c have " length (remzero (maskedDB_zero
                    (bvxor (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))
                      (MGF (sha1 (generate_M' (sha1 m) salt))
                        (length (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt))))))))
                    (length (nat_to_bv (p * q)) - Suc 0) @
                   sha1 (generate_M' (sha1 m) salt) @ BC)) <=  roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8 - 168 +168 - (8 - (length (nat_to_bv (p * q)) - Suc 0) mod 8)" by simp 
  then have "length (remzero (maskedDB_zero
                    (bvxor (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt)))))
                      (MGF (sha1 (generate_M' (sha1 m) salt))
                        (length (generate_DB (generate_PS (length (nat_to_bv (p * q)) - Suc 0) (length (sha1 (generate_M' (sha1 m) salt))))))))
                    (length (nat_to_bv (p * q)) - Suc 0) @
                   sha1 (generate_M' (sha1 m) salt) @ BC)) <= roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8 - (8 - (length (nat_to_bv (p * q)) - Suc 0) mod 8)" using round by simp
  moreover have "  roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8 - (8 - (length (nat_to_bv (p * q)) - Suc 0) mod 8) = (length (nat_to_bv (p*q))-Suc 0)" using x and emBits_roundup_cancel2 by simp
  moreover have "0<length (nat_to_bv (p*q))" 
  proof -
    from p have s: "1<p" by (simp add: prime_nat_iff)
    moreover from q have "1<q" by (simp add: prime_nat_iff)
    ultimately have "p<p*q" by simp 
    then have "1<p*q" using s by arith
    then show ?thesis using len_nat_to_bv_pos by simp
  qed
  ultimately show ?thesis by arith
qed

lemma length_emsapss_smaller_pq: "\<lbrakk>prime p; prime q; emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0) \<noteq> []; (length (nat_to_bv (p * q)) - Suc 0) mod 8 ~= 0\<rbrakk> \<Longrightarrow>  length (remzero (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0))) < length (nat_to_bv (p*q))"
proof -
  assume a: "emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0) \<noteq> []"
  assume p: "prime p" and q: "prime q"
  assume x: "(length (nat_to_bv (p * q)) - Suc 0) mod 8 ~= 0"
  have b: " emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)= emsapss_encode_help1 (sha1 m)
    (length (nat_to_bv (p * q)) - Suc 0)"
  proof (simp only: emsapss_encode_def)
    from a show "(if ((2^64 \<le> length m) \<or> (2^32 * 160 < (length (nat_to_bv (p*q)) - Suc 0)))
      then []
      else (emsapss_encode_help1 (sha1 m) (length (nat_to_bv (p*q))- Suc 0))) = (emsapss_encode_help1 (sha1 m) (length (nat_to_bv (p*q)) - Suc 0))"
      by (auto simp add: emsapss_encode_def)
  qed
  have c: "length (remzero (emsapss_encode_help1 (sha1 m) (length (nat_to_bv (p * q)) - Suc 0))) < length (nat_to_bv (p*q))"
  proof (simp only: emsapss_encode_help1_def) 
     from a and b have d: "(if ((length (nat_to_bv (p * q)) - Suc 0) < (length (sha1 m) + sLen + 16))
      then []
      else (emsapss_encode_help2 (generate_M' (sha1 m) salt)
      (length (nat_to_bv (p * q)) - Suc 0))) = (emsapss_encode_help2 ((generate_M' (sha1 m)) salt) (length (nat_to_bv (p*q)) - Suc 0))"
        by (auto simp add: emsapss_encode_def emsapss_encode_help1_def)
     from d have len: "length (sha1 m) + sLen + 16 <= (length (nat_to_bv (p*q))) - Suc 0"
     proof (cases "length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16")
       assume "length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16"
       then have len1: "(if length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16 then []
      else emsapss_encode_help2 (generate_M' (sha1 m) salt) (length (nat_to_bv (p * q)) - Suc 0)) = []" by simp
       assume len2:  "(if length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16 then []
      else emsapss_encode_help2 (generate_M' (sha1 m) salt) (length (nat_to_bv (p * q)) - Suc 0)) =
     emsapss_encode_help2 (generate_M' (sha1 m) salt) (length (nat_to_bv (p * q)) - Suc 0)"
       from len1 and len2 and a and b show "length (sha1 m) + sLen + 16 \<le> length (nat_to_bv (p * q)) - Suc 0"
        by (auto simp add: emsapss_encode_def emsapss_encode_help1_def)
     next
       assume "\<not> length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16"
       then show "length (sha1 m) + sLen + 16 \<le> length (nat_to_bv (p * q)) - Suc 0" by simp
     qed
    have e: "length (remzero (emsapss_encode_help2 (generate_M' (sha1 m) salt)
   (length (nat_to_bv (p * q)) - Suc 0))) < length (nat_to_bv (p * q))"
      proof (simp only: emsapss_encode_help2_def)
        show "length
          (remzero
          (emsapss_encode_help3 (sha1 (generate_M' (sha1 m) salt))
          (length (nat_to_bv (p * q)) - Suc 0)))
          < length (nat_to_bv (p * q))"
        proof (simp add: emsapss_encode_help3_def emsapss_encode_help4_def emsapss_encode_help5_def)
          show "length
            (remzero
            (emsapss_encode_help6
            (generate_DB
            (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
            (length (sha1 (generate_M' (sha1 m) salt)))))
            (MGF (sha1 (generate_M' (sha1 m) salt))
            (length
            (generate_DB
            (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
            (length (sha1 (generate_M' (sha1 m) salt)))))))
            (sha1 (generate_M' (sha1 m) salt))
            (length (nat_to_bv (p * q)) - Suc 0)))
            < length (nat_to_bv (p * q))"
          proof (simp only: emsapss_encode_help6_def)
            from a and b and d have mgf: "MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))) ~=
              []" by (auto simp add: emsapss_encode_def emsapss_encode_help1_def emsapss_encode_help2_def emsapss_encode_help3_def emsapss_encode_help4_def emsapss_encode_help5_def emsapss_encode_help6_def)
            from a and b and d have f: "(if MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))) =
              []
              then []
              else (emsapss_encode_help7
              (bvxor
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))
              (MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt))))))))
              (sha1 (generate_M' (sha1 m) salt))
              (length (nat_to_bv (p * q)) - Suc 0))) = (emsapss_encode_help7
              (bvxor
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))
              (MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt))))))))
              (sha1 (generate_M' (sha1 m) salt))
              (length (nat_to_bv (p * q)) - Suc 0))"
              by (auto simp add: emsapss_encode_def emsapss_encode_help1_def emsapss_encode_help2_def
                emsapss_encode_help3_def emsapss_encode_help4_def emsapss_encode_help5_def
                emsapss_encode_help6_def)
            have "length (remzero (emsapss_encode_help7
              (bvxor
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))
              (MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt))))))))
              (sha1 (generate_M' (sha1 m) salt)) (length (nat_to_bv (p * q)) - Suc 0))) < length (nat_to_bv (p * q))"
            proof (simp add: emsapss_encode_help7_def emsapss_encode_help8_def)
              from p and q and x show " length
                (remzero
                (maskedDB_zero
                (bvxor
                (generate_DB
                (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
                (length (sha1 (generate_M' (sha1 m) salt)))))
                (MGF (sha1 (generate_M' (sha1 m) salt))
                (length
                (generate_DB
                (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
                (length (sha1 (generate_M' (sha1 m) salt))))))))
                (length (nat_to_bv (p * q)) - Suc 0) @
                sha1 (generate_M' (sha1 m) salt) @ BC))
                < length (nat_to_bv (p * q))" using "length_helper" and len and mgf by simp
            qed
            then show "length
              (remzero
              (if MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))) =
              []
              then []
              else emsapss_encode_help7
              (bvxor
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt)))))
              (MGF (sha1 (generate_M' (sha1 m) salt))
              (length
              (generate_DB
              (generate_PS (length (nat_to_bv (p * q)) - Suc 0)
              (length (sha1 (generate_M' (sha1 m) salt))))))))
              (sha1 (generate_M' (sha1 m) salt))
              (length (nat_to_bv (p * q)) - Suc 0)))
              < length (nat_to_bv (p * q))" using f by simp
          qed
        qed
      qed
    from d and e show "length
      (remzero
      (if length (nat_to_bv (p * q)) - Suc 0 < length (sha1 m) + sLen + 16
      then []
      else emsapss_encode_help2 (generate_M' (sha1 m) salt)
      (length (nat_to_bv (p * q)) - Suc 0)))
      < length (nat_to_bv (p * q))" by simp
  qed
  from b and c show ?thesis by simp
qed

lemma bv_to_nat_emsapss_smaller_pq: assumes a: "prime p" and b: "prime q" and pneq: "p ~= q" and c: "emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0) \<noteq> []" shows "bv_to_nat (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)) < p*q"
proof -
  from a and b and c show ?thesis
  proof (cases "8 dvd ((length (nat_to_bv (p * q))) - Suc 0)")
    assume d: "8 dvd ((length (nat_to_bv (p * q))) - Suc 0)"
    then have "2 ^ (roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8) < p*q"
    proof -
      from d have e: "roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8 = length (nat_to_bv (p * q)) - Suc 0" using rnddvd by simp
      have "p*q = bv_to_nat (nat_to_bv (p*q))" by simp
      then have "2 ^ (length (nat_to_bv (p * q)) - Suc 0) < p*q"
      proof -
        have "0<p*q"
        proof -
          have "0<p" using a by (simp add: prime_nat_iff)
          moreover have "0<q" using b by (simp add: prime_nat_iff)
          ultimately show ?thesis by simp
        qed
        moreover have "2^(length (nat_to_bv (p*q)) - Suc 0) ~= p*q" 
        proof (cases "2^(length (nat_to_bv (p*q)) - Suc 0) = p*q")
          assume "2^(length (nat_to_bv (p*q)) - Suc 0) = p*q"
          then have "p=q" using a and b and prime_equal by simp
          then show ?thesis using pneq by simp
        next
          assume "2^(length (nat_to_bv (p*q)) - Suc 0) ~= p*q"
          then show ?thesis by simp
        qed
        ultimately show ?thesis using len_lower_bound[of "p*q"] by (simp)
      qed
      then show ?thesis using e by simp
    qed
    moreover from c have "bv_to_nat (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)) < 2 ^ (roundup (length (nat_to_bv (p * q)) - Suc 0)8 * 8 )" 
      using bv_to_nat_emsapss_encode_le [of m "(length (nat_to_bv (p * q)) - Suc 0)"] by auto
    ultimately show ?thesis by simp
  next
    assume y: "~(8 dvd (length (nat_to_bv (p*q)) - Suc 0))"
    then show ?thesis
    proof -
      from y have x: "~((length (nat_to_bv (p * q)) - Suc 0) mod 8 = 0)" by (simp add: dvd_eq_mod_eq_0)
      from remzeroeq have d: "bv_to_nat (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)) = bv_to_nat (remzero (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)))" by simp
      from a and b and c and x and length_emsapss_smaller_pq[of p q m] have "bv_to_nat (remzero (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0))) < bv_to_nat (nat_to_bv (p*q))" using length_lower[of "remzero (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0))" "nat_to_bv (p * q)"] and prime_hd_non_zero[of p q] by (auto)
      then show "bv_to_nat (emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)) < p * q" using d and bv_nat_bv by simp
    qed
  qed
qed

lemma rsa_pss_verify: "\<lbrakk> prime p; prime q; p \<noteq> q; n = p*q; e*d mod ((pred p)*(pred q)) = 1; rsapss_sign m e n \<noteq> []; s = rsapss_sign m e n \<rbrakk> \<Longrightarrow> rsapss_verify m s d n = True" 
  apply (simp only: rsapss_sign_def rsapss_verify_def)
  apply (simp only: rsapss_sign_help1_def)
  apply (auto)
  apply (simp add: length_nat_to_bv_length)
  apply (simp add: bv_to_nat_nat_to_bv_length)
  apply (insert length_emsapss_encode [of m "(length (nat_to_bv (p * q)) - Suc 0)"])
  apply (insert bv_to_nat_emsapss_smaller_pq [of p q m])
  apply (simp add: cryptinverts)
  apply (insert length_emsapss_encode [of m "(length (nat_to_bv (p * q)) - Suc 0)"])
  apply (insert nat_to_bv_length_bv_to_nat [of "emsapss_encode m (length (nat_to_bv (p * q)) - Suc 0)" "roundup (length (nat_to_bv (p * q)) - Suc 0) 8 * 8"])
  apply (simp add: verify)
  done

end

