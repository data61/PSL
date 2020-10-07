(*  Title:      RSAPSS/SHA1.thy
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt
*)

section  "Formal definition of the secure hash algorithm"

theory SHA1
imports SHA1Padding
begin

text \<open>We define the secure hash algorithm SHA-1 and give a proof for the
  length of the message digest\<close>

definition fif where
  fif: "fif x y z = bvor (bvand x y) (bvand (bv_not x) z)"

definition fxor where
  fxor: "fxor x y z = bvxor (bvxor x y) z"

definition fmaj where
  fmaj: "fmaj x y z = bvor (bvor (bvand x y) (bvand x z)) (bvand y z)"

definition fselect :: "nat \<Rightarrow> bit list \<Rightarrow> bit list \<Rightarrow> bit list \<Rightarrow> bit list" where
  fselect: "fselect r x y z = (if (r < 20) then (fif x y z) else 
                        (if (r < 40) then (fxor x y z) else
                          (if (r < 60) then (fmaj x y z) else
                             (fxor x y z))))"

definition K1 where
  K1: "K1 = hexvtobv [x5,xA,x8,x2,x7,x9,x9,x9]"

definition K2 where
  K2: "K2 = hexvtobv [x6,xE,xD,x9,xE,xB,xA,x1]"

definition K3 where
  K3: "K3 = hexvtobv [x8,xF,x1,xB,xB,xC,xD,xC]"
 
definition K4 where
  K4: "K4 = hexvtobv [xC,xA,x6,x2,xC,x1,xD,x6]"

definition kselect :: "nat \<Rightarrow> bit list" where
  kselect: "kselect r = (if (r < 20) then K1 else 
                    (if (r < 40) then K2 else
                        (if (r < 60) then K3 else
                            K4)))"

definition getblock where
  getblock: "getblock x = select x 0 511"

fun delblockhelp where
  "delblockhelp [] n = []"
  | "delblockhelp (x#r) n = (if n <= 0 then x#r else delblockhelp r (n-(1::nat)))"

definition delblock where
  delblock: "delblock x = delblockhelp x 512"

primrec sha1compress where
  "sha1compress 0 b A B C D E = (let j = (79::nat) in
                                       (let W = select b (32*j) ((32*j)+31) in 
                                        (let AA = addmod32 (addmod32 (addmod32 W (bvrol A 5)) (fselect j B C D)) (addmod32 E (kselect j));
                                             BB = A;
                                             CC = bvrol B 30;
                                             DD = C;
                                             EE = D in
                                AA@BB@CC@DD@EE)))"
 | "sha1compress (Suc n) b A B C D E = (let j = (79 - (Suc n)) in
                                       (let W = select b (32*j) ((32*j)+31) in 
                                        (let AA = addmod32 (addmod32 (addmod32 W (bvrol A 5)) (fselect j B C D)) (addmod32 E (kselect j));
                                             BB = A;
                                             CC = bvrol B 30;
                                             DD = C;
                                             EE = D in
                               sha1compress n b AA BB CC DD EE)))"

definition sha1expandhelp where
  "sha1expandhelp x i = (let j = (79+16-i) in (bvrol (bvxor(bvxor(
    select x (32*(j-(3::nat))) (31+(32*(j-(3::nat))))) (select x (32*(j-(8::nat))) (31+(32*(j-(8::nat)))))) (bvxor(select x (32*(j-(14::nat))) (31+(32*(j-(14::nat))))) (select x (32*(j-(16::nat))) (31+(32*(j-(16::nat))))))) 1))"

fun sha1expand where
  "sha1expand x i = (if (i < 16) then x else
     let y = sha1expandhelp x i in
   sha1expand (x @ y) (i - 1))"

definition sha1compressstart where
  sha1compressstart: "sha1compressstart r b A B C D E = sha1compress r (sha1expand b 79) A B C D E"

function (sequential) sha1block where
  "sha1block b [] A B C D E = (let H = sha1compressstart 79 b A B C D E;
                                   AA = addmod32 A (select H 0 31);
                                   BB = addmod32 B (select H 32 63);
                                   CC = addmod32 C (select H 64 95);
                                   DD = addmod32 D (select H 96 127);
                                   EE = addmod32 E (select H 128 159)
                               in AA@BB@CC@DD@EE)"
  | "sha1block b x A B C D E =  (let H = sha1compressstart 79 b A B C D E;
                                     AA = addmod32 A (select H 0 31);
                                     BB = addmod32 B (select H 32 63);
                                     CC = addmod32 C (select H 64 95);
                                     DD = addmod32 D (select H 96 127);
                                     EE = addmod32 E (select H 128 159)
                               in sha1block (getblock x) (delblock x) AA BB CC DD E)"
by pat_completeness auto

termination proof -
  have aux: "\<And>n xs :: bit list. length (delblockhelp xs n) <= length xs" 
  proof -
    fix n and xs :: "bit list"
    show "length (delblockhelp xs n) \<le> length xs" 
      by (induct n rule: delblockhelp.induct) auto
  qed
  have "\<And>x xs :: bit list. length (delblock (x#xs)) < Suc (length xs)"
  proof -
    fix x and xs :: "bit list"
    from aux have "length (delblockhelp xs 511) < Suc (length xs)"
    using le_less_trans [of "length (delblockhelp xs 511)" "length xs"] by auto
    then show "length (delblock (x#xs)) < Suc (length xs)" by (simp add: delblock)
  qed
  then show ?thesis
    by (relation "measure (\<lambda>(b, x, A, B, C, D, E). length x)") auto
qed

definition IV1 where
  IV1: "IV1 = hexvtobv [x6,x7,x4,x5,x2,x3,x0,x1]"

definition IV2 where
  IV2: "IV2 = hexvtobv [xE,xF,xC,xD,xA,xB,x8,x9]"

definition IV3 where
  IV3: "IV3 = hexvtobv [x9,x8,xB,xA,xD,xC,xF,xE]"

definition IV4 where
  IV4: "IV4 = hexvtobv [x1,x0,x3,x2,x5,x4,x7,x6]"

definition IV5 where
  IV5: "IV5 = hexvtobv [xC,x3,xD,x2,xE,x1,xF,x0]"

definition sha1 where
  sha1: "sha1 x = (let y = sha1padd x in
  sha1block (getblock y) (delblock y) IV1 IV2 IV3 IV4 IV5)"


lemma sha1blocklen: "length (sha1block b x A B C D E) = 160"
proof (induct b x A B C D E rule: sha1block.induct)
  case 1 show ?case by (simp add: Let_def addmod32len)
next
  case 2 then show ?case by (simp add: Let_def)
qed

lemma sha1len: "length (sha1 m) = 160"
  unfolding sha1 Let_def sha1blocklen ..

end
