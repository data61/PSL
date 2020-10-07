(*  Title:      RSAPSS/Wordoperations.thy
    Author:     Christina Lindenberg, Kai Wirt, Technische Universität Darmstadt
    Copyright:  2005 - Technische Universität Darmstadt
*)

section  \<open>Extensions to the Word theory required for SHA1\<close>

theory WordOperations
imports Word
begin

type_synonym bv = "bit list"

datatype HEX = x0 | x1 | x2 | x3 | x4 | x5 | x6 | x7 | x8 | x9 | xA | xB | xC | xD | xE | xF

definition
  bvxor: "bvxor a b = bv_mapzip (\<oplus>\<^sub>b) a b"

definition
  bvand: "bvand a b = bv_mapzip (\<and>\<^sub>b) a b"

definition
  bvor: "bvor a b = bv_mapzip (\<or>\<^sub>b) a b"

primrec last where
  "last [] = Zero"
| "last (x#r) = (if (r=[]) then x else (last r))"

primrec dellast where
  "dellast [] = []"
| "dellast (x#r) = (if (r = []) then [] else (x#dellast r))"

fun bvrol where
  "bvrol a 0 = a"
| "bvrol [] x = []"
| "bvrol (x#r) (Suc n) = bvrol (r@[x]) n"

fun bvror where
  "bvror a 0 = a"
| "bvror [] x = []"
| "bvror x (Suc n) = bvror (last x # dellast x) n"

fun selecthelp where
  "selecthelp [] n = (if (n <= 0) then [Zero] else (Zero # selecthelp [] (n-(1::nat))))"
| "selecthelp (x#l) n = (if (n <= 0) then [x] else (x # selecthelp l (n-(1::nat))))" 

fun select where
  "select [] i n = (if (i <= 0) then (selecthelp [] n) else select [] (i-(1::nat)) (n-(1::nat)))"
| "select (x#l) i n = (if (i <= 0) then (selecthelp (x#l) n) else select l (i-(1::nat)) (n-(1::nat)))"

definition
  addmod32: "addmod32 a b =
    rev (select (rev (nat_to_bv ((bv_to_nat a) + (bv_to_nat b)))) 0 31)"

definition
  bv_prepend: "bv_prepend x b bv = replicate x b @ bv"

primrec zerolist where
  "zerolist 0 = []"
| "zerolist (Suc n) = zerolist n  @ [Zero]"

primrec hextobv where
  "hextobv x0 = [Zero,Zero,Zero,Zero]"
| "hextobv x1 = [Zero,Zero,Zero,One]"
| "hextobv x2 = [Zero,Zero,One,Zero]"
| "hextobv x3 = [Zero,Zero,One,One]"
| "hextobv x4 = [Zero,One,Zero,Zero]"
| "hextobv x5 = [Zero,One,Zero,One]"
| "hextobv x6 = [Zero,One,One,Zero]"
| "hextobv x7 = [Zero,One,One,One]"
| "hextobv x8 = [One,Zero,Zero,Zero]"
| "hextobv x9 = [One,Zero,Zero,One]"
| "hextobv xA = [One,Zero,One,Zero]"
| "hextobv xB = [One,Zero,One,One]"
| "hextobv xC = [One,One,Zero,Zero]"
| "hextobv xD = [One,One,Zero,One]"
| "hextobv xE = [One,One,One,Zero]"
| "hextobv xF = [One,One,One,One]"

primrec hexvtobv where
  "hexvtobv [] = []"
| "hexvtobv (x#r) = hextobv x @ hexvtobv r"

lemma selectlenhelp: "length (selecthelp l i) = (i + 1)"
proof (induct i arbitrary: l)
  case 0
  show "length (selecthelp l 0) = 0 + 1"
  proof (cases l)
    case Nil
    then have "selecthelp l 0 = [Zero]" by simp
    then show ?thesis by simp
  next
    case (Cons a as)
    then have "selecthelp l 0 = [a]" by simp
    then show ?thesis by simp
  qed
next
  case (Suc x)
  show "length (selecthelp l (Suc x)) = (Suc x) + 1"
  proof (cases l)
    case Nil
    then have "selecthelp l (Suc x) = Zero # selecthelp l x" by simp 
    then show "length (selecthelp l (Suc x)) = Suc x + 1" using Suc by simp
  next
    case (Cons a b)
    then have "selecthelp l (Suc x) = a # selecthelp b x" by simp
    then have "length (selecthelp l (Suc x)) = 1 + length (selecthelp b x)" by simp
    then show "length (selecthelp l (Suc x)) = Suc x + 1" using Suc by simp
  qed
qed

lemma selectlenhelp2:  "\<And>i. \<forall>l j. \<exists>k. select l i j = select k 0 (j - i)"
proof (auto)
  fix i
  show "\<And>l j. \<exists>k. select l i j = select k 0 (j - i)"
  proof (induct i)
    fix l and j 
    have "select l 0 j = select l 0 (j-(0::nat))" by simp
    then show "\<exists>k. select l 0 j = select k 0 (j - (0::nat))" by auto
  next
    case (Suc x)
    have b: "select l (Suc x) j = select (tl l) x (j-(1::nat))"
    proof (cases l)
      case Nil
      then have "select l (Suc x) j = select l x (j-(1::nat))" by simp
      moreover have "tl l = l" using Nil by simp
      ultimately show ?thesis by (simp)
    next
      case (Cons head tail)
      then have "select l (Suc x) j = select tail x (j-(1::nat))" by simp
      moreover have "tail = tl l" using Cons by simp
      ultimately show ?thesis by simp
    qed
    have "\<exists>k. select l x j = select k 0 (j - (x::nat))" using Suc by simp
    moreover have  "\<exists>k. select (tl l) x (j-(1::nat)) = select k 0 (j-(1::nat)-(x::nat))" using Suc[of "tl l" "j-(1::nat)"] by auto
    ultimately have "\<exists>k. select l (Suc x) j = select k 0 (j-(1::nat) - (x::nat))" using b by auto
    then show "\<exists>k. select l (Suc x) j = select k 0 (j - Suc x)" by simp
  qed
qed

lemma selectlenhelp3: "\<forall>j. select l 0 j = selecthelp l j"
proof
  fix j
  show "select l 0 j = selecthelp l j"
  proof (cases l)
    case Nil
    assume "l=[]"
    then show "select l 0 j = selecthelp l j" by simp
  next
    case (Cons a b)
    then show "select l 0 j = selecthelp l j" by simp
  qed
qed

lemma selectlen: "length (select l i j) = j - i + 1"
proof -
  from selectlenhelp2 have "\<exists>k. select l i j = select k 0 (j-i)" by simp
  then have "\<exists>k. length (select l i j) = length (select k 0 (j-i))" by auto
  then have c: "\<exists>k. length (select l i j) = length (selecthelp k (j-i))"
    using selectlenhelp3 by simp
  from c obtain k where d: "length (select l i j) = length (selecthelp k (j-i))" by auto
  have "0<=j-i" by arith
  then have "length (selecthelp k (j-i)) = j-i+1" using selectlenhelp by simp
  then show "length (select l i j) = j-i+1" using d by simp
qed

lemma addmod32len: "\<And> a b. length (addmod32 a b) = 32"
  using selectlen [of _ 0 31] addmod32 by simp

end
