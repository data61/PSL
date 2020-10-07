(*  Title:      JinjaThreads/Common/BinOp.thy
    Author:     Andreas Lochbihler
*)

section \<open>Binary Operators\<close>

theory BinOp
imports
  WellForm
begin

datatype bop =  \<comment> \<open>names of binary operations\<close>
    Eq
  | NotEq
  | LessThan
  | LessOrEqual
  | GreaterThan
  | GreaterOrEqual
  | Add    
  | Subtract
  | Mult
  | Div
  | Mod
  | BinAnd
  | BinOr
  | BinXor
  | ShiftLeft
  | ShiftRightZeros
  | ShiftRightSigned

subsection\<open>The semantics of binary operators\<close>

type_synonym 'addr binop_ret = "'addr val + 'addr" \<comment> \<open>a value or the address of an exception\<close>

fun binop_LessThan :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_LessThan (Intg i1) (Intg i2) = Some (Inl (Bool (i1 <s i2)))"
| "binop_LessThan v1 v2 = None"

fun binop_LessOrEqual :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_LessOrEqual (Intg i1) (Intg i2) = Some (Inl (Bool (i1 <=s i2)))"
| "binop_LessOrEqual v1 v2 = None"

fun binop_GreaterThan :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_GreaterThan (Intg i1) (Intg i2) = Some (Inl (Bool (i2 <s i1)))"
| "binop_GreaterThan v1 v2 = None"

fun binop_GreaterOrEqual :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_GreaterOrEqual (Intg i1) (Intg i2) = Some (Inl (Bool (i2 <=s i1)))"
| "binop_GreaterOrEqual v1 v2 = None"

fun binop_Add :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_Add (Intg i1) (Intg i2) = Some (Inl (Intg (i1 + i2)))"
| "binop_Add v1 v2 = None"

fun binop_Subtract :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_Subtract (Intg i1) (Intg i2) = Some (Inl (Intg (i1 - i2)))"
| "binop_Subtract v1 v2 = None"

fun binop_Mult :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_Mult (Intg i1) (Intg i2) = Some (Inl (Intg (i1 * i2)))"
| "binop_Mult v1 v2 = None"

fun binop_BinAnd :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_BinAnd (Intg i1) (Intg i2) = Some (Inl (Intg (i1 AND i2)))"
| "binop_BinAnd (Bool b1) (Bool b2) = Some (Inl (Bool (b1 \<and> b2)))"
| "binop_BinAnd v1 v2 = None"

fun binop_BinOr :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_BinOr (Intg i1) (Intg i2) = Some (Inl (Intg (i1 OR i2)))"
| "binop_BinOr (Bool b1) (Bool b2) = Some (Inl (Bool (b1 \<or> b2)))"
| "binop_BinOr v1 v2 = None"

fun binop_BinXor :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_BinXor (Intg i1) (Intg i2) = Some (Inl (Intg (i1 XOR i2)))"
| "binop_BinXor (Bool b1) (Bool b2) = Some (Inl (Bool (b1 \<noteq> b2)))"
| "binop_BinXor v1 v2 = None"

fun binop_ShiftLeft :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_ShiftLeft (Intg i1) (Intg i2) = Some (Inl (Intg (i1 << unat (i2 AND 0x1f))))"
| "binop_ShiftLeft v1 v2 = None"

fun binop_ShiftRightZeros :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_ShiftRightZeros (Intg i1) (Intg i2) = Some (Inl (Intg (i1 >> unat (i2 AND 0x1f))))"
| "binop_ShiftRightZeros v1 v2 = None"

fun binop_ShiftRightSigned :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_ShiftRightSigned (Intg i1) (Intg i2) = Some (Inl (Intg (i1 >>> unat (i2 AND 0x1f))))"
| "binop_ShiftRightSigned v1 v2 = None"

text \<open>
  Division on @{typ "'a word"} is unsigned, but JLS specifies signed division.
\<close>
definition word_sdiv :: "'a :: len word \<Rightarrow> 'a word \<Rightarrow> 'a word" (infixl "sdiv" 70)
where [code]:
  "x sdiv y =
   (let x' = sint x; y' = sint y;
        negative = (x' < 0) \<noteq> (y' < 0);
        result = abs x' div abs y'
    in word_of_int (if negative then -result else result))"

definition word_smod :: "'a :: len word \<Rightarrow> 'a word \<Rightarrow> 'a word" (infixl "smod" 70)
where [code]:
  "x smod y =
   (let x' = sint x; y' = sint y;
        negative = (x' < 0);
        result = abs x' mod abs y'
    in word_of_int (if negative then -result else result))"

declare word_sdiv_def [simp] word_smod_def [simp]

lemma sdiv_smod_id: "(a sdiv b) * b + (a smod b) = a"
proof -
  have F5: "\<forall>u::'a word. - (- u) = u" by (metis word_sint.Rep_inverse' minus_minus wi_hom_neg)
  have F7: "\<forall>v u::'a word. u + v = v + u" by(metis add.left_commute add_0_right)
  have F8: "\<forall>(w::'a word) (v::int) u::int. word_of_int u + word_of_int v * w = word_of_int (u + v * sint w)"
    by (metis word_sint.Rep_inverse wi_hom_syms(1) wi_hom_syms(3))
  have "\<exists>u. u = - sint b \<and> word_of_int (sint a mod u + - (- u * (sint a div u))) = a"
    using F5 by (metis minus_minus word_sint.Rep_inverse' mult_minus_left add.commute mult_div_mod_eq [symmetric])
  hence "word_of_int (sint a mod - sint b + - (sint b * (sint a div - sint b))) = a" by (metis equation_minus_iff)
  hence "word_of_int (sint a mod - sint b) + word_of_int (- (sint a div - sint b)) * b = a"
    using F8 by(metis mult.commute mult_minus_left)
  hence eq: "word_of_int (- (sint a div - sint b)) * b + word_of_int (sint a mod - sint b) = a" using F7 by metis

  show ?thesis
  proof(cases "sint a < 0")
    case True note a = this
    show ?thesis
    proof(cases "sint b < 0")
      case True
      with a show ?thesis
        by simp (metis F7 F8 eq minus_equation_iff minus_mult_minus mod_div_mult_eq)
    next
      case False
      from eq have "word_of_int (- (- sint a div sint b)) * b + word_of_int (- (- sint a mod sint b)) = a"
        by (metis div_minus_right mod_minus_right)
      with a False show ?thesis by simp
    qed
  next
    case False note a = this
    show ?thesis
    proof(cases "sint b < 0")
      case True
      with a eq show ?thesis by simp
    next
      case False with a show ?thesis
        by simp (metis wi_hom_add wi_hom_mult add.commute mult.commute word_sint.Rep_inverse add.commute mult_div_mod_eq [symmetric])
    qed
  qed
qed

notepad begin
have  "  5  sdiv ( 3 :: word32) =  1"
  and "  5  smod ( 3 :: word32) =  2"
  and "  5  sdiv (-3 :: word32) = -1"
  and "  5  smod (-3 :: word32) =  2"
  and "(-5) sdiv ( 3 :: word32) = -1"
  and "(-5) smod ( 3 :: word32) = -2"
  and "(-5) sdiv (-3 :: word32) =  1"
  and "(-5) smod (-3 :: word32) = -2"
  and "-2147483648 sdiv 1 = (-2147483648 :: word32)"
  by eval+
end

context heap_base begin

fun binop_Mod :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_Mod (Intg i1) (Intg i2) = 
   Some (if i2 = 0 then Inr (addr_of_sys_xcpt ArithmeticException) else Inl (Intg (i1 smod i2)))"
| "binop_Mod v1 v2 = None"

fun binop_Div :: "'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop_Div (Intg i1) (Intg i2) = 
   Some (if i2 = 0 then Inr (addr_of_sys_xcpt ArithmeticException) else Inl (Intg (i1 sdiv i2)))"
| "binop_Div v1 v2 = None"

primrec binop :: "bop \<Rightarrow> 'addr val \<Rightarrow> 'addr val \<Rightarrow> 'addr binop_ret option"
where
  "binop Eq v1 v2 =  Some (Inl (Bool (v1 = v2)))"
| "binop NotEq v1 v2 = Some (Inl (Bool (v1 \<noteq> v2)))"
| "binop LessThan = binop_LessThan"
| "binop LessOrEqual = binop_LessOrEqual"
| "binop GreaterThan = binop_GreaterThan"
| "binop GreaterOrEqual = binop_GreaterOrEqual"
| "binop Add = binop_Add"
| "binop Subtract = binop_Subtract"
| "binop Mult = binop_Mult"
| "binop Mod = binop_Mod"
| "binop Div = binop_Div"
| "binop BinAnd = binop_BinAnd"
| "binop BinOr = binop_BinOr"
| "binop BinXor = binop_BinXor"
| "binop ShiftLeft = binop_ShiftLeft"
| "binop ShiftRightZeros = binop_ShiftRightZeros"
| "binop ShiftRightSigned = binop_ShiftRightSigned"

end

lemma [simp]:
  "(binop_LessThan v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Bool (i1 <s i2)))"
by(cases "(v1, v2)" rule: binop_LessThan.cases) auto

lemma [simp]:
  "(binop_LessOrEqual v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Bool (i1 <=s i2)))"
by(cases "(v1, v2)" rule: binop_LessOrEqual.cases) auto

lemma [simp]:
  "(binop_GreaterThan v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Bool (i2 <s i1)))"
by(cases "(v1, v2)" rule: binop_GreaterThan.cases) auto

lemma [simp]:
  "(binop_GreaterOrEqual v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Bool (i2 <=s i1)))"
by(cases "(v1, v2)" rule: binop_GreaterOrEqual.cases) auto

lemma [simp]:
  "(binop_Add v\<^sub>1 v\<^sub>2  = Some va) \<longleftrightarrow>
   (\<exists>i\<^sub>1 i\<^sub>2. v\<^sub>1 = Intg i\<^sub>1 \<and> v\<^sub>2 = Intg i\<^sub>2 \<and> va = Inl (Intg (i\<^sub>1+i\<^sub>2)))"
by(cases "(v\<^sub>1, v\<^sub>2)" rule: binop_Add.cases) auto

lemma [simp]:
  "(binop_Subtract v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Intg (i1 - i2)))"
by(cases "(v1, v2)" rule: binop_Subtract.cases) auto

lemma [simp]: 
  "(binop_Mult v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Intg (i1 * i2)))"
by(cases "(v1, v2)" rule: binop_Mult.cases) auto

lemma [simp]:
  "(binop_BinAnd v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>b1 b2. v1 = Bool b1 \<and> v2 = Bool b2 \<and> va = Inl (Bool (b1 \<and> b2))) \<or> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Intg (i1 AND i2)))"
by(cases "(v1, v2)" rule: binop_BinAnd.cases) auto

lemma [simp]:
  "(binop_BinOr v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>b1 b2. v1 = Bool b1 \<and> v2 = Bool b2 \<and> va = Inl (Bool (b1 \<or> b2))) \<or>
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Intg (i1 OR i2)))"
by(cases "(v1, v2)" rule: binop_BinOr.cases) auto

lemma [simp]:
  "(binop_BinXor v1 v2 = Some va) \<longleftrightarrow>
   (\<exists>b1 b2. v1 = Bool b1 \<and> v2 = Bool b2 \<and> va = Inl (Bool (b1 \<noteq> b2))) \<or>
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Intg (i1 XOR i2)))"
by(cases "(v1, v2)" rule: binop_BinXor.cases) auto

lemma [simp]:
  "(binop_ShiftLeft v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Intg (i1 << unat (i2 AND 0x1f))))"
by(cases "(v1, v2)" rule: binop_ShiftLeft.cases) auto

lemma [simp]:
  "(binop_ShiftRightZeros v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Intg (i1 >> unat (i2 AND 0x1f))))"
by(cases "(v1, v2)" rule: binop_ShiftRightZeros.cases) auto

lemma [simp]:
  "(binop_ShiftRightSigned v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> va = Inl (Intg (i1 >>> unat (i2 AND 0x1f))))"
by(cases "(v1, v2)" rule: binop_ShiftRightSigned.cases) auto

context heap_base begin

lemma [simp]:
  "(binop_Mod v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> 
      va = (if i2 = 0 then Inr (addr_of_sys_xcpt ArithmeticException) else Inl (Intg(i1 smod i2))))"
by(cases "(v1, v2)" rule: binop_Mod.cases) auto

lemma [simp]:
  "(binop_Div v1 v2 = Some va) \<longleftrightarrow> 
   (\<exists>i1 i2. v1 = Intg i1 \<and> v2 = Intg i2 \<and> 
      va = (if i2 = 0 then Inr (addr_of_sys_xcpt ArithmeticException) else Inl (Intg(i1 sdiv i2))))"
by(cases "(v1, v2)" rule: binop_Div.cases) auto

end

subsection \<open>Typing for binary operators\<close>

inductive WT_binop :: "'m prog \<Rightarrow> ty \<Rightarrow> bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _\<guillemotleft>_\<guillemotright>_ :: _" [51,0,0,0,51] 50)
where
  WT_binop_Eq:
  "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1 \<Longrightarrow> P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 :: Boolean"

| WT_binop_NotEq:
  "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1 \<Longrightarrow> P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 :: Boolean"

| WT_binop_LessThan:
  "P \<turnstile> Integer\<guillemotleft>LessThan\<guillemotright>Integer :: Boolean"

| WT_binop_LessOrEqual:
  "P \<turnstile> Integer\<guillemotleft>LessOrEqual\<guillemotright>Integer :: Boolean"

| WT_binop_GreaterThan:
  "P \<turnstile> Integer\<guillemotleft>GreaterThan\<guillemotright>Integer :: Boolean"

| WT_binop_GreaterOrEqual:
  "P \<turnstile> Integer\<guillemotleft>GreaterOrEqual\<guillemotright>Integer :: Boolean"

| WT_binop_Add:
  "P \<turnstile> Integer\<guillemotleft>Add\<guillemotright>Integer :: Integer"

| WT_binop_Subtract:
  "P \<turnstile> Integer\<guillemotleft>Subtract\<guillemotright>Integer :: Integer"

| WT_binop_Mult:
  "P \<turnstile> Integer\<guillemotleft>Mult\<guillemotright>Integer :: Integer"

| WT_binop_Div:
  "P \<turnstile> Integer\<guillemotleft>Div\<guillemotright>Integer :: Integer"

| WT_binop_Mod:
  "P \<turnstile> Integer\<guillemotleft>Mod\<guillemotright>Integer :: Integer"

| WT_binop_BinAnd_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinAnd\<guillemotright>Boolean :: Boolean"

| WT_binop_BinAnd_Int:
  "P \<turnstile> Integer\<guillemotleft>BinAnd\<guillemotright>Integer :: Integer"

| WT_binop_BinOr_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinOr\<guillemotright>Boolean :: Boolean"

| WT_binop_BinOr_Int:
  "P \<turnstile> Integer\<guillemotleft>BinOr\<guillemotright>Integer :: Integer"

| WT_binop_BinXor_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinXor\<guillemotright>Boolean :: Boolean"

| WT_binop_BinXor_Int:
  "P \<turnstile> Integer\<guillemotleft>BinXor\<guillemotright>Integer :: Integer"

| WT_binop_ShiftLeft:
  "P \<turnstile> Integer\<guillemotleft>ShiftLeft\<guillemotright>Integer :: Integer"

| WT_binop_ShiftRightZeros:
  "P \<turnstile> Integer\<guillemotleft>ShiftRightZeros\<guillemotright>Integer :: Integer"

| WT_binop_ShiftRightSigned:
  "P \<turnstile> Integer\<guillemotleft>ShiftRightSigned\<guillemotright>Integer :: Integer"

lemma WT_binopI [intro]:
  "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1 \<Longrightarrow> P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 :: Boolean"
  "P \<turnstile> T1 \<le> T2 \<or> P \<turnstile> T2 \<le> T1 \<Longrightarrow> P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 :: Boolean"
  "bop = Add \<or> bop = Subtract \<or> bop = Mult \<or> bop = Mod \<or> bop = Div \<or> bop = BinAnd \<or> bop = BinOr \<or> bop = BinXor \<or> 
   bop = ShiftLeft \<or> bop = ShiftRightZeros \<or> bop = ShiftRightSigned
   \<Longrightarrow> P \<turnstile> Integer\<guillemotleft>bop\<guillemotright>Integer :: Integer"
  "bop = LessThan \<or> bop = LessOrEqual \<or> bop = GreaterThan \<or> bop = GreaterOrEqual \<Longrightarrow> P \<turnstile> Integer\<guillemotleft>bop\<guillemotright>Integer :: Boolean"
  "bop = BinAnd \<or> bop = BinOr \<or> bop = BinXor \<Longrightarrow> P \<turnstile> Boolean\<guillemotleft>bop\<guillemotright>Boolean :: Boolean"
by(auto intro: WT_binop.intros)

inductive_cases [elim]:
  "P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>LessThan\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>LessOrEqual\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>GreaterThan\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>GreaterOrEqual\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>Add\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>Subtract\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>Mult\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>Div\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>Mod\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>BinAnd\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>BinOr\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>BinXor\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>ShiftLeft\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>ShiftRightZeros\<guillemotright>T2 :: T"
  "P \<turnstile> T1\<guillemotleft>ShiftRightSigned\<guillemotright>T2 :: T"

lemma WT_binop_fun: "\<lbrakk> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T' \<rbrakk> \<Longrightarrow> T = T'"
by(cases bop)(auto)

lemma WT_binop_is_type:
  "\<lbrakk> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T; is_type P T1; is_type P T2 \<rbrakk> \<Longrightarrow> is_type P T"
by(cases bop) auto

inductive WTrt_binop :: "'m prog \<Rightarrow> ty \<Rightarrow> bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _\<guillemotleft>_\<guillemotright>_ : _" [51,0,0,0,51] 50)
where
  WTrt_binop_Eq:
  "P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 : Boolean"

| WTrt_binop_NotEq:
  "P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 : Boolean"

| WTrt_binop_LessThan:
  "P \<turnstile> Integer\<guillemotleft>LessThan\<guillemotright>Integer : Boolean"

| WTrt_binop_LessOrEqual:
  "P \<turnstile> Integer\<guillemotleft>LessOrEqual\<guillemotright>Integer : Boolean"

| WTrt_binop_GreaterThan:
  "P \<turnstile> Integer\<guillemotleft>GreaterThan\<guillemotright>Integer : Boolean"

| WTrt_binop_GreaterOrEqual:
  "P \<turnstile> Integer\<guillemotleft>GreaterOrEqual\<guillemotright>Integer : Boolean"

| WTrt_binop_Add:
  "P \<turnstile> Integer\<guillemotleft>Add\<guillemotright>Integer : Integer"

| WTrt_binop_Subtract:
  "P \<turnstile> Integer\<guillemotleft>Subtract\<guillemotright>Integer : Integer"

| WTrt_binop_Mult:
  "P \<turnstile> Integer\<guillemotleft>Mult\<guillemotright>Integer : Integer"

| WTrt_binop_Div:
  "P \<turnstile> Integer\<guillemotleft>Div\<guillemotright>Integer : Integer"

| WTrt_binop_Mod:
  "P \<turnstile> Integer\<guillemotleft>Mod\<guillemotright>Integer : Integer"

| WTrt_binop_BinAnd_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinAnd\<guillemotright>Boolean : Boolean"

| WTrt_binop_BinAnd_Int:
  "P \<turnstile> Integer\<guillemotleft>BinAnd\<guillemotright>Integer : Integer"

| WTrt_binop_BinOr_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinOr\<guillemotright>Boolean : Boolean"

| WTrt_binop_BinOr_Int:
  "P \<turnstile> Integer\<guillemotleft>BinOr\<guillemotright>Integer : Integer"

| WTrt_binop_BinXor_Bool:
  "P \<turnstile> Boolean\<guillemotleft>BinXor\<guillemotright>Boolean : Boolean"

| WTrt_binop_BinXor_Int:
  "P \<turnstile> Integer\<guillemotleft>BinXor\<guillemotright>Integer : Integer"

| WTrt_binop_ShiftLeft:
  "P \<turnstile> Integer\<guillemotleft>ShiftLeft\<guillemotright>Integer : Integer"

| WTrt_binop_ShiftRightZeros:
  "P \<turnstile> Integer\<guillemotleft>ShiftRightZeros\<guillemotright>Integer : Integer"

| WTrt_binop_ShiftRightSigned:
  "P \<turnstile> Integer\<guillemotleft>ShiftRightSigned\<guillemotright>Integer : Integer"

lemma WTrt_binopI [intro]:
  "P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 : Boolean"
  "P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 : Boolean"
  "bop = Add \<or> bop = Subtract \<or> bop = Mult \<or> bop = Div \<or> bop = Mod \<or> bop = BinAnd \<or> bop = BinOr \<or> bop = BinXor \<or>
   bop = ShiftLeft \<or> bop = ShiftRightZeros \<or> bop = ShiftRightSigned
   \<Longrightarrow> P \<turnstile> Integer\<guillemotleft>bop\<guillemotright>Integer : Integer"
  "bop = LessThan \<or> bop = LessOrEqual \<or> bop = GreaterThan \<or> bop = GreaterOrEqual \<Longrightarrow> P \<turnstile> Integer\<guillemotleft>bop\<guillemotright>Integer : Boolean"
  "bop = BinAnd \<or> bop = BinOr \<or> bop = BinXor \<Longrightarrow> P \<turnstile> Boolean\<guillemotleft>bop\<guillemotright>Boolean : Boolean"
by(auto intro: WTrt_binop.intros)

inductive_cases WTrt_binop_cases [elim]:
  "P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>LessThan\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>LessOrEqual\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>GreaterThan\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>GreaterOrEqual\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Add\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Subtract\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Mult\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Div\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Mod\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>BinAnd\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>BinOr\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>BinXor\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>ShiftLeft\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>ShiftRightZeros\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>ShiftRightSigned\<guillemotright>T2 : T"

inductive_simps WTrt_binop_simps [simp]:
  "P \<turnstile> T1\<guillemotleft>Eq\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>NotEq\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>LessThan\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>LessOrEqual\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>GreaterThan\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>GreaterOrEqual\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Add\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Subtract\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Mult\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Div\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>Mod\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>BinAnd\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>BinOr\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>BinXor\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>ShiftLeft\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>ShiftRightZeros\<guillemotright>T2 : T"
  "P \<turnstile> T1\<guillemotleft>ShiftRightSigned\<guillemotright>T2 : T"

fun binop_relevant_class :: "bop \<Rightarrow> 'm prog \<Rightarrow> cname \<Rightarrow> bool"
where
  "binop_relevant_class Div = (\<lambda>P C. P \<turnstile> ArithmeticException \<preceq>\<^sup>* C )"
| "binop_relevant_class Mod = (\<lambda>P C. P \<turnstile> ArithmeticException \<preceq>\<^sup>* C )"
| "binop_relevant_class _ = (\<lambda>P C. False)"

lemma WT_binop_WTrt_binop:
  "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 :: T \<Longrightarrow> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T"
by(auto elim: WT_binop.cases)

context heap begin

lemma binop_progress:
  "\<lbrakk> typeof\<^bsub>h\<^esub> v1 = \<lfloor>T1\<rfloor>; typeof\<^bsub>h\<^esub> v2 = \<lfloor>T2\<rfloor>; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T \<rbrakk>
  \<Longrightarrow> \<exists>va. binop bop v1 v2 = \<lfloor>va\<rfloor>"
by(cases bop)(auto del: disjCI split del: if_split)

lemma binop_type:
  assumes wf: "wf_prog wf_md P"
  and pre: "preallocated h"
  and type: "typeof\<^bsub>h\<^esub> v1 = \<lfloor>T1\<rfloor>" "typeof\<^bsub>h\<^esub> v2 = \<lfloor>T2\<rfloor>" "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T"
  shows "binop bop v1 v2 = \<lfloor>Inl v\<rfloor> \<Longrightarrow> P,h \<turnstile> v :\<le> T"
  and "binop bop v1 v2 = \<lfloor>Inr a\<rfloor> \<Longrightarrow> P,h \<turnstile> Addr a :\<le> Class Throwable"
using type
apply(case_tac [!] bop)
apply(auto split: if_split_asm simp add: conf_def wf_preallocatedD[OF wf pre])
done

lemma binop_relevant_class:
  assumes wf: "wf_prog wf_md P"
  and pre: "preallocated h"
  and bop: "binop bop v1 v2 = \<lfloor>Inr a\<rfloor>"
  and sup: "P \<turnstile> cname_of h a \<preceq>\<^sup>* C"
  shows "binop_relevant_class bop P C"
using assms
by(cases bop)(auto split: if_split_asm)

end

lemma WTrt_binop_fun: "\<lbrakk> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T; P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T' \<rbrakk> \<Longrightarrow> T = T'"
by(cases bop)(auto)

lemma WTrt_binop_THE [simp]: "P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T \<Longrightarrow> The (WTrt_binop P T1 bop T2) = T"
by(auto dest: WTrt_binop_fun)

lemma WTrt_binop_widen_mono:
  "\<lbrakk> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T; P \<turnstile> T1' \<le> T1; P \<turnstile> T2' \<le> T2 \<rbrakk> \<Longrightarrow> \<exists>T'. P \<turnstile> T1'\<guillemotleft>bop\<guillemotright>T2' : T' \<and> P \<turnstile> T' \<le> T"
by(cases bop)(auto elim!: WTrt_binop_cases)

lemma WTrt_binop_is_type:
  "\<lbrakk> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T; is_type P T1; is_type P T2 \<rbrakk> \<Longrightarrow> is_type P T"
by(cases bop) auto

subsection \<open>Code generator setup\<close>

lemmas [code] =
  heap_base.binop_Div.simps
  heap_base.binop_Mod.simps
  heap_base.binop.simps

code_pred 
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  WT_binop
.

code_pred
  (modes: i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o \<Rightarrow> bool, i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool)
  WTrt_binop
.

lemma eval_WTrt_binop_i_i_i_i_o:
  "Predicate.eval (WTrt_binop_i_i_i_i_o P T1 bop T2) T \<longleftrightarrow> P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T"
by(auto elim: WTrt_binop_i_i_i_i_oE intro: WTrt_binop_i_i_i_i_oI)

lemma the_WTrt_binop_code:
  "(THE T. P \<turnstile> T1\<guillemotleft>bop\<guillemotright>T2 : T) = Predicate.the (WTrt_binop_i_i_i_i_o P T1 bop T2)"
by(simp add: Predicate.the_def eval_WTrt_binop_i_i_i_i_o)

end
