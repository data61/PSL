section \<open>Nameful WS1S Formulas\<close>

(*<*)
theory WS1S_Nameful
imports WS1S_Formula
begin
(*>*)

declare [[coercion "of_char :: char \<Rightarrow> nat", coercion_enabled]]

definition is_upper :: "char \<Rightarrow> bool" where [simp]: "is_upper c = (c \<in> {65..90 :: nat})"
definition is_lower :: "char \<Rightarrow> bool" where [simp]: "is_lower c = (c \<in> {97..122 :: nat})"

(*nonempty string starting with lower case*)
typedef fo = "{s. s \<noteq> [] \<and> is_lower (hd s)}" by (auto intro!: exI[of _ "''x''"])
(*nonempty string starting with upper case*)
typedef so = "{s. s \<noteq> [] \<and> is_upper (hd s)}" by (auto intro!: exI[of _ "''X''"])

datatype ws1s =
    T | F | Or ws1s ws1s | And ws1s ws1s | Not ws1s
  | Ex1 fo ws1s | Ex2 so ws1s | All1 fo ws1s | All2 so ws1s
  | Lt fo fo
  | In fo so
  | Eq_Const fo nat
  | Eq_Presb so nat
  | Eq_FO fo fo
  | Eq_FO_Offset fo fo nat
  | Eq_SO so so
  | Eq_SO_Inc so so
  | Eq_Max fo so
  | Eq_Min fo so
  | Empty so
  | Singleton so
  | Subset so so
  | Disjoint so so
  | Eq_Union so so so
  | Eq_Inter so so so
  | Eq_Diff so so so

(*standard WS1S semantics, finiteness captured by the type fset*)
primrec satisfies :: "(fo \<Rightarrow> nat) \<Rightarrow> (so \<Rightarrow> nat fset) \<Rightarrow> ws1s \<Rightarrow> bool" where
  "satisfies I1 I2 T = True"
| "satisfies I1 I2 F = False"
| "satisfies I1 I2 (Or \<phi> \<psi>) = (satisfies I1 I2 \<phi> \<or> satisfies I1 I2 \<psi>)"
| "satisfies I1 I2 (And \<phi> \<psi>) = (satisfies I1 I2 \<phi> \<and> satisfies I1 I2 \<psi>)"
| "satisfies I1 I2 (Not \<phi>) = (\<not> satisfies I1 I2 \<phi>)"
| "satisfies I1 I2 (Ex1 x \<phi>) = (\<exists>n. satisfies (I1(x := n)) I2 \<phi>)"
| "satisfies I1 I2 (Ex2 X \<phi>) = (\<exists>N. satisfies I1 (I2(X := N)) \<phi>)"
| "satisfies I1 I2 (All1 x \<phi>) = (\<forall>n. satisfies (I1(x := n)) I2 \<phi>)"
| "satisfies I1 I2 (All2 X \<phi>) = (\<forall>N. satisfies I1 (I2(X := N)) \<phi>)"

| "satisfies I1 I2 (Lt x y) = (I1 x < I1 y)"
| "satisfies I1 I2 (In x X) = (I1 x |\<in>| I2 X)"
| "satisfies I1 I2 (Eq_Const x n) = (I1 x = n)"
| "satisfies I1 I2 (Eq_Presb X n) = ((\<Sum>x \<in> fset (I2 X). 2 ^ x) = n)"
| "satisfies I1 I2 (Eq_FO x y) = (I1 x = I1 y)"
| "satisfies I1 I2 (Eq_FO_Offset x y n) = (I1 x = I1 y + n)"
| "satisfies I1 I2 (Eq_SO X Y) = (I2 X = I2 Y)"
| "satisfies I1 I2 (Eq_SO_Inc X Y) = (I2 X = Suc |`| I2 Y)"
| "satisfies I1 I2 (Eq_Max x X) = (let Z = I2 X in Z \<noteq> {||} \<and> I1 x = fMax Z)"
| "satisfies I1 I2 (Eq_Min x X) = (let Z = I2 X in Z \<noteq> {||} \<and> I1 x = fMin Z)"
| "satisfies I1 I2 (Empty X) = (I2 X = {||})"
| "satisfies I1 I2 (Singleton X) = (\<exists>x. I2 X = {|x|})"
| "satisfies I1 I2 (Subset X Y) = (I2 X |\<subseteq>| I2 Y)"
| "satisfies I1 I2 (Disjoint X Y) = (I2 X |\<inter>| I2 Y = {||})"
| "satisfies I1 I2 (Eq_Union X Y Z) = (I2 X = I2 Y |\<union>| I2 Z)"
| "satisfies I1 I2 (Eq_Inter X Y Z) = (I2 X = I2 Y |\<inter>| I2 Z)"
| "satisfies I1 I2 (Eq_Diff X Y Z) = (I2 X = I2 Y |-| I2 Z)"

primrec fos where
  "fos T = []"
| "fos F = []"
| "fos (Or \<phi> \<psi>) = List.union (fos \<phi>) (fos \<psi>)"
| "fos (And \<phi> \<psi>) = List.union (fos \<phi>) (fos \<psi>)"
| "fos (Not \<phi>) = fos \<phi>"
| "fos (Ex1 x \<phi>) = List.remove1 x (fos \<phi>)"
| "fos (Ex2 X \<phi>) = fos \<phi>"
| "fos (All1 x \<phi>) = List.remove1 x (fos \<phi>)"
| "fos (All2 X \<phi>) = fos \<phi>"
| "fos (Lt x y) = remdups [x, y]"
| "fos (In x X) = [x]"
| "fos (Eq_Const x n) = [x]"
| "fos (Eq_Presb X n) = []"
| "fos (Eq_FO x y) = remdups [x, y]"
| "fos (Eq_FO_Offset x y n) = remdups [x, y]"
| "fos (Eq_SO X Y) = []"
| "fos (Eq_SO_Inc X Y) = []"
| "fos (Eq_Max x X) = [x]"
| "fos (Eq_Min x X) = [x]"
| "fos (Empty X) = []"
| "fos (Singleton X) = []"
| "fos (Subset X Y) = []"
| "fos (Disjoint X Y) = []"
| "fos (Eq_Union X Y Z) = []"
| "fos (Eq_Inter X Y Z) = []"
| "fos (Eq_Diff X Y Z) = []"

primrec sos where
  "sos T = []"
| "sos F = []"
| "sos (Or \<phi> \<psi>) = List.union (sos \<phi>) (sos \<psi>)"
| "sos (And \<phi> \<psi>) = List.union (sos \<phi>) (sos \<psi>)"
| "sos (Not \<phi>) = sos \<phi>"
| "sos (Ex1 x \<phi>) = sos \<phi>"
| "sos (Ex2 X \<phi>) = List.remove1 X (sos \<phi>)"
| "sos (All1 x \<phi>) = sos \<phi>"
| "sos (All2 X \<phi>) = List.remove1 X (sos \<phi>)"
| "sos (Lt x y) = []"
| "sos (In x X) = [X]"
| "sos (Eq_Const x n) = []"
| "sos (Eq_Presb X n) = [X]"
| "sos (Eq_FO x y) = []"
| "sos (Eq_FO_Offset x y n) = []"
| "sos (Eq_SO X Y) = remdups [X, Y]"
| "sos (Eq_SO_Inc X Y) = remdups [X, Y]"
| "sos (Eq_Max x X) = [X]"
| "sos (Eq_Min x X) = [X]"
| "sos (Empty X) = [X]"
| "sos (Singleton X) = [X]"
| "sos (Subset X Y) = remdups [X, Y]"
| "sos (Disjoint X Y) = remdups [X, Y]"
| "sos (Eq_Union X Y Z) = remdups [X, Y, Z]"
| "sos (Eq_Inter X Y Z) = remdups [X, Y, Z]"
| "sos (Eq_Diff X Y Z) = remdups [X, Y, Z]"

lemma distinct_fos[simp]: "distinct (fos \<phi>)" by (induct \<phi>) auto
lemma distinct_sos[simp]: "distinct (sos \<phi>)" by (induct \<phi>) auto

primrec \<epsilon> where
  "\<epsilon> bs1 bs2 T = FBool True"
| "\<epsilon> bs1 bs2 F = FBool False"
| "\<epsilon> bs1 bs2 (Or \<phi> \<psi>) = FOr (\<epsilon> bs1 bs2 \<phi>) (\<epsilon> bs1 bs2 \<psi>)"
| "\<epsilon> bs1 bs2 (And \<phi> \<psi>) = FAnd (\<epsilon> bs1 bs2 \<phi>) (\<epsilon> bs1 bs2 \<psi>)"
| "\<epsilon> bs1 bs2 (Not \<phi>) = FNot (\<epsilon> bs1 bs2 \<phi>)"
| "\<epsilon> bs1 bs2 (Ex1 x \<phi>) = FEx FO (\<epsilon> (x # bs1) bs2 \<phi>)"
| "\<epsilon> bs1 bs2 (Ex2 X \<phi>) = FEx SO (\<epsilon> bs1 (X # bs2) \<phi>)"
| "\<epsilon> bs1 bs2 (All1 x \<phi>) = FAll FO (\<epsilon> (x # bs1) bs2 \<phi>)"
| "\<epsilon> bs1 bs2 (All2 X \<phi>) = FAll SO (\<epsilon> bs1 (X # bs2) \<phi>)"
| "\<epsilon> bs1 bs2 (Lt x y) = FBase (Less None (index bs1 x) (index bs1 y))"
| "\<epsilon> bs1 bs2 (In x X) = FBase (WS1S_Formula.In False (index bs1 x) (index bs2 X))"
| "\<epsilon> bs1 bs2 (Eq_Const x n) = FBase (WS1S_Formula.Eq_Const None (index bs1 x) n)"
| "\<epsilon> bs1 bs2 (Eq_Presb X n) = FBase (WS1S_Formula.Eq_Presb None (index bs2 X) n)"
| "\<epsilon> bs1 bs2 (Eq_FO x y) = FBase (WS1S_Formula.Eq_FO False (index bs1 x) (index bs1 y))"
| "\<epsilon> bs1 bs2 (Eq_FO_Offset x y n) = FBase (WS1S_Formula.Plus_FO None (index bs1 x) (index bs1 y) n)"
| "\<epsilon> bs1 bs2 (Eq_SO X Y) = FBase (WS1S_Formula.Eq_SO (index bs2 X) (index bs2 Y))"
| "\<epsilon> bs1 bs2 (Eq_SO_Inc X Y) = FBase (WS1S_Formula.Suc_SO False False (index bs2 X) (index bs2 Y))"
| "\<epsilon> bs1 bs2 (Eq_Max x X) = FBase (WS1S_Formula.Eq_Max False (index bs1 x) (index bs2 X))"
| "\<epsilon> bs1 bs2 (Eq_Min x X) = FBase (WS1S_Formula.Eq_Min False (index bs1 x) (index bs2 X))"
| "\<epsilon> bs1 bs2 (Empty X) = FBase (WS1S_Formula.Empty (index bs2 X))"
| "\<epsilon> bs1 bs2 (Singleton X) = FBase (WS1S_Formula.Singleton (index bs2 X))"
| "\<epsilon> bs1 bs2 (Subset X Y) = FBase (WS1S_Formula.Subset (index bs2 X) (index bs2 Y))"
| "\<epsilon> bs1 bs2 (Disjoint X Y) = FBase (WS1S_Formula.Disjoint (index bs2 X) (index bs2 Y))"
| "\<epsilon> bs1 bs2 (Eq_Union X Y Z) = FBase (WS1S_Formula.Eq_Union (index bs2 X) (index bs2 Y) (index bs2 Z))"
| "\<epsilon> bs1 bs2 (Eq_Inter X Y Z) = FBase (WS1S_Formula.Eq_Inter (index bs2 X) (index bs2 Y) (index bs2 Z))"
| "\<epsilon> bs1 bs2 (Eq_Diff X Y Z) = FBase (WS1S_Formula.Eq_Diff(index bs2 X) (index bs2 Y) (index bs2 Z))"

lift_definition mk_I ::
  "(fo \<Rightarrow> nat) \<Rightarrow> (so \<Rightarrow> nat fset) \<Rightarrow> fo list \<Rightarrow> so list \<Rightarrow> interp" is
  "\<lambda>I1 I2 fs ss. let I1s = map (\<lambda>x. {|I1 x|}) fs; I2s = map I2 ss in (MSB (I1s @ I2s), I1s, I2s)"
  by (auto simp: Let_def)

definition dec_I1 :: "interp \<Rightarrow> fo list \<Rightarrow> fo \<Rightarrow> nat" where "dec_I1 \<AA> fs x = fMin (index fs x\<^bsup>\<AA>\<^esup>FO)"
definition dec_I2 :: "interp \<Rightarrow> so list \<Rightarrow> so \<Rightarrow> nat fset" where "dec_I2 \<AA> ss X = index ss X\<^bsup>\<AA>\<^esup>SO"

lemma nvars_mk_I[simp]: "#\<^sub>V (mk_I I1 I2 fs ss) = Abs_idx (length fs, length ss)"
  by transfer (auto simp: Let_def)

lemma assigns_mk_I_FO[simp]:
  "m\<^bsup>mk_I I1 I2 bs1 bs2\<^esup>FO = (if m < length bs1 then {|I1 (bs1 ! m)|} else {||})"
  by transfer (auto simp: Let_def)

lemma assigns_mk_I_SO[simp]:
  "m\<^bsup>mk_I I1 I2 bs1 bs2\<^esup>SO = (if m < length bs2 then I2 (bs2 ! m) else {||})"
  by transfer (auto simp: Let_def)

lemma satisfies_cong:
  "\<lbrakk>\<forall>x \<in> set (fos \<phi>). I1 x = J1 x; \<forall>X \<in> set (sos \<phi>). I2 X = J2 X\<rbrakk> \<Longrightarrow>
  satisfies I1 I2 \<phi> \<longleftrightarrow> satisfies J1 J2 \<phi>"
proof (induct \<phi> arbitrary: I1 I2 J1 J2)
  case (Or \<phi> \<psi>) from Or.hyps[of I1 J1 I2 J2] Or.prems show ?case by auto
next
  case (And \<phi> \<psi>) from And.hyps[of I1 J1 I2 J2] And.prems show ?case by auto
next
  case (Ex1 x \<phi>) with Ex1.hyps[of "I1(x := y)" "J1(x := y)" I2 J2 for y, cong] show ?case by auto
next
  case (Ex2 X \<phi>) with Ex2.hyps[of I1 J1 "I2(X := Y)" "J2(X := Y)" for Y, cong] show ?case by auto
next
  case (All1 x \<phi>) with All1.hyps[of "I1(x := y)" "J1(x := y)" I2 J2 for y, cong] show ?case by auto
next
  case (All2 X \<phi>) with All2.hyps[of I1 J1 "I2(X := Y)" "J2(X := Y)" for Y, cong] show ?case by auto
qed simp_all

lemma dec_I_mk_I_satisfies_cong:
  "\<lbrakk>set (fos \<phi>) \<subseteq> set bs1; set (sos \<phi>) \<subseteq> set bs2; \<AA> = mk_I I1 I2 bs1 bs2\<rbrakk> \<Longrightarrow>
  satisfies (dec_I1 \<AA> bs1) (dec_I2 \<AA> bs2) \<phi> \<longleftrightarrow> satisfies I1 I2 \<phi>"
  by (rule satisfies_cong) (auto simp: dec_I1_def dec_I2_def)

definition "ok_I \<AA> fs = (\<forall>x \<in> set fs. index fs x\<^bsup>\<AA>\<^esup>FO \<noteq> {||})"

lemma ok_I_mk_I[simp]: "ok_I (mk_I I1 I2 bs1 bs2) bs1"
  unfolding ok_I_def by transfer (auto simp: Let_def)

lemma in_FV_\<epsilon>D[dest]: "\<lbrakk>v \<in> FV (\<epsilon> bs1 bs2 \<phi>) FO;
  set (fos \<phi>) \<subseteq> set bs1; set (sos \<phi>) \<subseteq> set bs2\<rbrakk> \<Longrightarrow>
  (\<exists>y \<in> set bs1. v = index bs1 y)"
proof (induct \<phi> arbitrary: bs1 bs2 v)
  case (Ex1 x \<phi>) from Ex1.hyps[of "Suc v" "x # bs1" bs2] Ex1.prems show ?case
    by (auto simp: Diff_subset_conv split: if_splits)
next
  case (Ex2 X \<phi>) from Ex2.hyps[of v bs1 "X # bs2"] Ex2.prems show ?case
    by (auto simp: Diff_subset_conv split: if_splits)
next
  case (All1 x \<phi>) from All1.hyps[of "Suc v" "x # bs1" bs2] All1.prems show ?case
    by (auto simp: Diff_subset_conv split: if_splits)
next
  case (All2 X \<phi>) from All2.hyps[of v bs1 "X # bs2"] All2.prems show ?case
    by (auto simp: Diff_subset_conv split: if_splits)
qed (auto split: if_splits)

lemma dec_I1_Extend_FO[simp]:
  "dec_I1 (Extend FO 0 \<AA> P) (x # bs1) = (dec_I1 \<AA> bs1)(x := fMin P)"
  by (auto simp: dec_I1_def)

lemma dec_I1_Extend_SO[simp]: "dec_I1 (Extend SO i \<AA> P) bs1 = dec_I1 \<AA> bs1"
  by (auto simp: dec_I1_def)

lemma dec_I2_Extend_FO[simp]: "dec_I2 (Extend FO i \<AA> P) bs2 = dec_I2 \<AA> bs2"
  by (auto simp: dec_I2_def)

lemma dec_I2_Extend_SO[simp]:
  "dec_I2 (Extend SO 0 \<AA> P) (X # bs2) = (dec_I2 \<AA> bs2)(X := P)"
  by (auto simp: dec_I2_def fun_eq_iff)

lemma sat_\<epsilon>: "\<lbrakk>set (fos \<phi>) \<subseteq> set bs1; set (sos \<phi>) \<subseteq> set bs2; ok_I \<AA> bs1\<rbrakk> \<Longrightarrow>
  WS1S.sat \<AA> (\<epsilon> bs1 bs2 \<phi>) \<longleftrightarrow>
  satisfies (dec_I1 \<AA> bs1) (dec_I2 \<AA> bs2) \<phi>"
proof (induct \<phi> arbitrary: \<AA> bs1 bs2)
  case (Or \<phi> \<psi>) from Or.hyps[of bs1 bs2 \<AA>] Or.prems show ?case
    unfolding WS1S.sat_def
    by (auto simp: restrict_def ok_I_def split: order.splits)
next
  case (And \<phi> \<psi>) from And.hyps[of bs1 bs2 \<AA>] And.prems show ?case
    unfolding WS1S.sat_def
    by (auto simp: restrict_def ok_I_def split: order.splits)
next
  case (Not \<phi>) from Not.hyps[of bs1 bs2 \<AA>] Not.prems show ?case
    unfolding WS1S.sat_def
    by (auto simp: restrict_def ok_I_def split: order.splits)
next
  case (Ex1 x \<phi>)
  { fix P :: "nat fset" assume "P \<noteq> {||}"
    with Ex1.prems have "WS1S.sat (Extend FO 0 \<AA> P) (\<epsilon> (x # bs1) bs2 \<phi>) \<longleftrightarrow>
      satisfies (dec_I1 (Extend FO 0 \<AA> P) (x # bs1)) (dec_I2 (Extend FO 0 \<AA> P) bs2) \<phi>"
      by (intro Ex1.hyps) (auto simp: ok_I_def)
  } note IH = this
  show ?case
  proof
    assume "WS1S.sat \<AA> (\<epsilon> bs1 bs2 (Ex1 x \<phi>))"
    then obtain P where "P \<noteq> {||}" "WS1S.sat (Extend FO 0 \<AA> P) (\<epsilon> (x # bs1) bs2 \<phi>)"
      unfolding WS1S.sat_def by (auto simp: restrict_def split: order.splits)
    then have "satisfies (dec_I1 (Extend FO 0 \<AA> P) (x # bs1)) (dec_I2 (Extend FO 0 \<AA> P) bs2) \<phi>"
      by (auto simp: IH)
    then show "satisfies (dec_I1 \<AA> bs1) (dec_I2 \<AA> bs2) (Ex1 x \<phi>)" by auto
  next
    assume "satisfies (dec_I1 \<AA> bs1) (dec_I2 \<AA> bs2) (Ex1 x \<phi>)"
    then obtain n where "satisfies (dec_I1 (Extend FO 0 \<AA> {|n|}) (x # bs1))
      (dec_I2 (Extend FO 0 \<AA> {|n|}) bs2) \<phi>" by auto
    then have "WS1S.sat (Extend FO 0 \<AA> {|n|}) (\<epsilon> (x # bs1) bs2 \<phi>)"
      by (auto simp: IH)
    then show "WS1S.sat \<AA> (\<epsilon> bs1 bs2 (Ex1 x \<phi>))" unfolding WS1S.sat_def
      by (auto simp: restrict_def split: order.splits)
  qed
next
  case (Ex2 X \<phi>)
  { fix P :: "nat fset"
    from Ex2.prems have "WS1S.sat (Extend SO 0 \<AA> P) (\<epsilon> bs1 (X # bs2) \<phi>) \<longleftrightarrow>
      satisfies (dec_I1 (Extend SO 0 \<AA> P) bs1) (dec_I2 (Extend SO 0 \<AA> P) (X # bs2)) \<phi>"
      by (intro Ex2.hyps) (auto simp: ok_I_def)
  } note IH = this
  show ?case
  proof -
    have "WS1S.sat \<AA> (\<epsilon> bs1 bs2 (Ex2 X \<phi>)) \<longleftrightarrow>
      (\<exists>P. WS1S.sat (Extend SO 0 \<AA> P) (\<epsilon> bs1 (X # bs2) \<phi>))"
      unfolding WS1S.sat_def by (auto simp: restrict_def split: order.splits)
    also have "\<dots> \<longleftrightarrow> (\<exists>P. satisfies (dec_I1 (Extend SO 0 \<AA> P) bs1)
      (dec_I2 (Extend SO 0 \<AA> P) (X # bs2)) \<phi>)" by (auto simp: IH)
    also have "\<dots> \<longleftrightarrow> satisfies (dec_I1 \<AA> bs1) (dec_I2 \<AA> bs2) (Ex2 X \<phi>)" by simp
    finally show ?thesis .
  qed
next
  case (All1 x \<phi>)
  { fix P :: "nat fset" assume "P \<noteq> {||}"
    with All1.prems have "WS1S.sat (Extend FO 0 \<AA> P) (\<epsilon> (x # bs1) bs2 \<phi>) \<longleftrightarrow>
      satisfies (dec_I1 (Extend FO 0 \<AA> P) (x # bs1)) (dec_I2 (Extend FO 0 \<AA> P) bs2) \<phi>"
      by (intro All1.hyps) (auto simp: ok_I_def)
  } note IH = this
  show ?case
  proof
    assume L: "WS1S.sat \<AA> (\<epsilon> bs1 bs2 (All1 x \<phi>))"
    { fix n :: "nat"
      from L have "WS1S.sat (Extend FO 0 \<AA> {|n|}) (\<epsilon> (x # bs1) bs2 \<phi>)"
        unfolding WS1S.sat_def by (auto simp: restrict_def split: order.splits)
      then have "satisfies (dec_I1 (Extend FO 0 \<AA> {|n|}) (x # bs1))
        (dec_I2 (Extend FO 0 \<AA> {|n|}) bs2) \<phi>" by (auto simp: IH)
    }
    then show "satisfies (dec_I1 \<AA> bs1) (dec_I2 \<AA> bs2) (All1 x \<phi>)" by simp
  next
    assume R: "satisfies (dec_I1 \<AA> bs1) (dec_I2 \<AA> bs2) (All1 x \<phi>)"
    { fix P :: "nat fset" assume "P \<noteq> {||}"
      with R have "satisfies (dec_I1 (Extend FO 0 \<AA> P) (x # bs1))
        (dec_I2 (Extend FO 0 \<AA> P) bs2) \<phi>" by auto
      with \<open>P \<noteq> {||}\<close> have "WS1S.sat (Extend FO 0 \<AA> P) (\<epsilon> (x # bs1) bs2 \<phi>)"
        by (auto simp: IH)
    }
    with All1.prems in_FV_\<epsilon>D[of _ "x # bs1" bs2 \<phi>]
      show "WS1S.sat \<AA> (\<epsilon> bs1 bs2 (All1 x \<phi>))" unfolding WS1S.sat_def
      by (auto 0 3 simp: restrict_def ok_I_def split: if_splits order.splits)
  qed
next
  case (All2 X \<phi>)
  { fix P :: "nat fset"
    from All2.prems have "WS1S.sat (Extend SO 0 \<AA> P) (\<epsilon> bs1 (X # bs2) \<phi>) \<longleftrightarrow>
      satisfies (dec_I1 (Extend SO 0 \<AA> P) bs1) (dec_I2 (Extend SO 0 \<AA> P) (X # bs2)) \<phi>"
      by (intro All2.hyps) (auto simp: ok_I_def)
  } note IH = this
  show ?case
  proof -
    have "WS1S.sat \<AA> (\<epsilon> bs1 bs2 (All2 X \<phi>)) \<longleftrightarrow>
      (\<forall>P. WS1S.sat (Extend SO 0 \<AA> P) (\<epsilon> bs1 (X # bs2) \<phi>))"
      unfolding WS1S.sat_def by (auto simp: restrict_def split: order.splits)
    also have "\<dots> \<longleftrightarrow> (\<forall>P. satisfies (dec_I1 (Extend SO 0 \<AA> P) bs1)
      (dec_I2 (Extend SO 0 \<AA> P) (X # bs2)) \<phi>)" by (auto simp: IH)
    also have "\<dots> \<longleftrightarrow> satisfies (dec_I1 \<AA> bs1) (dec_I2 \<AA> bs2) (All2 X \<phi>)" by simp
    finally show ?thesis .
  qed
qed (auto simp: WS1S.sat_def Let_def dec_I1_def dec_I2_def ok_I_def
  restrict_def split: if_splits order.splits)

definition "eqv \<phi> \<psi> =
  (let fs = List.union (fos \<phi>) (fos \<psi>); ss = List.union (sos \<phi>) (sos \<psi>)
  in check_eqv (Abs_idx (length fs, length ss)) (\<epsilon> fs ss \<phi>) (\<epsilon> fs ss \<psi>))"

lemma eqv_sound: "eqv \<phi> \<psi> \<Longrightarrow> satisfies I1 I2 \<phi> \<longleftrightarrow> satisfies I1 I2 \<psi>"
  unfolding eqv_def Let_def
  by (drule check_eqv_sound[rotated, of _ _ _
    "mk_I I1 I2 (List.union (fos \<phi>) (fos \<psi>)) (List.union (sos \<phi>) (sos \<psi>))"])
    (auto simp: sat_\<epsilon> dec_I_mk_I_satisfies_cong)

definition "Thm \<phi> = eqv \<phi> T"

lemma "Thm \<Phi> \<Longrightarrow> satisfies I1 I2 \<Phi>"
  unfolding Thm_def by (drule eqv_sound[of _ _ I1 I2]) simp

setup_lifting type_definition_fo
setup_lifting type_definition_so

instantiation fo :: equal
begin
  lift_definition equal_fo :: "fo \<Rightarrow> fo \<Rightarrow> bool" is "(=)" .
  instance by (standard, transfer) simp
end

instantiation so :: equal
begin
  lift_definition equal_so :: "so \<Rightarrow> so \<Rightarrow> bool" is "(=)" .
  instance by (standard, transfer) simp
end

(*<*)
end
(*>*)
