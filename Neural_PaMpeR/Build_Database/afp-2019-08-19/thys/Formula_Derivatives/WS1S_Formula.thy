section \<open>Concrete Atomic WS1S Formulas (Minimum Semantics for FO Variables)\<close>

(*<*)
theory WS1S_Formula
imports
  Abstract_Formula
  WS1S_Prelim
begin
(*>*)

datatype (FOV0: 'fo, SOV0: 'so) atomic =
  Fo 'fo |
  Eq_Const "nat option" 'fo nat |
  Less "bool option" 'fo 'fo |
  Plus_FO "nat option" 'fo 'fo nat |
  Eq_FO bool 'fo 'fo |
  Eq_SO 'so 'so |
  Suc_SO bool bool 'so 'so |
  Empty 'so |
  Singleton 'so |
  Subset 'so 'so |
  In bool 'fo 'so |
  Eq_Max bool 'fo 'so |
  Eq_Min bool 'fo 'so |
  Eq_Union 'so 'so 'so |
  Eq_Inter 'so 'so 'so |
  Eq_Diff 'so 'so 'so |
  Disjoint 'so 'so |
  Eq_Presb "nat option" 'so nat

derive linorder option
derive linorder atomic \<comment> \<open>very slow\<close>

type_synonym fo = nat
type_synonym so = nat
type_synonym ws1s = "(fo, so) atomic"
type_synonym formula = "(ws1s, order) aformula"

primrec wf0 where
  "wf0 idx (Fo m) = LESS FO m idx"
| "wf0 idx (Eq_Const i m n) = (LESS FO m idx \<and> (case i of Some i \<Rightarrow> i \<le> n | _ \<Rightarrow> True))"
| "wf0 idx (Less _ m1 m2) = (LESS FO m1 idx \<and> LESS FO m2 idx)"
| "wf0 idx (Plus_FO i m1 m2 n) =
  (LESS FO m1 idx \<and> LESS FO m2 idx \<and> (case i of Some i \<Rightarrow> i \<le> n | _ \<Rightarrow> True))"
| "wf0 idx (Eq_FO _ m1 m2) = (LESS FO m1 idx \<and> LESS FO m2 idx)"
| "wf0 idx (Eq_SO M1 M2) = (LESS SO M1 idx \<and> LESS SO M2 idx)"
| "wf0 idx (Suc_SO br bl M1 M2) = (LESS SO M1 idx \<and> LESS SO M2 idx)"
| "wf0 idx (Empty M) = LESS SO M idx"
| "wf0 idx (Singleton M) = LESS SO M idx"
| "wf0 idx (Subset M1 M2) = (LESS SO M1 idx \<and> LESS SO M2 idx)"
| "wf0 idx (In _ m M) = (LESS FO m idx \<and> LESS SO M idx)"
| "wf0 idx (Eq_Max _ m M) = (LESS FO m idx \<and> LESS SO M idx)"
| "wf0 idx (Eq_Min _ m M) = (LESS FO m idx \<and> LESS SO M idx)"
| "wf0 idx (Eq_Union M1 M2 M3) = (LESS SO M1 idx \<and> LESS SO M2 idx \<and> LESS SO M3 idx)"
| "wf0 idx (Eq_Inter M1 M2 M3) = (LESS SO M1 idx \<and> LESS SO M2 idx \<and> LESS SO M3 idx)"
| "wf0 idx (Eq_Diff M1 M2 M3) = (LESS SO M1 idx \<and> LESS SO M2 idx \<and> LESS SO M3 idx)"
| "wf0 idx (Disjoint M1 M2) = (LESS SO M1 idx \<and> LESS SO M2 idx)"
| "wf0 idx (Eq_Presb _ M n) = LESS SO M idx"

inductive lformula0 where
  "lformula0 (Fo m)"
| "lformula0 (Eq_Const None m n)"
| "lformula0 (Less None m1 m2)"
| "lformula0 (Plus_FO None m1 m2 n)"
| "lformula0 (Eq_FO False m1 m2)"
| "lformula0 (Eq_SO M1 M2)"
| "lformula0 (Suc_SO False bl M1 M2)"
| "lformula0 (Empty M)"
| "lformula0 (Singleton M)"
| "lformula0 (Subset M1 M2)"
| "lformula0 (In False m M)"
| "lformula0 (Eq_Max False m M)"
| "lformula0 (Eq_Min False m M)"
| "lformula0 (Eq_Union M1 M2 M3)"
| "lformula0 (Eq_Inter M1 M2 M3)"
| "lformula0 (Eq_Diff M1 M2 M3)"
| "lformula0 (Disjoint M1 M2)"
| "lformula0 (Eq_Presb None M n)"

code_pred lformula0 .

declare lformula0.intros[simp]

inductive_cases lformula0E[elim]: "lformula0 a"

abbreviation "FV0 \<equiv> case_order FOV0 SOV0"

fun find0 where
  "find0 FO i (Fo m) = (i = m)"
| "find0 FO i (Eq_Const _ m _) = (i = m)"
| "find0 FO i (Less _ m1 m2) = (i = m1 \<or> i = m2)"
| "find0 FO i (Plus_FO _ m1 m2 _) = (i = m1 \<or> i = m2)"
| "find0 FO i (Eq_FO _ m1 m2) = (i = m1 \<or> i = m2)"
| "find0 SO i (Eq_SO M1 M2) = (i = M1 \<or> i = M2)"
| "find0 SO i (Suc_SO _ _ M1 M2) = (i = M1 \<or> i = M2)"
| "find0 SO i (Empty M) = (i = M)"
| "find0 SO i (Singleton M) = (i = M)"
| "find0 SO i (Subset M1 M2) = (i = M1 \<or> i = M2)"
| "find0 FO i (In _ m _) = (i = m)"
| "find0 SO i (In _ _ M) = (i = M)"
| "find0 FO i (Eq_Max _ m _) = (i = m)"
| "find0 SO i (Eq_Max _ _ M) = (i = M)"
| "find0 FO i (Eq_Min _ m _) = (i = m)"
| "find0 SO i (Eq_Min _ _ M) = (i = M)"
| "find0 SO i (Eq_Union M1 M2 M3) = (i = M1 \<or> i = M2 \<or> i = M3)"
| "find0 SO i (Eq_Inter M1 M2 M3) = (i = M1 \<or> i = M2 \<or> i = M3)"
| "find0 SO i (Eq_Diff M1 M2 M3) = (i = M1 \<or> i = M2 \<or> i = M3)"
| "find0 SO i (Disjoint M1 M2) = (i = M1 \<or> i = M2)"
| "find0 SO i (Eq_Presb _ M _) = (i = M)"
| "find0 _ _ _ = False"

abbreviation "decr0 ord k \<equiv> map_atomic (case_order (dec k) id ord) (case_order id (dec k) ord)"

lemma sum_pow2_image_Suc:
  "finite X \<Longrightarrow> sum ((^) (2 :: nat)) (Suc ` X) = 2 * sum ((^) 2) X"
  by (induct X rule: finite_induct) (auto intro: trans[OF sum.insert])

lemma sum_pow2_insert0:
  "\<lbrakk>finite X; 0 \<notin> X\<rbrakk> \<Longrightarrow> sum ((^) (2 :: nat)) (insert 0 X) = Suc (sum ((^) 2) X)"
  by (induct X rule: finite_induct) (auto intro: trans[OF sum.insert])

lemma sum_pow2_upto: "sum ((^) (2 :: nat)) {0 ..< x} = 2 ^ x - 1"
  by (induct x) (auto simp: algebra_simps)

lemma sum_pow2_inj:
  "\<lbrakk>finite X; finite Y; (\<Sum>x\<in>X. 2 ^ x :: nat) = (\<Sum>x\<in>Y. 2 ^ x)\<rbrakk> \<Longrightarrow> X = Y"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?f X = ?f Y \<Longrightarrow> _")
proof (induct X arbitrary: Y rule: finite_linorder_max_induct)
  case (insert x X)
  from insert(2) have "?f X \<le> ?f {0 ..< x}" by (intro sum_mono2) auto
  also have "\<dots> < 2 ^ x" by (induct x) simp_all
  finally have "?f X < 2 ^ x" .
  moreover from insert(1,2) have *: "?f X + 2 ^ x = ?f Y"
    using trans[OF sym[OF insert(5)] sum.insert] by auto
  ultimately have "?f Y < 2 ^ Suc x" by simp

  have "\<forall>y \<in> Y. y \<le> x"
  proof (rule ccontr)
    assume "\<not> (\<forall>y\<in>Y. y \<le> x)"
    then obtain y where "y \<in> Y" "Suc x \<le> y" by auto
    from this(2) have "2 ^ Suc x \<le> (2 ^ y :: nat)" by (intro power_increasing) auto
    also from \<open>y \<in> Y\<close> insert(4) have "\<dots> \<le> ?f Y" by (metis order.refl sum.remove trans_le_add1)
    finally show False using \<open>?f Y < 2 ^ Suc x\<close> by simp
  qed

  { assume "x \<notin> Y"
    with \<open>\<forall>y \<in> Y. y \<le> x\<close> have "?f Y \<le> ?f {0 ..< x}" by (intro sum_mono2) (auto simp: le_less)
    also have "\<dots> < 2 ^ x" by (induct x) simp_all
    finally have "?f Y < 2 ^ x" .
    with * have False by auto
  }
  then have "x \<in> Y" by blast

  from insert(4) have "?f (Y - {x}) + 2 ^ x = ?f (insert x (Y - {x}))"by (subst sum.insert) auto
  also have "\<dots> = ?f X + 2 ^ x" unfolding * using \<open>x \<in> Y\<close> by (simp add: insert_absorb)
  finally have "?f X = ?f (Y - {x})" by simp
  with insert(3,4) have "X = Y - {x}" by simp
  with \<open>x \<in> Y\<close> show ?case by auto
qed simp

lemma finite_pow2_eq:
  fixes n :: nat
  shows "finite {i. 2 ^ i = n}"
proof -
  have "((^) 2) ` {i. 2 ^ i = n} \<subseteq> {n}" by auto
  then have "finite (((^) (2 :: nat)) ` {i. 2 ^ i = n})" by (rule finite_subset) blast
  then show "finite {i. 2 ^ i = n}" by (rule finite_imageD) (auto simp: inj_on_def)
qed

lemma finite_pow2_le[simp]:
  fixes n :: nat
  shows "finite {i. 2 ^ i \<le> n}"
  by (induct n) (auto simp: le_Suc_eq finite_pow2_eq)

lemma le_pow2[simp]: "x \<le> y \<Longrightarrow> x \<le> 2 ^ y"
  by (induct x arbitrary: y) (force simp add: Suc_le_eq order.strict_iff_order)+

lemma ld_bounded: "Max {i. 2 ^ i \<le> Suc n} \<le> Suc n" (is "?m \<le> Suc n")
proof -
  have "?m \<le> 2 ^ ?m" by (rule le_pow2) simp
  moreover
  have "?m \<in> {i. 2 ^ i \<le> Suc n}" by (rule Max_in) (auto intro: exI[of _ 0])
  then have "2 ^ ?m \<le> Suc n" by simp
  ultimately show ?thesis by linarith
qed

primrec satisfies0 where
  "satisfies0 \<AA> (Fo m) = (m\<^bsup>\<AA>\<^esup>FO \<noteq> {||})"
| "satisfies0 \<AA> (Eq_Const i m n) =
   (let P = m\<^bsup>\<AA>\<^esup>FO in if P = {||}
   then (case i of Some i \<Rightarrow> Length \<AA> = i | _ \<Rightarrow> False)
   else fMin P = n)"
| "satisfies0 \<AA> (Less b m1 m2) =
   (let P1 = m1\<^bsup>\<AA>\<^esup>FO; P2 = m2\<^bsup>\<AA>\<^esup>FO in if P1 = {||} \<or> P2 = {||}
   then (case b of None \<Rightarrow> False | Some True \<Rightarrow> P2 = {||} | Some False \<Rightarrow> P1 \<noteq> {||})
   else fMin P1 < fMin P2)"
| "satisfies0 \<AA> (Plus_FO i m1 m2 n) =
   (let P1 = m1\<^bsup>\<AA>\<^esup>FO; P2 = m2\<^bsup>\<AA>\<^esup>FO in if P1 = {||} \<or> P2 = {||}
   then (case i of Some 0 \<Rightarrow> P1 = P2 | Some i \<Rightarrow> P2 \<noteq> {||} \<and> fMin P2 + i = Length \<AA> | _ \<Rightarrow> False)
   else fMin P1 = fMin P2 + n)"
| "satisfies0 \<AA> (Eq_FO b m1 m2) =
   (let P1 = m1\<^bsup>\<AA>\<^esup>FO; P2 = m2\<^bsup>\<AA>\<^esup>FO in if P1 = {||} \<or> P2 = {||}
   then b \<and> P1 = P2
   else fMin P1 = fMin P2)"
| "satisfies0 \<AA> (Eq_SO M1 M2) = (M1\<^bsup>\<AA>\<^esup>SO = M2\<^bsup>\<AA>\<^esup>SO)"
| "satisfies0 \<AA> (Suc_SO br bl M1 M2) =
   ((if br then finsert (Length \<AA>) else id) (M1\<^bsup>\<AA>\<^esup>SO) =
    (if bl then finsert 0 else id) (Suc |`| M2\<^bsup>\<AA>\<^esup>SO))"
| "satisfies0 \<AA> (Empty M) = (M\<^bsup>\<AA>\<^esup>SO = {||})"
| "satisfies0 \<AA> (Singleton M) = (\<exists>x. M\<^bsup>\<AA>\<^esup>SO = {|x|})"
| "satisfies0 \<AA> (Subset M1 M2) = (M1\<^bsup>\<AA>\<^esup>SO |\<subseteq>| M2\<^bsup>\<AA>\<^esup>SO)"
| "satisfies0 \<AA> (In b m M) =
   (let P = m\<^bsup>\<AA>\<^esup>FO in if P = {||} then b else fMin P |\<in>| M\<^bsup>\<AA>\<^esup>SO)"
| "satisfies0 \<AA> (Eq_Max b m M) =
   (let P1 = m\<^bsup>\<AA>\<^esup>FO; P2 = M\<^bsup>\<AA>\<^esup>SO in if b then P1 = {||}
   else if P1 = {||} \<or> P2 = {||} then False else fMin P1 = fMax P2)"
| "satisfies0 \<AA> (Eq_Min b m M) =
   (let P1 = m\<^bsup>\<AA>\<^esup>FO; P2 = M\<^bsup>\<AA>\<^esup>SO in if P1 = {||} \<or> P2 = {||} then b \<and> P1 = P2 else fMin P1 = fMin P2)"
| "satisfies0 \<AA> (Eq_Union M1 M2 M3) = (M1\<^bsup>\<AA>\<^esup>SO = M2\<^bsup>\<AA>\<^esup>SO |\<union>| M3\<^bsup>\<AA>\<^esup>SO)"
| "satisfies0 \<AA> (Eq_Inter M1 M2 M3) = (M1\<^bsup>\<AA>\<^esup>SO = M2\<^bsup>\<AA>\<^esup>SO |\<inter>| M3\<^bsup>\<AA>\<^esup>SO)"
| "satisfies0 \<AA> (Eq_Diff M1 M2 M3) = (M1\<^bsup>\<AA>\<^esup>SO = M2\<^bsup>\<AA>\<^esup>SO |-| M3\<^bsup>\<AA>\<^esup>SO)"
| "satisfies0 \<AA> (Disjoint M1 M2) = (M1\<^bsup>\<AA>\<^esup>SO |\<inter>| M2\<^bsup>\<AA>\<^esup>SO = {||})"
| "satisfies0 \<AA> (Eq_Presb i M n) = (((\<Sum>x\<in>fset (M\<^bsup>\<AA>\<^esup>SO). 2 ^ x) = n) \<and>
   (case i of None \<Rightarrow> True | Some l \<Rightarrow> Length \<AA> = l))"

fun lderiv0 where
  "lderiv0 (bs1, bs2) (Fo m) = (if bs1 ! m then FBool True else FBase (Fo m))"
| "lderiv0 (bs1, bs2) (Eq_Const None m n) = (if n = 0 \<and> bs1 ! m then FBool True
     else if n = 0 \<or> bs1 ! m then FBool False else FBase (Eq_Const None m (n - 1)))"
| "lderiv0 (bs1, bs2) (Less None m1 m2) = (case (bs1 ! m1, bs1 ! m2) of
    (False, False) \<Rightarrow> FBase (Less None m1 m2)
  | (True, False) \<Rightarrow> FBase (Fo m2)
  | _ \<Rightarrow> FBool False)"|
 "lderiv0 (bs1, bs2) (Eq_FO False m1 m2) = (case (bs1 ! m1, bs1 ! m2) of
    (False, False) \<Rightarrow> FBase (Eq_FO False m1 m2)
  | (True, True) \<Rightarrow> FBool True
  | _ \<Rightarrow> FBool False)"
| "lderiv0 (bs1, bs2) (Plus_FO None m1 m2 n) = (if n = 0
  then
    (case (bs1 ! m1, bs1 ! m2) of
      (False, False) \<Rightarrow> FBase (Plus_FO None m1 m2 n)
    | (True, True) \<Rightarrow> FBool True
    | _ \<Rightarrow> FBool False)
  else 
    (case (bs1 ! m1, bs1 ! m2) of
      (False, False) \<Rightarrow> FBase (Plus_FO None m1 m2 n)
    | (False, True) \<Rightarrow> FBase (Eq_Const None m1 (n - 1))
    | _ \<Rightarrow> FBool False))"
| "lderiv0 (bs1, bs2) (Eq_SO M1 M2) =
  (if bs2 ! M1 = bs2 ! M2 then FBase (Eq_SO M1 M2) else FBool False)"
| "lderiv0 (bs1, bs2) (Suc_SO False bl M1 M2) = (if bl = bs2 ! M1
    then FBase (Suc_SO False (bs2 ! M2) M1 M2) else FBool False)"
| "lderiv0 (bs1, bs2) (Empty M) = (case bs2 ! M of
    True \<Rightarrow> FBool False
  | False \<Rightarrow> FBase (Empty M))"
| "lderiv0 (bs1, bs2) (Singleton M) = (case bs2 ! M of
    True \<Rightarrow> FBase (Empty M)
  | False \<Rightarrow> FBase (Singleton M))"
| "lderiv0 (bs1, bs2) (Subset M1 M2) = (case (bs2 ! M1, bs2 ! M2) of
    (True, False) \<Rightarrow> FBool False
  | _ \<Rightarrow> FBase (Subset M1 M2))"
| "lderiv0 (bs1, bs2) (In False m M) = (case (bs1 ! m, bs2 ! M) of
    (False, _) \<Rightarrow> FBase (In False m M)
  | (True, True) \<Rightarrow> FBool True
  | _ \<Rightarrow> FBool False)"
| "lderiv0 (bs1, bs2) (Eq_Max False m M) = (case (bs1 ! m, bs2 ! M) of
    (False, _) \<Rightarrow> FBase (Eq_Max False m M)
  | (True, True) \<Rightarrow> FBase (Empty M)
  | _ \<Rightarrow> FBool False)"
| "lderiv0 (bs1, bs2) (Eq_Min False m M) = (case (bs1 ! m, bs2 ! M) of
    (False, False) \<Rightarrow> FBase (Eq_Min False m M)
  | (True, True) \<Rightarrow> FBool True
  | _ \<Rightarrow> FBool False)"
| "lderiv0 (bs1, bs2) (Eq_Union M1 M2 M3) = (if bs2 ! M1 = (bs2 ! M2 \<or> bs2 ! M3)
   then FBase (Eq_Union M1 M2 M3) else FBool False)"
| "lderiv0 (bs1, bs2) (Eq_Inter M1 M2 M3) = (if bs2 ! M1 = (bs2 ! M2 \<and> bs2 ! M3)
   then FBase (Eq_Inter M1 M2 M3) else FBool False)"
| "lderiv0 (bs1, bs2) (Eq_Diff M1 M2 M3) = (if bs2 ! M1 = (bs2 ! M2 \<and> \<not> bs2 ! M3)
   then FBase (Eq_Diff M1 M2 M3) else FBool False)"
| "lderiv0 (bs1, bs2) (Disjoint M1 M2) =
  (if bs2 ! M1 \<and> bs2 ! M2 then FBool False else FBase (Disjoint M1 M2))"
| "lderiv0 (bs1, bs2) (Eq_Presb None M n) = (if bs2 ! M = (n mod 2 = 0)
   then FBool False else FBase (Eq_Presb None M (n div 2)))"
| "lderiv0 _ _ = undefined"

fun ld where
  "ld 0 = 0"
| "ld (Suc 0) = 0"
| "ld n = Suc (ld (n div 2))"

lemma ld_alt[simp]: "n > 0 \<Longrightarrow> ld n = Max {i. 2 ^ i \<le> n}"
proof (safe intro!: Max_eqI[symmetric])
  assume "n > 0" then show "2 ^ ld n \<le> n" by (induct n rule: ld.induct) auto
next
  fix y
  assume "2 ^ y \<le> n"
  then show "y \<le> ld n"
  proof (induct n arbitrary: y rule: ld.induct)
    case (3 z)
    then have "y - 1 \<le> ld (Suc (Suc z) div 2)"
      by (cases y) simp_all
    then show ?case by simp
  qed (auto simp: le_eq_less_or_eq)
qed simp

fun rderiv0 where
  "rderiv0 (bs1, bs2) (Fo m) = (if bs1 ! m then FBool True else FBase (Fo m))"
| "rderiv0 (bs1, bs2) (Eq_Const i m n) = (case bs1 ! m of
    False \<Rightarrow> FBase (Eq_Const (case i of Some (Suc i) \<Rightarrow> Some i | _ \<Rightarrow> None) m n)
  | True \<Rightarrow> FBase (Eq_Const (Some n) m n))"
| "rderiv0 (bs1, bs2) (Less b m1 m2) = (case bs1 ! m2 of
    False \<Rightarrow> (case b of
      Some False \<Rightarrow> (case bs1 ! m1 of
        True \<Rightarrow> FBase (Less (Some True) m1 m2)
      | False \<Rightarrow> FBase (Less (Some False) m1 m2))
    | _ \<Rightarrow> FBase (Less b m1 m2))
  | True \<Rightarrow> FBase (Less (Some False) m1 m2))"
| "rderiv0 (bs1, bs2) (Plus_FO i m1 m2 n) = (if n = 0
  then
    (case (bs1 ! m1, bs1 ! m2) of
      (False, False) \<Rightarrow> FBase (Plus_FO i m1 m2 n)
    | (True, True) \<Rightarrow> FBase (Plus_FO (Some 0) m1 m2 n)
    | _ \<Rightarrow> FBase (Plus_FO None m1 m2 n))
  else
    (case bs1 ! m1 of
      True \<Rightarrow> FBase (Plus_FO (Some n) m1 m2 n)
    | False \<Rightarrow> (case bs1 ! m2 of
        False \<Rightarrow> (case i of
          Some (Suc (Suc i)) \<Rightarrow> FBase (Plus_FO (Some (Suc i)) m1 m2 n)
        | Some (Suc 0) \<Rightarrow> FBase (Plus_FO None m1 m2 n)
        | _ \<Rightarrow> FBase (Plus_FO i m1 m2 n))
      | True \<Rightarrow> (case i of
          Some (Suc i) \<Rightarrow> FBase (Plus_FO (Some i) m1 m2 n)
        | _ \<Rightarrow> FBase (Plus_FO None m1 m2 n)))))"
| "rderiv0 (bs1, bs2) (Eq_FO b m1 m2) = (case (bs1 ! m1, bs1 ! m2) of
    (False, False) \<Rightarrow> FBase (Eq_FO b m1 m2)
  | (True, True) \<Rightarrow> FBase (Eq_FO True m1 m2)
  | _ \<Rightarrow> FBase (Eq_FO False m1 m2))"
| "rderiv0 (bs1, bs2) (Eq_SO M1 M2) =
  (if bs2 ! M1 = bs2 ! M2 then FBase (Eq_SO M1 M2) else FBool False)"
| "rderiv0 (bs1, bs2) (Suc_SO br bl M1 M2) = (if br = bs2 ! M2
    then FBase (Suc_SO  (bs2 ! M1) bl M1 M2) else FBool False)"
| "rderiv0 (bs1, bs2) (Empty M) = (case bs2 ! M of
    True \<Rightarrow> FBool False
  | False \<Rightarrow> FBase (Empty M))"
| "rderiv0 (bs1, bs2) (Singleton M) = (case bs2 ! M of
    True \<Rightarrow> FBase (Empty M)
  | False \<Rightarrow> FBase (Singleton M))"
| "rderiv0 (bs1, bs2) (Subset M1 M2) = (case (bs2 ! M1, bs2 ! M2) of
    (True, False) \<Rightarrow> FBool False
  | _ \<Rightarrow> FBase (Subset M1 M2))"
| "rderiv0 (bs1, bs2) (In b m M) = (case (bs1 ! m, bs2 ! M) of
    (True, True) \<Rightarrow> FBase (In True m M)
  | (True, False) \<Rightarrow> FBase (In False m M)
  | _ \<Rightarrow> FBase (In b m M))"
| "rderiv0 (bs1, bs2) (Eq_Max b m M) =  (case (bs1 ! m, bs2 ! M) of
    (True, True) \<Rightarrow> if b then FBool False else FBase (Eq_Max True m M)
  | (True, False) \<Rightarrow> if b then FBool False else FBase (Eq_Max False m M)
  | (False, True) \<Rightarrow> if b then FBase (Eq_Max True m M) else FBool False
  | (False, False) \<Rightarrow> FBase (Eq_Max b m M))"
| "rderiv0 (bs1, bs2) (Eq_Min b m M) =  (case (bs1 ! m, bs2 ! M) of
    (True, True) \<Rightarrow> FBase (Eq_Min True m M)
  | (False, False) \<Rightarrow> FBase (Eq_Min b m M)
  | _ \<Rightarrow> FBase (Eq_Min False m M))"
| "rderiv0 (bs1, bs2) (Eq_Union M1 M2 M3) = (if bs2 ! M1 = (bs2 ! M2 \<or> bs2 ! M3)
   then FBase (Eq_Union M1 M2 M3) else FBool False)"
| "rderiv0 (bs1, bs2) (Eq_Inter M1 M2 M3) = (if bs2 ! M1 = (bs2 ! M2 \<and> bs2 ! M3)
   then FBase (Eq_Inter M1 M2 M3) else FBool False)"
| "rderiv0 (bs1, bs2) (Eq_Diff M1 M2 M3) = (if bs2 ! M1 = (bs2 ! M2 \<and> \<not> bs2 ! M3)
   then FBase (Eq_Diff M1 M2 M3) else FBool False)"
| "rderiv0 (bs1, bs2) (Disjoint M1 M2) =
  (if bs2 ! M1 \<and> bs2 ! M2 then FBool False else FBase (Disjoint M1 M2))"
| "rderiv0 (bs1, bs2) (Eq_Presb l M n) = (case l of
     None \<Rightarrow> if bs2 ! M then
         if n = 0 then FBool False
         else let l = ld n in FBase (Eq_Presb (Some l) M (n - 2 ^ l))
       else FBase (Eq_Presb l M n)
  | Some 0 \<Rightarrow> FBool False
  | Some (Suc l) \<Rightarrow> if bs2 ! M \<and> n \<ge> 2 ^ l then FBase (Eq_Presb (Some l) M (n - 2 ^ l))
      else if \<not> bs2 ! M \<and> n < 2 ^ l then FBase (Eq_Presb (Some l) M n)
      else FBool False)"

primrec nullable0 where
  "nullable0 (Fo m) = False"
| "nullable0 (Eq_Const i m n) = (i = Some 0)"
| "nullable0 (Less b m1 m2) = (case b of None \<Rightarrow> False | Some b \<Rightarrow> b)"
| "nullable0 (Plus_FO i m1 m2 n) = (i = Some 0)"
| "nullable0 (Eq_FO b m1 m2) = b"
| "nullable0 (Eq_SO M1 M2) = True"
| "nullable0 (Suc_SO br bl M1 M2) = (bl = br)"
| "nullable0 (Empty M) = True"
| "nullable0 (Singleton M) = False"
| "nullable0 (Subset M1 M2) = True"
| "nullable0 (In b m M) = b"
| "nullable0 (Eq_Max b m M) = b"
| "nullable0 (Eq_Min b m M) = b"
| "nullable0 (Eq_Union M1 M2 M3) = True"
| "nullable0 (Eq_Inter M1 M2 M3) = True"
| "nullable0 (Eq_Diff M1 M2 M3) = True"
| "nullable0 (Disjoint M1 M2) = True"
| "nullable0 (Eq_Presb l M n) = (n = 0 \<and> (l = Some 0 \<or> l = None))"

definition "restrict ord P = (case ord of FO \<Rightarrow> P \<noteq> {||} | SO \<Rightarrow> True)"
definition "Restrict ord i = (case ord of FO \<Rightarrow> FBase (Fo i) | SO \<Rightarrow> FBool True)"

declare [[goals_limit = 50]]


global_interpretation WS1S: Formula SUC LESS assigns nvars Extend CONS SNOC Length
  extend size_atom zero \<sigma> eval downshift upshift finsert cut len restrict Restrict
  lformula0 FV0 find0 wf0 decr0 satisfies0 nullable0 lderiv0 rderiv0 undefined
  defines norm = "Formula_Operations.norm find0 decr0"
  and nFOr = "Formula_Operations.nFOr :: formula \<Rightarrow> _"
  and nFAnd = "Formula_Operations.nFAnd :: formula \<Rightarrow> _"
  and nFNot = "Formula_Operations.nFNot find0 decr0 :: formula \<Rightarrow> _"
  and nFEx = "Formula_Operations.nFEx find0 decr0"
  and nFAll = "Formula_Operations.nFAll find0 decr0"
  and decr = "Formula_Operations.decr decr0 :: _ \<Rightarrow> _ \<Rightarrow> formula \<Rightarrow> _"
  and find = "Formula_Operations.find find0 :: _ \<Rightarrow> _ \<Rightarrow> formula \<Rightarrow> _"
  and FV = "Formula_Operations.FV FV0"
  and RESTR = "Formula_Operations.RESTR Restrict :: _ \<Rightarrow> formula"
  and RESTRICT = "Formula_Operations.RESTRICT Restrict FV0"
  and deriv = "\<lambda>d0 (a :: atom) (\<phi> :: formula). Formula_Operations.deriv extend d0 a \<phi>"
  and nullable = "\<lambda>\<phi> :: formula. Formula_Operations.nullable nullable0 \<phi>"
  and fut_default = "Formula.fut_default extend zero rderiv0"
  and fut = "Formula.fut extend zero find0 decr0 rderiv0"
  and finalize = "Formula.finalize SUC extend zero find0 decr0 rderiv0"
  and final = "Formula.final SUC extend zero find0 decr0
     nullable0 rderiv0 :: idx \<Rightarrow> formula \<Rightarrow> _"
  and ws1s_wf = "Formula_Operations.wf SUC (wf0 :: idx \<Rightarrow> ws1s \<Rightarrow> _)"
  and ws1s_lformula = "Formula_Operations.lformula lformula0 :: formula \<Rightarrow> _"
  and check_eqv = "\<lambda>idx. DAs.check_eqv
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    (final idx) (\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_lformula \<phi>)
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    (final idx) (\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_lformula \<phi>) (=)"
  and bounded_check_eqv = "\<lambda>idx. DAs.check_eqv
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    nullable (\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_lformula \<phi>)
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: (ws1s, order) aformula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    nullable (\<lambda>\<phi> :: formula. ws1s_wf idx \<phi> \<and> ws1s_lformula \<phi>) (=)"
  and automaton = "DA.automaton
    (\<lambda>a \<phi>. norm (deriv lderiv0 (a :: atom) \<phi> :: formula))"
proof
  fix k idx and a :: ws1s and l assume "wf0 (SUC k idx) a" "LESS k l (SUC k idx)" "\<not> find0 k l a"
  then show "wf0 idx (decr0 k l a)"
    by (induct a) (unfold wf0.simps atomic.map find0.simps,
     (transfer, force simp: dec_def split!: if_splits order.splits)+)
next
  fix k and a :: ws1s and l assume "lformula0 a"
  then show "lformula0 (decr0 k l a)" by (induct a) auto
next
  fix i k and a :: ws1s and \<AA> :: interp and P assume *: "\<not> find0 k i a" "LESS k i (SUC k (#\<^sub>V \<AA>))"
    and disj: "lformula0 a \<or> len P \<le> Length \<AA>"
  from disj show "satisfies0 (Extend k i \<AA> P) a = satisfies0 \<AA> (decr0 k i a)"
  proof
    assume "lformula0 a"
    then show ?thesis using *
      by (induct a rule: lformula0.induct)
        (auto simp: dec_def split: if_splits order.split option.splits bool.splits) \<comment> \<open>slow\<close>
  next
    note dec_def[simp]
    assume "len P \<le> Length \<AA>"
    with * show ?thesis
    proof (induct a)
      case Fo then show ?case by (cases k) auto
    next
      case Eq_Const then show ?case
        by (cases k) (auto simp: Let_def len_def split: if_splits option.splits)
    next
      case Less then show ?case by (cases k) auto
    next
      case Plus_FO then show ?case
        by (cases k) (auto simp: max_def len_def Let_def split: option.splits nat.splits)
    next
      case Eq_FO then show ?case by (cases k) auto
    next
      case Eq_SO then show ?case by (cases k) auto
    next
      case (Suc_SO br bl M1 M2) then show ?case
        by (cases k) (auto simp: max_def len_def)
    next
      case Empty then show ?case by (cases k) auto
    next
      case Singleton then show ?case by (cases k) auto
    next
      case Subset then show ?case by (cases k) auto
    next
      case In then show ?case by (cases k) auto
    qed (auto simp: len_def max_def split!: option.splits order.splits)
  qed
next
  fix idx and a :: ws1s and x assume "lformula0 a" "wf0 idx a"
  then show "Formula_Operations.wf SUC wf0 idx (lderiv0 x a)"
    by (induct a rule: lderiv0.induct)
      (auto simp: Formula_Operations.wf.simps Let_def split: bool.splits order.splits)
next
  fix a :: ws1s and x assume "lformula0 a"
  then show "Formula_Operations.lformula lformula0 (lderiv0 x a)"
    by (induct a rule: lderiv0.induct)
      (auto simp: Formula_Operations.lformula.simps split: bool.splits)
next
  fix idx and a :: ws1s and x assume "wf0 idx a"
  then show "Formula_Operations.wf SUC wf0 idx (rderiv0 x a)"
    by (induct a rule: lderiv0.induct)
      (auto simp: Formula_Operations.wf.simps Let_def sorted_append
        split: bool.splits order.splits nat.splits)
next
  fix \<AA> :: interp and a :: ws1s
  note fmember.rep_eq[symmetric, simp]
  assume "Length \<AA> = 0"
  then show "nullable0 a = satisfies0 \<AA> a"
    by (induct a, unfold wf0.simps nullable0.simps satisfies0.simps Let_def)
      (transfer, (auto 0 3 dest: MSB_greater split: prod.splits if_splits option.splits bool.splits nat.splits) [])+  \<comment> \<open>slow\<close>
next
   note Formula_Operations.satisfies_gen.simps[simp] Let_def[simp] upshift_def[simp]
   fix x :: atom and a :: ws1s and \<AA> :: interp
   assume "lformula0 a" "wf0 (#\<^sub>V \<AA>) a" "#\<^sub>V \<AA> = size_atom x"
   then show "Formula_Operations.satisfies Extend Length satisfies0 \<AA> (lderiv0 x a) =
     satisfies0 (CONS x \<AA>) a"
   proof (induct a)
     case 18
     then show ?case
       apply (auto simp: sum_pow2_image_Suc sum_pow2_insert0 image_iff split: prod.splits)
       apply presburger+
       done
   qed (auto split: prod.splits bool.splits)
next
   note Formula_Operations.satisfies_gen.simps[simp] Let_def[simp] upshift_def[simp]
   fix x :: atom and a :: ws1s and \<AA> :: interp
   assume "lformula0 a" "wf0 (#\<^sub>V \<AA>) a" "#\<^sub>V \<AA> = size_atom x"
   then show "Formula_Operations.satisfies_bounded Extend Length len satisfies0 \<AA> (lderiv0 x a) =
     satisfies0 (CONS x \<AA>) a"
   proof (induct a)
     case 18
     then show ?case
       apply (auto simp: sum_pow2_image_Suc sum_pow2_insert0 image_iff split: prod.splits)
       apply presburger+
       done
   qed (auto split: prod.splits bool.splits)
next
   note Formula_Operations.satisfies_gen.simps[simp] Let_def[simp]
   fix x :: atom and a :: ws1s and \<AA> :: interp
   assume "wf0 (#\<^sub>V \<AA>) a" "#\<^sub>V \<AA> = size_atom x"
   then show "Formula_Operations.satisfies_bounded Extend Length len satisfies0 \<AA> (rderiv0 x a) =
     satisfies0 (SNOC x \<AA>) a"
   proof (induct a)
     case Eq_Const then show ?case by (auto split: prod.splits option.splits nat.splits)
   next
     case Less then show ?case
       by (auto split: prod.splits option.splits bool.splits) (metis fMin_less_Length less_not_sym)+
   next
     case (Plus_FO i m1 m2 n) then show ?case
       by (auto simp: min.commute dest: fMin_less_Length
          split: prod.splits option.splits nat.splits bool.splits)
   next
     case Eq_FO then show ?case
       by (auto split: prod.splits option.splits bool.splits) (metis fMin_less_Length less_not_sym)+
   next
     case Eq_SO then show ?case
       by (auto split: prod.splits option.splits bool.splits)
         (metis assigns_less_Length finsertI1 less_not_refl)+
   next
     case Suc_SO then show ?case
     apply (auto 2 1 split: prod.splits)
                       apply (metis finsert_iff gr0_implies_Suc in_fimage_Suc nat.distinct(2))
                      apply (metis finsert_iff in_fimage_Suc less_not_refl)
                     apply (metis (no_types, hide_lams) fimage_finsert finsertE finsertI1 finsert_commute in_fimage_Suc n_not_Suc_n)
                    apply (metis (no_types, hide_lams) assigns_less_Length order.strict_iff_order finsert_iff in_fimage_Suc not_less_eq_eq order_refl)
                   apply (metis assigns_less_Length fimageI finsert_iff less_irrefl_nat nat.inject)
                  apply (metis finsertE finsertI1 finsert_commute finsert_fminus_single in_fimage_Suc n_not_Suc_n)
                 apply (metis (no_types, hide_lams) assigns_less_Length finsertE fminus_finsert2 fminus_iff in_fimage_Suc lessI not_less_iff_gr_or_eq)
                apply (metis assigns_less_Length finsert_iff lessI not_less_iff_gr_or_eq)
               apply (metis assigns_less_Length fimage_finsert finsert_iff not_less_eq not_less_iff_gr_or_eq)
              apply metis
             apply (metis assigns_less_Length order.strict_iff_order finsert_iff in_fimage_Suc not_less_eq_eq order_refl)
            apply (metis Suc_leI assigns_less_Length fimageI finsert_iff le_eq_less_or_eq lessI less_imp_not_less)
           apply (metis assigns_less_Length fimageE finsertI1 finsert_fminus_if fminus_finsert_absorb lessI less_not_sym)
          apply (metis assigns_less_Length order.strict_iff_order finsert_iff not_less_eq_eq order_refl)
         apply (metis assigns_less_Length order.strict_iff_order finsert_iff not_less_eq_eq order_refl)
        apply (metis assigns_less_Length fimage_Suc_inj fimage_finsert finsert_absorb finsert_iff less_not_refl nat.distinct(2))
       apply (metis assigns_less_Length fimage_Suc_inj fimage_finsert finsertI1 finsert_absorb less_not_refl)
      apply (metis assigns_less_Length fimage_Suc_inj fimage_finsert finsert_absorb finsert_iff less_not_refl nat.distinct(2))
     apply (metis assigns_less_Length fimage_Suc_inj fimage_finsert finsertI1 finsert_absorb2 less_not_refl)
     done
   next
     case In then show ?case by (auto split: prod.splits) (metis fMin_less_Length less_not_sym)+
   next
     case (Eq_Max b m M) then show ?case
       by (auto split: prod.splits bool.splits)
         (metis fMax_less_Length less_not_sym, (metis fMin_less_Length less_not_sym)+)
   next
     case Eq_Min then show ?case
      by (auto split: prod.splits bool.splits) (metis fMin_less_Length less_not_sym)+
   next
     case Eq_Union then show ?case
       by (auto 0 0 simp add: fset_eq_iff split: prod.splits) (metis assigns_less_Length less_not_refl)+
   next
     case Eq_Inter then show ?case
       by (auto 0 0 simp add: fset_eq_iff split: prod.splits) (metis assigns_less_Length less_not_refl)+
   next
     case Eq_Diff then show ?case
       by (auto 0 1 simp add: fset_eq_iff split: prod.splits) (metis assigns_less_Length less_not_refl)+
   next
     let ?f = "sum ((^) (2 :: nat))"
     note fmember.rep_eq[symmetric, simp]
     case (Eq_Presb l M n)
     moreover
     let ?M = "fset (M\<^bsup>\<AA>\<^esup>SO)" and ?L = "Length \<AA>"
     have "?f (insert ?L ?M) = 2 ^ ?L + ?f ?M"
       by (subst sum.insert) auto
     moreover have "n > 0 \<Longrightarrow> 2 ^ Max {i. 2 ^ i \<le> n} \<le> n"
       using Max_in[of "{i. 2 ^ i \<le> n}", simplified, OF exI[of _ 0]] by auto
     moreover
     { have "?f ?M \<le> ?f {0 ..< ?L}" by (rule sum_mono2) auto
       also have "\<dots> = 2 ^ ?L - 1" by (rule sum_pow2_upto)
       also have "\<dots> < 2 ^ ?L" by simp
       finally have "?f ?M < 2 ^ ?L" .
     }
     moreover have "Max {i. 2 ^ i \<le> 2 ^ ?L + ?f ?M} = ?L"
     proof (intro Max_eqI, safe)
       fix y assume "2 ^ y \<le> 2 ^ ?L + ?f ?M"
       { assume "?L < y"
         then have "(2 :: nat) ^ ?L + 2 ^ ?L \<le> 2 ^ y"
           by (cases y) (auto simp: less_Suc_eq_le numeral_eq_Suc add_le_mono)
         also note \<open>2 ^ y \<le> 2 ^ ?L + ?f ?M\<close>
         finally have " 2 ^ ?L \<le> ?f ?M" by simp
         with \<open>?f ?M < 2 ^ ?L\<close> have False by auto
       } then show "y \<le> ?L" by (intro leI) blast
     qed auto
     ultimately show ?case by (auto split: prod.splits option.splits nat.splits)
   qed (auto split: prod.splits)
next
   fix a :: ws1s and \<AA> \<BB> :: interp
   assume "wf0 (#\<^sub>V \<BB>) a" "#\<^sub>V \<AA> = #\<^sub>V \<BB>" "(\<And>m k. LESS k m (#\<^sub>V \<BB>) \<Longrightarrow> m\<^bsup>\<AA>\<^esup>k = m\<^bsup>\<BB>\<^esup>k)" "lformula0 a"
   then show "satisfies0 \<AA> a \<longleftrightarrow> satisfies0 \<BB> a" by (induct a) auto
next
   fix a :: ws1s
   assume "lformula0 a"
   moreover
   define d where "d = Formula_Operations.deriv extend lderiv0"
   define \<Phi> :: "_ \<Rightarrow> (ws1s, order) aformula set"
     where "\<Phi> a =
       (case a of
         Fo m \<Rightarrow> {FBase (Fo m), FBool True}
       | Eq_Const None m n \<Rightarrow> {FBase (Eq_Const None m i) | i . i \<le> n} \<union> {FBool True, FBool False}
       | Less None m1 m2 \<Rightarrow> {FBase (Less None m1 m2), FBase (Fo m2), FBool True, FBool False}
       | Plus_FO None m1 m2 n \<Rightarrow> {FBase (Eq_Const None m1 i) | i . i \<le> n} \<union>
          {FBase (Plus_FO None m1 m2 n), FBool True, FBool False}
       | Eq_FO False m1 m2 \<Rightarrow> {FBase (Eq_FO False m1 m2), FBool True, FBool False}
       | Eq_SO M1 M2 \<Rightarrow> {FBase (Eq_SO M1 M2), FBool False}
       | Suc_SO False bl M1 M2 \<Rightarrow> {FBase (Suc_SO False True M1 M2), FBase (Suc_SO False False M1 M2),
           FBool False}
       | Empty M \<Rightarrow> {FBase (Empty M), FBool False}
       | Singleton M \<Rightarrow> {FBase (Singleton M), FBase (Empty M), FBool False}
       | Subset M1 M2 \<Rightarrow> {FBase (Subset M1 M2), FBool False}
       | In False i I \<Rightarrow> {FBase (In False i I), FBool True, FBool False}
       | Eq_Max False m M \<Rightarrow> {FBase (Eq_Max False m M), FBase (Empty M), FBool False}
       | Eq_Min False m M \<Rightarrow> {FBase (Eq_Min False m M), FBool True, FBool False}
       | Eq_Union M1 M2 M3 \<Rightarrow> {FBase (Eq_Union M1 M2 M3), FBool False}
       | Eq_Inter M1 M2 M3 \<Rightarrow> {FBase (Eq_Inter M1 M2 M3), FBool False}
       | Eq_Diff M1 M2 M3 \<Rightarrow> {FBase (Eq_Diff M1 M2 M3), FBool False}
       | Disjoint M1 M2 \<Rightarrow> {FBase (Disjoint M1 M2), FBool False}
       | Eq_Presb None M n \<Rightarrow> {FBase (Eq_Presb None M i) | i . i \<le> n} \<union> {FBool False}
       | _ \<Rightarrow> {})" for a
   { fix xs
     note Formula_Operations.fold_deriv_FBool[simp] Formula_Operations.deriv.simps[simp] \<Phi>_def[simp]
     from \<open>lformula0 a\<close> have "FBase a \<in> \<Phi> a" by auto
     moreover have "\<And>x \<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> d x \<phi> \<in> \<Phi> a"
       by (auto simp: d_def split: atomic.splits list.splits bool.splits if_splits option.splits)
     then have "\<And>\<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> fold d xs \<phi> \<in> \<Phi> a" by (induct xs) auto
     ultimately have "fold d xs (FBase a) \<in> \<Phi> a" by blast
   }
   moreover have "finite (\<Phi> a)" using \<open>lformula0 a\<close> unfolding \<Phi>_def by (auto split: atomic.splits)
   ultimately show "finite {fold d xs (FBase a) | xs. True}" by (blast intro: finite_subset)
next
   fix a :: ws1s
   define d where "d = Formula_Operations.deriv extend rderiv0"
   define \<Phi> :: "_ \<Rightarrow> (ws1s, order) aformula set"
     where "\<Phi> a =
       (case a of
         Fo m \<Rightarrow> {FBase (Fo m), FBool True}
       | Eq_Const i m n \<Rightarrow>
          {FBase (Eq_Const (Some j) m n) | j . j \<le> (case i of Some i \<Rightarrow> max i n | _ \<Rightarrow> n)} \<union>
          {FBase (Eq_Const None m n)}
       | Less b m1 m2 \<Rightarrow> {FBase (Less None m1 m2), FBase (Less (Some True) m1 m2),
          FBase (Less (Some False) m1 m2)}
       | Plus_FO i m1 m2 n \<Rightarrow> 
          {FBase (Plus_FO (Some j) m1 m2 n) | j . j \<le> (case i of Some i \<Rightarrow> max i n | _ \<Rightarrow> n)} \<union>
          {FBase (Plus_FO None m1 m2 n)}
       | Eq_FO b m1 m2 \<Rightarrow> {FBase (Eq_FO True m1 m2), FBase (Eq_FO False m1 m2)}
       | Eq_SO M1 M2 \<Rightarrow> {FBase (Eq_SO M1 M2), FBool False}
       | Suc_SO br bl M1 M2 \<Rightarrow> {FBase (Suc_SO False True M1 M2), FBase (Suc_SO False False M1 M2),
           FBase (Suc_SO True True M1 M2), FBase (Suc_SO True False M1 M2), FBool False}
       | Empty M \<Rightarrow> {FBase (Empty M), FBool False}
       | Singleton M \<Rightarrow> {FBase (Singleton M), FBase (Empty M), FBool False}
       | Subset M1 M2 \<Rightarrow> {FBase (Subset M1 M2), FBool False}
       | In b i I \<Rightarrow> {FBase (In True i I), FBase (In False i I)}
       | Eq_Max b m M \<Rightarrow> {FBase (Eq_Max False m M), FBase (Eq_Max True m M), FBool False}
       | Eq_Min b m M \<Rightarrow> {FBase (Eq_Min False m M), FBase (Eq_Min True m M)}
       | Eq_Union M1 M2 M3 \<Rightarrow> {FBase (Eq_Union M1 M2 M3), FBool False}
       | Eq_Inter M1 M2 M3 \<Rightarrow> {FBase (Eq_Inter M1 M2 M3), FBool False}
       | Eq_Diff M1 M2 M3 \<Rightarrow> {FBase (Eq_Diff M1 M2 M3), FBool False}
       | Disjoint M1 M2 \<Rightarrow> {FBase (Disjoint M1 M2), FBool False}
       | Eq_Presb i M n \<Rightarrow> {FBase (Eq_Presb (Some l) M j) | j l .
           j \<le> (case i of Some i \<Rightarrow> max i n | _ \<Rightarrow> n) \<and> l \<le> (case i of Some i \<Rightarrow> max i n | _ \<Rightarrow> n)} \<union>
           {FBase (Eq_Presb None M n), FBool False})" for a
   { fix xs
     note Formula_Operations.fold_deriv_FBool[simp] Formula_Operations.deriv.simps[simp] \<Phi>_def[simp]
     then have "FBase a \<in> \<Phi> a" by (auto split: atomic.splits option.splits)
     moreover have "\<And>x \<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> d x \<phi> \<in> \<Phi> a"
       by (auto simp add: d_def Let_def not_le gr0_conv_Suc leD[OF ld_bounded]
         split: atomic.splits list.splits bool.splits if_splits option.splits nat.splits)
     then have "\<And>\<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> fold d xs \<phi> \<in> \<Phi> a"
       by (induct xs) auto
     ultimately have "fold d xs (FBase a) \<in> \<Phi> a" by blast
   }
   moreover have "finite (\<Phi> a)" unfolding \<Phi>_def using [[simproc add: finite_Collect]]
     by (auto split: atomic.splits)
   ultimately show "finite {fold d xs (FBase a) | xs. True}" by (blast intro: finite_subset)
next
  fix k l and a :: ws1s
  show "find0 k l a \<longleftrightarrow> l \<in> FV0 k a" by (induct a rule: find0.induct) auto
next
  fix a :: ws1s and k :: order
  show "finite (FV0 k a)" by (cases k) (induct a, auto)+
next
  fix idx a k v
  assume "wf0 idx a" "v \<in> FV0 k a"
  then show "LESS k v idx" by (cases k) (induct a, auto)+
next
  fix idx k i
  assume "LESS k i idx"
  then show "Formula_Operations.wf SUC wf0 idx (Restrict k i)"
     unfolding Restrict_def by (cases k) (auto simp: Formula_Operations.wf.simps)
next
  fix k and i :: nat
  show "Formula_Operations.lformula lformula0 (Restrict k i)"
    unfolding Restrict_def by (cases k) (auto simp: Formula_Operations.lformula.simps)
next
  fix i \<AA> k P r
  assume "i\<^bsup>\<AA>\<^esup>k = P"
  then show "restrict k P \<longleftrightarrow>
    Formula_Operations.satisfies_gen Extend Length satisfies0 r \<AA> (Restrict k i)"
    unfolding restrict_def Restrict_def
    by (cases k) (auto simp: Formula_Operations.satisfies_gen.simps)
qed (auto simp: Extend_commute_unsafe downshift_def upshift_def fimage_iff Suc_le_eq len_def
  dec_def eval_def cut_def len_downshift_helper dest!: CONS_surj
  dest: fMax_ge fMax_ffilter_less fMax_boundedD fsubset_fsingletonD
  split!: order.splits if_splits)

(*Workaround for code generation*)
lemma check_eqv_code[code]: "check_eqv idx r s =
  ((ws1s_wf idx r \<and> ws1s_lformula r) \<and> (ws1s_wf idx s \<and> ws1s_lformula s) \<and>
  (case rtrancl_while (\<lambda>(p, q). final idx p = final idx q)
    (\<lambda>(p, q). map (\<lambda>a. (norm (deriv lderiv0 a p), norm (deriv lderiv0 a q))) (\<sigma> idx))
    (norm (RESTRICT r), norm (RESTRICT s)) of
    None \<Rightarrow> False
  | Some ([], x) \<Rightarrow> True
  | Some (a # list, x) \<Rightarrow> False))"
  unfolding check_eqv_def WS1S.check_eqv_def WS1S.step_alt ..

definition while where [code del, code_abbrev]: "while idx \<phi> = while_default (fut_default idx \<phi>)"
declare while_default_code[of "fut_default idx \<phi>" for idx \<phi>, folded while_def, code]

lemma check_eqv_sound: 
  "\<lbrakk>#\<^sub>V \<AA> = idx; check_eqv idx \<phi> \<psi>\<rbrakk> \<Longrightarrow> (WS1S.sat \<AA> \<phi> \<longleftrightarrow> WS1S.sat \<AA> \<psi>)"
  unfolding check_eqv_def by (rule WS1S.check_eqv_soundness)

lemma bounded_check_eqv_sound:
  "\<lbrakk>#\<^sub>V \<AA> = idx; bounded_check_eqv idx \<phi> \<psi>\<rbrakk> \<Longrightarrow> (WS1S.sat\<^sub>b \<AA> \<phi> \<longleftrightarrow> WS1S.sat\<^sub>b \<AA> \<psi>)"
  unfolding bounded_check_eqv_def by (rule WS1S.bounded_check_eqv_soundness)

method_setup check_equiv = \<open>
  let
    fun tac ctxt =
      let
        val conv = @{computation_check terms: Trueprop
          "0 :: nat" "1 :: nat" "2 :: nat" "3 :: nat" Suc
          "plus :: nat \<Rightarrow> _" "minus :: nat \<Rightarrow> _"
          "times :: nat \<Rightarrow> _" "divide :: nat \<Rightarrow> _" "modulo :: nat \<Rightarrow> _"
          "0 :: int" "1 :: int" "2 :: int" "3 :: int" "-1 :: int"
          check_eqv datatypes: formula "int list" integer idx
         "nat \<times> nat" "nat option" "bool option"} ctxt
      in
        CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1 conv)) ctxt) THEN'
        resolve_tac ctxt [TrueI]
      end
  in
    Scan.succeed (SIMPLE_METHOD' o tac)
  end
\<close>

end
