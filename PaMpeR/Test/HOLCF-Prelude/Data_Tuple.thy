section \<open>Data: Tuple\<close>

theory Data_Tuple
  imports
    Type_Classes
    Data_Bool
begin

subsection \<open>Datatype definitions\<close>

domain Unit ("\<langle>\<rangle>") = Unit ("\<langle>\<rangle>")

domain ('a, 'b) Tuple2 ("\<langle>_, _\<rangle>") =
  Tuple2 (lazy fst :: "'a") (lazy snd :: "'b") ("\<langle>_, _\<rangle>")

notation Tuple2 ("\<langle>,\<rangle>")

fixrec uncurry :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> \<langle>'a, 'b\<rangle> \<rightarrow> 'c"
  where "uncurry\<cdot>f\<cdot>p = f\<cdot>(fst\<cdot>p)\<cdot>(snd\<cdot>p)"

fixrec curry :: "(\<langle>'a, 'b\<rangle>  \<rightarrow> 'c) \<rightarrow> 'a \<rightarrow> 'b \<rightarrow> 'c"
  where "curry\<cdot>f\<cdot>a\<cdot>b = f\<cdot>\<langle>a, b\<rangle>"

domain ('a, 'b, 'c) Tuple3 ("\<langle>_, _, _\<rangle>") =
  Tuple3 (lazy "'a") (lazy "'b") (lazy "'c") ("\<langle>_, _, _\<rangle>")

notation Tuple3 ("\<langle>,,\<rangle>")

subsection \<open>Type class instances\<close>

instantiation Unit :: Ord_linear
begin

definition
  "eq = (\<Lambda> \<langle>\<rangle> \<langle>\<rangle>. TT)"

definition
  "compare = (\<Lambda> \<langle>\<rangle> \<langle>\<rangle>. EQ)"

instance
  apply standard
        apply (unfold eq_Unit_def compare_Unit_def)
        apply simp
       apply (rename_tac x, case_tac x, simp, simp)
      apply (rename_tac x y, case_tac x, simp, case_tac y, simp, simp)
     apply (rename_tac x y, case_tac x, case_tac y, simp, simp, case_tac y, simp, simp)
    apply (rename_tac x y, case_tac x, simp, case_tac y, simp, simp)
   apply (rename_tac x, case_tac x, simp, simp)
  apply (rename_tac x y z, case_tac x, simp, case_tac y, simp, case_tac z, simp, simp)
  done

end

instantiation Tuple2 :: (Eq, Eq) Eq_strict
begin

definition
  "eq = (\<Lambda> \<langle>x1, y1\<rangle> \<langle>x2, y2\<rangle>. eq\<cdot>x1\<cdot>x2 andalso eq\<cdot>y1\<cdot>y2)"

instance proof
  fix x :: "\<langle>'a, 'b\<rangle>"
  show "eq\<cdot>x\<cdot>\<bottom> = \<bottom>"
    unfolding eq_Tuple2_def by (cases x, simp_all)
  show "eq\<cdot>\<bottom>\<cdot>x = \<bottom>"
    unfolding eq_Tuple2_def by simp
qed

end

lemma eq_Tuple2_simps [simp]:
  "eq\<cdot>\<langle>x1, y1\<rangle>\<cdot>\<langle>x2, y2\<rangle> = (eq\<cdot>x1\<cdot>x2 andalso eq\<cdot>y1\<cdot>y2)"
  unfolding eq_Tuple2_def by simp

instance Tuple2 :: (Eq_sym, Eq_sym) Eq_sym
proof
  fix x y :: "\<langle>'a, 'b\<rangle>"
  show "eq\<cdot>x\<cdot>y = eq\<cdot>y\<cdot>x"
    unfolding eq_Tuple2_def
    by (cases x, simp, (cases y, simp, simp add: eq_sym)+)
qed

instance Tuple2 :: (Eq_equiv, Eq_equiv) Eq_equiv
proof
  fix x y z :: "\<langle>'a, 'b\<rangle>"
  show "eq\<cdot>x\<cdot>x \<noteq> FF"
    by (cases x, simp_all)
  { assume "eq\<cdot>x\<cdot>y = TT" and "eq\<cdot>y\<cdot>z = TT" then show "eq\<cdot>x\<cdot>z = TT"
      by (cases x, simp, cases y, simp, cases z, simp, simp,
          fast intro: eq_trans) }
qed

instance Tuple2 :: (Eq_eq, Eq_eq) Eq_eq
proof
  fix x y :: "\<langle>'a, 'b\<rangle>"
  show "eq\<cdot>x\<cdot>x \<noteq> FF"
    by (cases x, simp_all)
  { assume "eq\<cdot>x\<cdot>y = TT" then show "x = y"
      by (cases x, simp, cases y, simp, simp, fast) }
qed

instantiation Tuple2 :: (Ord, Ord) Ord_strict
begin

definition
  "compare = (\<Lambda> \<langle>x1, y1\<rangle> \<langle>x2, y2\<rangle>.
    thenOrdering\<cdot>(compare\<cdot>x1\<cdot>x2)\<cdot>(compare\<cdot>y1\<cdot>y2))"

instance
  by standard (simp add: compare_Tuple2_def,
      rename_tac x, case_tac x, simp_all add: compare_Tuple2_def)

end

lemma compare_Tuple2_simps [simp]:
  "compare\<cdot>\<langle>x1, y1\<rangle>\<cdot>\<langle>x2, y2\<rangle> = thenOrdering\<cdot>(compare\<cdot>x1\<cdot>x2)\<cdot>(compare\<cdot>y1\<cdot>y2)"
  unfolding compare_Tuple2_def by simp

instance Tuple2 :: (Ord_linear, Ord_linear) Ord_linear
proof
  fix x y z :: "\<langle>'a, 'b\<rangle>"
  show "eq\<cdot>x\<cdot>y = is_EQ\<cdot>(compare\<cdot>x\<cdot>y)"
    by (cases x, simp, cases y, simp, simp add: eq_conv_compare)
  show "oppOrdering\<cdot>(compare\<cdot>x\<cdot>y) = compare\<cdot>y\<cdot>x"
    by (cases x, simp, cases y, simp, simp add: oppOrdering_thenOrdering)
  { assume "compare\<cdot>x\<cdot>y = EQ" then show "x = y"
      by (cases x, simp, cases y, simp, auto elim: compare_EQ_dest) }
  { assume "compare\<cdot>x\<cdot>y = LT" and "compare\<cdot>y\<cdot>z = LT" then show "compare\<cdot>x\<cdot>z = LT"
      apply (cases x, simp, cases y, simp, cases z, simp, simp)
      apply (elim disjE conjE)
         apply (fast elim!: compare_LT_trans)
        apply (fast dest: compare_EQ_dest)
       apply (fast dest: compare_EQ_dest)
      apply (drule compare_EQ_dest)
      apply (fast elim!: compare_LT_trans)
      done }
  show "compare\<cdot>x\<cdot>x \<sqsubseteq> EQ"
    by (cases x, simp_all)
qed

instantiation Tuple3 :: (Eq, Eq, Eq) Eq_strict
begin

definition
  "eq = (\<Lambda> \<langle>x1, y1, z1\<rangle> \<langle>x2, y2, z2\<rangle>.
    eq\<cdot>x1\<cdot>x2 andalso eq\<cdot>y1\<cdot>y2 andalso eq\<cdot>z1\<cdot>z2)"

instance proof
  fix x :: "\<langle>'a, 'b, 'c\<rangle>"
  show "eq\<cdot>x\<cdot>\<bottom> = \<bottom>"
    unfolding eq_Tuple3_def by (cases x, simp_all)
  show "eq\<cdot>\<bottom>\<cdot>x = \<bottom>"
    unfolding eq_Tuple3_def by simp
qed

end

lemma eq_Tuple3_simps [simp]:
  "eq\<cdot>\<langle>x1, y1, z1\<rangle>\<cdot>\<langle>x2, y2, z2\<rangle> = (eq\<cdot>x1\<cdot>x2 andalso eq\<cdot>y1\<cdot>y2 andalso eq\<cdot>z1\<cdot>z2)"
  unfolding eq_Tuple3_def by simp

instance Tuple3 :: (Eq_sym, Eq_sym, Eq_sym) Eq_sym
proof
  fix x y :: "\<langle>'a, 'b, 'c\<rangle>"
  show "eq\<cdot>x\<cdot>y = eq\<cdot>y\<cdot>x"
    unfolding eq_Tuple3_def
    by (cases x, simp, (cases y, simp, simp add: eq_sym)+)
qed

instance Tuple3 :: (Eq_equiv, Eq_equiv, Eq_equiv) Eq_equiv
proof
  fix x y z :: "\<langle>'a, 'b, 'c\<rangle>"
  show "eq\<cdot>x\<cdot>x \<noteq> FF"
    by (cases x, simp_all)
  { assume "eq\<cdot>x\<cdot>y = TT" and "eq\<cdot>y\<cdot>z = TT" then show "eq\<cdot>x\<cdot>z = TT"
      by (cases x, simp, cases y, simp, cases z, simp, simp,
          fast intro: eq_trans) }
qed

instance Tuple3 :: (Eq_eq, Eq_eq, Eq_eq) Eq_eq
proof
  fix x y :: "\<langle>'a, 'b, 'c\<rangle>"
  show "eq\<cdot>x\<cdot>x \<noteq> FF"
    by (cases x, simp_all)
  { assume "eq\<cdot>x\<cdot>y = TT" then show "x = y"
      by (cases x, simp, cases y, simp, simp, fast) }
qed

instantiation Tuple3 :: (Ord, Ord, Ord) Ord_strict
begin

definition
  "compare = (\<Lambda> \<langle>x1, y1, z1\<rangle> \<langle>x2, y2, z2\<rangle>.
    thenOrdering\<cdot>(compare\<cdot>x1\<cdot>x2)\<cdot>(thenOrdering\<cdot>(compare\<cdot>y1\<cdot>y2)\<cdot>(compare\<cdot>z1\<cdot>z2)))"

instance
  by standard (simp add: compare_Tuple3_def,
    rename_tac x, case_tac x, simp_all add: compare_Tuple3_def)

end

lemma compare_Tuple3_simps [simp]:
  "compare\<cdot>\<langle>x1, y1, z1\<rangle>\<cdot>\<langle>x2, y2, z2\<rangle> =
    thenOrdering\<cdot>(compare\<cdot>x1\<cdot>x2)\<cdot>
      (thenOrdering\<cdot>(compare\<cdot>y1\<cdot>y2)\<cdot>(compare\<cdot>z1\<cdot>z2))"
  unfolding compare_Tuple3_def by simp

instance Tuple3 :: (Ord_linear, Ord_linear, Ord_linear) Ord_linear
proof
  fix x y z :: "\<langle>'a, 'b, 'c\<rangle>"
  show "eq\<cdot>x\<cdot>y = is_EQ\<cdot>(compare\<cdot>x\<cdot>y)"
    by (cases x, simp, cases y, simp, simp add: eq_conv_compare)
  show "oppOrdering\<cdot>(compare\<cdot>x\<cdot>y) = compare\<cdot>y\<cdot>x"
    by (cases x, simp, cases y, simp, simp add: oppOrdering_thenOrdering)
  { assume "compare\<cdot>x\<cdot>y = EQ" then show "x = y"
      by (cases x, simp, cases y, simp, auto elim: compare_EQ_dest) }
  { assume "compare\<cdot>x\<cdot>y = LT" and "compare\<cdot>y\<cdot>z = LT" then show "compare\<cdot>x\<cdot>z = LT"
      apply (cases x, simp, cases y, simp, cases z, simp, simp)
      apply (elim disjE conjE)
              apply (fast elim!: compare_LT_trans)
             apply (fast dest: compare_EQ_dest)
            apply (fast dest: compare_EQ_dest)
           apply (fast dest: compare_EQ_dest)
          apply (fast dest: compare_EQ_dest)
         apply (drule compare_EQ_dest)
         apply (fast elim!: compare_LT_trans)
        apply (fast dest: compare_EQ_dest)
       apply (fast dest: compare_EQ_dest)
      apply (fast dest: compare_EQ_dest elim!: compare_LT_trans)
      done }
  show "compare\<cdot>x\<cdot>x \<sqsubseteq> EQ"
    by (cases x, simp_all)
qed

end