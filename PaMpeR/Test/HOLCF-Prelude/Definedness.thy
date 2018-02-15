section \<open>Definedness\<close>

theory Definedness
  imports
    Data_List
    "HOL-Library.Adhoc_Overloading"
begin

text \<open>
  This is an attempt for a setup for better handling bottom, by a better
  simp setup, and less breaking the abstractions.
\<close>

definition defined :: "'a :: pcpo \<Rightarrow> bool" where
  "defined x = (x \<noteq> \<bottom>)"

lemma defined_bottom [simp]: "\<not> defined \<bottom>"
  by (simp add: defined_def)

lemma defined_seq [simp]: "defined x \<Longrightarrow> seq\<cdot>x\<cdot>y = y"
  by (simp add: defined_def)

consts val :: "'a::type \<Rightarrow> 'b::type" ("\<lbrakk>_\<rbrakk>")

text \<open>val for booleans\<close>

definition val_Bool :: "tr \<Rightarrow> bool" where
  "val_Bool i = (THE j. i = Def j)"

adhoc_overloading
  val val_Bool

lemma defined_Bool_simps [simp]:
  "defined (Def i)"
  "defined TT"
  "defined FF"
  by (simp_all add: defined_def)

lemma val_Bool_simp1 [simp]:
  "\<lbrakk>Def i\<rbrakk> = i"
  by (simp_all add: val_Bool_def TT_def FF_def)

lemma val_Bool_simp2 [simp]:
  "\<lbrakk>TT\<rbrakk> = True"
  "\<lbrakk>FF\<rbrakk> = False"
  by (simp_all add: TT_def FF_def)

lemma IF_simps [simp]:
  "defined b \<Longrightarrow> \<lbrakk> b \<rbrakk> \<Longrightarrow> (If b then x else y) = x"
  "defined b \<Longrightarrow> \<lbrakk> b \<rbrakk> = False \<Longrightarrow> (If b then x else y) = y"
  by (cases b, simp_all)+

lemma defined_neg [simp]: "defined (neg\<cdot>b) \<longleftrightarrow> defined b"
  by (cases b, auto)

lemma val_Bool_neg [simp]: "defined b \<Longrightarrow> \<lbrakk> neg \<cdot> b \<rbrakk> = (\<not> \<lbrakk> b \<rbrakk>)"
  by (cases b, auto)

text \<open>val for integers\<close>

definition val_Integer :: "Integer \<Rightarrow> int" where
  "val_Integer i = (THE j. i = MkI\<cdot>j)"

adhoc_overloading
  val val_Integer

lemma defined_Integer_simps [simp]:
  "defined (MkI\<cdot>i)"
  "defined (0::Integer)"
  "defined (1::Integer)"
  by (simp_all add: defined_def)

lemma defined_numeral [simp]: "defined (numeral x :: Integer)"
  by (simp add: defined_def)

lemma val_Integer_simps [simp]:
  "\<lbrakk>MkI\<cdot>i\<rbrakk> = i"
  "\<lbrakk>0\<rbrakk> = 0"
  "\<lbrakk>1\<rbrakk> = 1"
  by (simp_all add: val_Integer_def)

lemma val_Integer_numeral [simp]: "\<lbrakk> numeral x :: Integer \<rbrakk> = numeral x"
  by (simp_all add: val_Integer_def)


lemma val_Integer_to_MkI:
  "defined i \<Longrightarrow> i = (MkI \<cdot> \<lbrakk> i \<rbrakk>)"
  apply (cases i)
   apply (auto simp add: val_Integer_def defined_def)
  done

lemma defined_Integer_minus [simp]: "defined i \<Longrightarrow> defined j \<Longrightarrow> defined (i - (j::Integer))"
  apply (cases i, auto)
  apply (cases j, auto)
  done

lemma val_Integer_minus [simp]: "defined i \<Longrightarrow> defined j \<Longrightarrow> \<lbrakk> i - j \<rbrakk> = \<lbrakk> i \<rbrakk> - \<lbrakk> j \<rbrakk>"
  apply (cases i, auto)
  apply (cases j, auto)
  done

lemma defined_Integer_plus [simp]: "defined i \<Longrightarrow> defined j \<Longrightarrow> defined (i + (j::Integer))"
  apply (cases i, auto)
  apply (cases j, auto)
  done

lemma val_Integer_plus [simp]: "defined i \<Longrightarrow> defined j \<Longrightarrow> \<lbrakk> i + j \<rbrakk> = \<lbrakk> i \<rbrakk> + \<lbrakk> j \<rbrakk>"
  apply (cases i, auto)
  apply (cases j, auto)
  done

lemma defined_Integer_eq [simp]: "defined (eq\<cdot>a\<cdot>b) \<longleftrightarrow> defined a \<and> defined (b::Integer)"
  apply (cases a, simp)
  apply (cases b, simp)
  apply simp
  done

lemma val_Integer_eq [simp]: "defined a \<Longrightarrow> defined b \<Longrightarrow> \<lbrakk> eq\<cdot>a\<cdot>b \<rbrakk> = (\<lbrakk> a \<rbrakk> = (\<lbrakk> b \<rbrakk> :: int))"
  apply (cases a, simp)
  apply (cases b, simp)
  apply simp
  done


text \<open>Full induction for non-negative integers\<close>

lemma nonneg_full_Int_induct [consumes 1, case_names neg Suc]:
  assumes defined: "defined i"
  assumes neg: "\<And> i. defined i \<Longrightarrow> \<lbrakk>i\<rbrakk> < 0 \<Longrightarrow> P i"
  assumes step: "\<And> i. defined i \<Longrightarrow> 0 \<le> \<lbrakk>i\<rbrakk> \<Longrightarrow> (\<And> j. defined j \<Longrightarrow> \<lbrakk> j \<rbrakk> < \<lbrakk> i \<rbrakk> \<Longrightarrow> P j) \<Longrightarrow> P i"
  shows "P (i::Integer)"
proof (cases i)
  case bottom
  then have False using defined by simp
  then show ?thesis ..
next
  case (MkI integer)
  show ?thesis
  proof (cases integer)
    case neg
    then show ?thesis using assms(2) MkI by simp
  next
    case (nonneg nat)
    have "P (MkI\<cdot>(int nat))"
    proof(induction nat rule:full_nat_induct)
      case (1 nat)
      have "defined (MkI\<cdot>(int nat))" by simp
      moreover
      have "0 \<le> \<lbrakk> MkI\<cdot>(int nat) \<rbrakk>"  by simp
      moreover
      { fix j::Integer
        assume "defined j" and le: "\<lbrakk> j \<rbrakk> < \<lbrakk> MkI\<cdot>(int nat) \<rbrakk>"
        have "P j"
        proof(cases j)
          case bottom with \<open>defined j\<close> show ?thesis by simp
        next
          case (MkI integer)
          show ?thesis
          proof(cases integer)
            case (neg nat)
            have "\<lbrakk>j\<rbrakk> < 0" using neg MkI by simp
            with \<open>defined j\<close>
            show ?thesis by (rule assms(2))
          next
            case (nonneg m)
            have "Suc m \<le> nat" using le nonneg MkI by simp
            then have "P (MkI\<cdot>(int m))" by (metis "1.IH")
            then show ?thesis using nonneg MkI by simp
          qed
        qed
      }
      ultimately
      show ?case
        by (rule step)
    qed
    then show ?thesis using nonneg MkI by simp
  qed
qed

text \<open>Some list lemmas re-done with the new setup.\<close>

lemma nth_tail: (* TODO: move *)
  "defined n \<Longrightarrow> \<lbrakk> n \<rbrakk> \<ge> 0  \<Longrightarrow> tail\<cdot>xs !! n = xs !! (1 + n)"
  apply (cases xs, simp_all)
  apply (cases n, simp)
  apply (simp add: one_Integer_def zero_Integer_def)
  done

lemma nth_zipWith: (* TODO: move *)
  assumes f1 [simp]: "\<And>y. f\<cdot>\<bottom>\<cdot>y = \<bottom>"
  assumes f2 [simp]: "\<And>x. f\<cdot>x\<cdot>\<bottom> = \<bottom>"
  shows "zipWith\<cdot>f\<cdot>xs\<cdot>ys !! n = f\<cdot>(xs !! n)\<cdot>(ys !! n)"
proof (induct xs arbitrary: ys n)
  case (Cons x xs ys n) then show ?case
    by (cases ys, simp_all split:nth_Cons_split)
qed simp_all


lemma nth_neg [simp]: "defined n \<Longrightarrow> \<lbrakk> n \<rbrakk> < 0 \<Longrightarrow> nth\<cdot>xs\<cdot>n = \<bottom>"
proof (induction xs arbitrary: n)
  have [simp]: "eq\<cdot>n\<cdot>0 = TT \<longleftrightarrow> (n::Integer) = 0" for n
    by (cases n, auto simp add: zero_Integer_def)
  case (Cons a xs n)
  have "eq\<cdot>n\<cdot>0 = FF"
    using Cons.prems
    by (cases "eq\<cdot>n\<cdot>0") auto
  then show ?case
    using Cons.prems
    by (auto intro: Cons.IH)
qed simp_all

lemma nth_Cons_simp [simp]:
  "defined n \<Longrightarrow> \<lbrakk> n \<rbrakk> = 0 \<Longrightarrow> nth\<cdot>(x : xs)\<cdot>n = x"
  "defined n \<Longrightarrow> \<lbrakk> n \<rbrakk> > 0 \<Longrightarrow> nth\<cdot>(x : xs)\<cdot>n = nth\<cdot>xs\<cdot>(n - 1)"
proof -
  assume "defined n" and "\<lbrakk> n \<rbrakk> = 0"
  then have "n = 0"  by (cases n) auto
  then show "nth\<cdot>(x : xs)\<cdot>n = x" by simp
next
  assume "defined n" and "\<lbrakk> n \<rbrakk> > 0"
  then have "eq\<cdot>n\<cdot>0 = FF" by (cases "eq\<cdot>n\<cdot>0") auto
  then show "nth\<cdot>(x : xs)\<cdot>n = nth\<cdot>xs\<cdot>(n - 1)" by simp
qed

end