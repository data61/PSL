section "Weights for Dijkstra's Algorithm"
theory Weight
imports Complex_Main
begin

text \<open>
  In this theory, we set up a type class for weights, and
  a typeclass for weights with an infinity element. The latter
  one is used internally in Dijkstra's algorithm.

  Moreover, we provide a datatype that adds an infinity element to a given
  base type.
\<close>

subsection \<open>Type Classes Setup\<close>

class weight = ordered_ab_semigroup_add + comm_monoid_add + linorder
begin

lemma add_nonneg_nonneg [simp]:
  assumes "0 \<le> a" and "0 \<le> b" shows "0 \<le> a + b"
proof -
  have "0 + 0 \<le> a + b" 
    using assms by (rule add_mono)
  then show ?thesis by simp
qed

lemma add_nonpos_nonpos[simp]:
  assumes "a \<le> 0" and "b \<le> 0" shows "a + b \<le> 0"
proof -
  have "a + b \<le> 0 + 0"
    using assms by (rule add_mono)
  then show ?thesis by simp
qed

lemma add_nonneg_eq_0_iff:
  assumes x: "0 \<le> x" and y: "0 \<le> y"
  shows "x + y = 0 \<longleftrightarrow> x = 0 \<and> y = 0"
  by (metis add.comm_neutral add.left_neutral add_left_mono antisym x y)

lemma add_incr: "0\<le>b \<Longrightarrow> a \<le> a+b"
  by (metis add.comm_neutral add_left_mono)

lemma add_incr_left[simp, intro!]: "0\<le>b \<Longrightarrow> a \<le> b + a"
  by (metis add_incr add.commute)

lemma sum_not_less[simp, intro!]: 
  "0\<le>b \<Longrightarrow> \<not> (a+b < a)"
  "0\<le>a \<Longrightarrow> \<not> (a+b < b)"
  apply (metis add_incr less_le_not_le)
  apply (metis add_incr_left less_le_not_le)
  done

end

instance nat :: weight ..
instance int :: weight ..
instance rat :: weight ..
instance real :: weight ..

term top


class top_weight = order_top + weight +
  assumes inf_add_right[simp]: "a + top = top"
begin

lemma inf_add_left[simp]: "top + a = top"
  by (metis add.commute inf_add_right)

lemmas [simp] = top_unique less_top[symmetric]
  
lemma not_less_inf[simp]:
  "\<not> (a < top) \<longleftrightarrow> a=top"
  by simp
  
end

subsection \<open>Adding Infinity\<close>
text \<open>
  We provide a standard way to add an infinity element to any type.
\<close>

datatype 'a infty = Infty | Num 'a

primrec val where "val (Num d) = d"

lemma num_val_iff[simp]: "e\<noteq>Infty \<Longrightarrow> Num (val e) = e" by (cases e) auto

type_synonym NatB = "nat infty"

instantiation infty :: (weight) top_weight
begin
  definition "(0::'a infty) == Num 0"
  definition "top \<equiv> Infty"

  fun less_eq_infty where
    "less_eq Infty (Num _) \<longleftrightarrow> False" |
    "less_eq _ Infty \<longleftrightarrow> True" |
    "less_eq (Num a) (Num b) \<longleftrightarrow> a\<le>b"

  lemma [simp]: "Infty\<le>a \<longleftrightarrow> a=Infty"
    by (cases a) auto

  fun less_infty where
    "less Infty _ \<longleftrightarrow> False" |
    "less (Num _) Infty \<longleftrightarrow> True" |
    "less (Num a) (Num b) \<longleftrightarrow> a<b"

  lemma [simp]: "less a Infty \<longleftrightarrow> a \<noteq> Infty"
    by (cases a) auto

  fun plus_infty where 
    "plus _ Infty = Infty" |
    "plus Infty _ = Infty" |
    "plus (Num a) (Num b) = Num (a+b)"

  lemma [simp]: "plus Infty a = Infty" by (cases a) simp_all


  instance
    apply (intro_classes)
    apply (case_tac [!] x) [4]
    apply simp_all
    apply (case_tac [!] y) [3]
    apply (simp_all add: less_le_not_le)
    apply (case_tac z)
    apply (simp_all add: top_infty_def zero_infty_def)
    apply (case_tac [!] a) [4]
    apply simp_all
    apply (case_tac [!] b) [3]
    apply (simp_all add: ac_simps)
    apply (case_tac [!] c) [2]
    apply (simp_all add: ac_simps add_right_mono)
    apply (case_tac "(x,y)" rule: less_eq_infty.cases)
    apply (simp_all add: linear)
    done
end

subsubsection \<open>Unboxing\<close>

text \<open>Conversion between the constants defined by the
  typeclass, and the concrete functions on the @{typ "'a infty"} type. 
\<close>
lemma infty_inf_unbox:
  "Num a \<noteq> top"
  "top \<noteq> Num a"
  "Infty = top"
  by (auto simp add: top_infty_def)

lemma infty_ord_unbox:
  "Num a \<le> Num b \<longleftrightarrow> a \<le> b"
  "Num a < Num b \<longleftrightarrow> a < b"
  by auto

lemma infty_plus_unbox:
  "Num a + Num b = Num (a+b)"
  by (auto)

lemma infty_zero_unbox:
  "Num a = 0 \<longleftrightarrow> a = 0"
  "Num 0 = 0"
  by (auto simp: zero_infty_def)

lemmas infty_unbox = 
  infty_inf_unbox infty_zero_unbox infty_ord_unbox infty_plus_unbox

lemma inf_not_zero[simp]:
  "top\<noteq>(0::_ infty)" "(0::_ infty)\<noteq>top"
  apply (unfold zero_infty_def top_infty_def)
  apply auto
  done

lemma num_val_iff'[simp]: "e\<noteq>top \<Longrightarrow> Num (val e) = e" 
  by (cases e) (auto simp add: infty_unbox)

lemma infty_neE: 
  "\<lbrakk>a\<noteq>Infty; \<And>d. a=Num d \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  "\<lbrakk>a\<noteq>top; \<And>d. a=Num d \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (case_tac [!] a) (auto simp add: infty_unbox)

end
