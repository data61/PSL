(*  Title:      ListInf.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Additional definitions and results for lists\<close>

theory ListInf
imports List2 "../CommonSet/InfiniteSet2"
begin

subsection \<open>Infinite lists\<close>

text \<open>
  We define infinite lists as functions over natural numbers, i. e.,
  we use functions @{typ "nat \<Rightarrow> 'a"}
  as infinite lists over elements of @{typ "'a"}.
  Mapping functions to intervals lists \<open>[m..<n]\<close>
  yiels common finite lists.\<close>


subsubsection \<open>Appending a functions to a list\<close>

type_synonym 'a ilist = "nat \<Rightarrow> 'a"

definition i_append :: "'a list \<Rightarrow> 'a ilist \<Rightarrow> 'a ilist" (infixr "\<frown>" 65)
  where "xs \<frown> f \<equiv> \<lambda>n. if n < length xs then xs ! n else f (n - length xs)"

text \<open>
  Synonym for the lemma \<open>fun_eq_iff\<close>
  from the HOL library to unify lemma names for finite and infinite lists,
  providing \<open>list_eq_iff\<close> for finite and
  \<open>ilist_eq_iff\<close> for infinite lists.\<close>
lemmas expand_ilist_eq = fun_eq_iff
lemmas ilist_eq_iff = expand_ilist_eq

lemma i_append_nth: "(xs \<frown> f) n = (if n < length xs then xs ! n else f (n - length xs))"
by (simp add: i_append_def)
lemma i_append_nth1[simp]: "n < length xs \<Longrightarrow> (xs \<frown> f) n = xs ! n"
by (simp add: i_append_def)
lemma i_append_nth2[simp]: "length xs \<le> n \<Longrightarrow> (xs \<frown> f) n = f (n - length xs)"
by (simp add: i_append_def)
lemma i_append_Nil[simp]: "[] \<frown> f = f"
by (simp add: i_append_def)

lemma i_append_assoc[simp]: "xs \<frown> (ys \<frown> f) = (xs @ ys) \<frown> f"
apply (case_tac "ys = []", simp)
apply (fastforce simp: expand_ilist_eq i_append_def nth_append)
done

lemma i_append_Cons: "(x # xs) \<frown> f = [x] \<frown> (xs \<frown> f)"
by simp

lemma i_append_eq_i_append_conv[simp]: "
  length xs = length ys \<Longrightarrow>
  (xs \<frown> f = ys \<frown> g) = (xs = ys \<and> f = g)"
apply (rule iffI)
 prefer 2
 apply simp
apply (simp add: expand_ilist_eq expand_list_eq i_append_nth)
apply (intro conjI impI allI)
 apply (rename_tac x)
 apply (drule_tac x=x in spec)
 apply simp
apply (rename_tac x)
apply (drule_tac x="x + length ys" in spec)
apply simp
done

lemma i_append_eq_i_append_conv2_aux: "
  \<lbrakk> xs \<frown> f = ys \<frown> g; length xs \<le> length ys \<rbrakk> \<Longrightarrow>
  \<exists>zs. xs @ zs = ys \<and> f = zs \<frown> g"
apply (simp add: expand_ilist_eq expand_list_eq nth_append)
apply (rule_tac x="drop (length xs) ys" in exI)
apply simp
apply (rule conjI)
 apply (clarify, rename_tac i)
 apply (drule_tac x=i in spec)
 apply simp
apply (clarify, rename_tac i)
apply (drule_tac x="length xs + i" in spec)
apply (simp add: i_append_nth)
apply (case_tac "length xs + i < length ys")
 apply fastforce
apply (fastforce simp: add.commute[of _ "length xs"])
done

lemma i_append_eq_i_append_conv2: "
  (xs \<frown> f = ys \<frown> g) =
  (\<exists>zs. xs = ys @ zs \<and> zs \<frown> f = g \<or> xs @ zs = ys \<and> f = zs \<frown> g)"
apply (rule iffI)
 apply (case_tac "length xs \<le> length ys")
  apply (frule i_append_eq_i_append_conv2_aux, assumption)
  apply blast
 apply (simp add: linorder_not_le eq_commute[of "xs \<frown> f"], drule less_imp_le)
 apply (frule i_append_eq_i_append_conv2_aux, assumption)
 apply blast
apply fastforce
done

lemma same_i_append_eq[iff]: "(xs \<frown> f = xs \<frown> g) = (f = g)"
apply (rule iffI)
 apply (clarsimp simp: expand_ilist_eq, rename_tac i)
 apply (erule_tac x="length xs + i" in allE)
 apply simp
apply simp
done


lemma NOT_i_append_same_eq: "
  \<not>(\<forall>xs ys f. (xs \<frown> (f::(nat \<Rightarrow> nat)) = ys \<frown> f) = (xs = ys))"
apply simp
apply (rule_tac x="[]" in exI)
apply (rule_tac x="[0]" in exI)
apply (rule_tac x="\<lambda>n. 0" in exI)
apply (simp add: expand_ilist_eq i_append_nth)
done

lemma i_append_hd: "(xs \<frown> f) 0 = (if xs = [] then f 0 else hd xs)"
by (simp add: hd_eq_first)

lemma i_append_hd2[simp]: "xs \<noteq> [] \<Longrightarrow> (xs \<frown> f) 0 = hd xs"
by (simp add: i_append_hd)

lemma eq_Nil_i_appendI: "f = g \<Longrightarrow> f = [] \<frown> g"
by simp

lemma i_append_eq_i_appendI: "
  \<lbrakk> xs @ xs' = ys; f = xs' \<frown> g \<rbrakk> \<Longrightarrow> xs \<frown> f = ys \<frown> g"
by simp


lemma o_ext: "
  (\<forall>x. (x \<in> range h \<longrightarrow> f x = g x)) \<Longrightarrow> f \<circ> h = g \<circ> h"
by (simp add: expand_ilist_eq)

lemma i_append_o[simp]: "g \<circ> (xs \<frown> f) = (map g xs) \<frown> (g \<circ> f)"
by (simp add: expand_ilist_eq i_append_nth)

lemma o_eq_conv: "(f \<circ> h = g \<circ> h) = (\<forall>x\<in>range h. f x = g x)"
by (simp add: expand_ilist_eq)

lemma o_cong: "
  \<lbrakk> h = i; \<And>x. x \<in> range i \<Longrightarrow> f x = g x \<rbrakk> \<Longrightarrow> f \<circ> h = f \<circ> i"
by blast

lemma ex_o_conv: "(\<exists>h. g = f \<circ> h) = (\<forall>y\<in>range g. \<exists>x. y = f x)"
apply (rule iffI)
 apply fastforce
apply (simp add: expand_ilist_eq)
apply (rule_tac x="\<lambda>x. (SOME y. g x = f y)" in exI)
apply (fastforce intro: someI_ex)
done

lemma o_inj_on: "
  \<lbrakk> f \<circ> g = f \<circ> h; inj_on f (range g \<union> range h) \<rbrakk> \<Longrightarrow> g = h"
apply (rule expand_ilist_eq[THEN iffD2], clarify, rename_tac x)
apply (drule_tac x=x in fun_cong)
apply (rule inj_onD)
apply simp+
done

lemma inj_on_o_eq_o: "
  inj_on f (range g \<union> range h) \<Longrightarrow>
  (f \<circ> g = f \<circ> h) = (g = h)"
apply (rule iffI)
 apply (rule o_inj_on, assumption+)
apply simp
done

lemma o_injective: "\<lbrakk> f \<circ> g = f \<circ> h; inj f \<rbrakk> \<Longrightarrow> g = h"
by (simp add: expand_ilist_eq inj_on_def)

lemma inj_o_eq_o: "inj f \<Longrightarrow> (f \<circ> g = f \<circ> h) = (g = h)"
apply (rule iffI)
 apply (rule o_injective, assumption+)
apply simp
done

lemma inj_oI: "inj f \<Longrightarrow> inj (\<lambda>g. f \<circ> g)"
apply (simp add: inj_on_def)
apply (blast intro: o_inj_on[unfolded inj_on_def])
done

lemma inj_oD: "inj (\<lambda>g. f \<circ> g) \<Longrightarrow> inj f"
apply (clarsimp simp add: inj_on_def, rename_tac g h)
apply (erule_tac x="\<lambda>n. g" in allE)
apply (erule_tac x="\<lambda>n. h" in allE)
apply (simp add: expand_ilist_eq)
done

lemma inj_o[iff]: "inj (\<lambda>g. f \<circ> g) = inj f"
apply (rule iffI)
 apply (rule inj_oD, assumption)
apply (rule inj_oI, assumption)
done

lemma inj_on_oI: "
  inj_on f (\<Union> ((\<lambda>f. range f) ` A)) \<Longrightarrow> inj_on (\<lambda>g. f \<circ> g) A"
apply (rule inj_onI)
apply (rule o_inj_on, assumption)
apply (unfold inj_on_def)
apply force
done

lemma o_idI: "\<forall>x. x \<in> range g \<longrightarrow> f x = x \<Longrightarrow> f \<circ> g = g"
by (simp add: expand_ilist_eq)

lemma o_fun_upd[simp]: "y \<notin> range g \<Longrightarrow> f (y := x) \<circ> g = f \<circ> g"
by (fastforce simp: expand_ilist_eq)

lemma range_i_append[simp]: "range (xs \<frown> f) = set xs \<union> range f"
by (fastforce simp: in_set_conv_nth i_append_nth)

lemma set_subset_i_append: "set xs \<subseteq> range (xs \<frown> f)"
by simp

lemma range_subset_i_append: "range f \<subseteq> range (xs \<frown> f)"
by simp

lemma range_ConsD: "y \<in> range ([x] \<frown> f) \<Longrightarrow> y = x \<or> y \<in> range f"
by simp

lemma range_o [simp]: "range (f \<circ> g) = f ` range g"
by (simp add: image_comp)

lemma in_range_conv_decomp: "
  (x \<in> range f) = (\<exists>xs g. f = xs \<frown> ([x] \<frown> g))"
apply (simp add: image_iff)
apply (rule iffI)
 apply (clarify, rename_tac n)
 apply (rule_tac x="map f [0..<n]" in exI)
 apply (rule_tac x="\<lambda>i. f (i + Suc n)" in exI)
 apply (simp add: expand_ilist_eq i_append_nth nth_append linorder_not_less less_Suc_eq_le)
apply (clarify, rename_tac xs g)
apply (rule_tac x="length xs" in exI)
apply simp
done


text \<open>\<open>nth\<close>\<close>

lemma i_append_nth_Cons_0[simp]: "((x # xs) \<frown> f) 0 = x"
by simp

lemma i_append_nth_Cons_Suc[simp]:
  "((x # xs) \<frown> f) (Suc n) = (xs \<frown> f) n"
by (simp add: i_append_nth)

lemma i_append_nth_Cons: "
  ([x] \<frown> f) n = (case n of 0 \<Rightarrow> x | Suc k \<Rightarrow> f k)"
by (case_tac n, simp_all add: i_append_nth)

lemma i_append_nth_Cons': "
  ([x] \<frown> f) n = (if n = 0 then x else f (n - Suc 0))"
by (case_tac n, simp_all add: i_append_nth)

lemma i_append_nth_length[simp]: "(xs \<frown> f) (length xs) = f 0"
by simp

lemma i_append_nth_length_plus[simp]: "(xs \<frown> f) (length xs + n) = f n"
by simp

lemma range_iff: "(y \<in> range f) = (\<exists>x. y = f x)"
by blast

lemma range_ball_nth: "\<forall>y\<in>range f. P y \<Longrightarrow> P (f x)"
by blast

lemma all_nth_imp_all_range: "\<lbrakk> \<forall>x. P (f x);y \<in> range f \<rbrakk> \<Longrightarrow> P y"
by blast

lemma all_range_conv_all_nth: "(\<forall>y\<in>range f. P y) = (\<forall>x. P (f x))"
by blast

lemma i_append_update1: "
  n < length xs \<Longrightarrow> (xs \<frown> f) (n := x) = xs[n := x] \<frown> f"
by (simp add: expand_ilist_eq i_append_nth)

lemma i_append_update2: "
  length xs \<le> n \<Longrightarrow> (xs \<frown> f) (n := x) = xs \<frown> (f(n - length xs := x))"
by (fastforce simp: expand_ilist_eq i_append_nth)

lemma i_append_update: "
  (xs \<frown> f) (n := x) =
  (if n < length xs then xs[n := x] \<frown> f
   else xs \<frown> (f(n - length xs := x)))"
by (simp add: i_append_update1 i_append_update2)

lemma i_append_update_length[simp]: "
  (xs \<frown> f) (length xs := y) = xs \<frown> (f(0 := y))"
by (simp add: i_append_update2)

lemma range_update_subset_insert: "
  range (f(n := x)) \<subseteq> insert x (range f)"
by fastforce

lemma range_update_subsetI: "
  \<lbrakk> range f \<subseteq> A; x \<in> A \<rbrakk> \<Longrightarrow> range (f(n := x)) \<subseteq> A"
by fastforce

lemma range_update_memI: "x \<in> range (f(n := x))"
by fastforce


subsubsection \<open>@{term take} and @{term drop} for infinite lists\<close>

text \<open>
  The @{term i_take} operator takes the first @{term n} elements of an infinite list,
  i.e. \<open>i_take f n = [f 0, f 1, \<dots>, f (n-1)]\<close>.
  The @{term i_drop} operator drops the first @{term n} elements of an infinite list,
  i.e. \<open>(i_take f n) 0 = f n, (i_take f n) 1 = f (n + 1), \<dots>\<close>.\<close>

definition i_take  :: "nat \<Rightarrow> 'a ilist \<Rightarrow> 'a list"
  where "i_take n f \<equiv> map f [0..<n]"
definition i_drop  :: "nat \<Rightarrow> 'a ilist \<Rightarrow> 'a ilist"
  where "i_drop n f \<equiv> (\<lambda>x. f (n + x))"

abbreviation i_take' :: "'a ilist \<Rightarrow> nat \<Rightarrow> 'a list"  (infixl "\<Down>" 100)
  where "f \<Down> n \<equiv> i_take n f"
abbreviation i_drop' :: "'a ilist \<Rightarrow> nat \<Rightarrow> 'a ilist"  (infixl "\<Up>" 100)
  where "f \<Up> n \<equiv> i_drop n f"

lemma "f \<Down> n = map f [0..<n]"
by (simp add: i_take_def)
lemma "f \<Up> n = (\<lambda>x. f (n + x))"
by (simp add: i_drop_def)


text \<open>Basic results for @{term i_take} and @{term i_drop}\<close>

lemma i_take_first: "f \<Down> Suc 0 = [f 0]"
by (simp add: i_take_def)

lemma i_drop_i_take_1: "f \<Up> n \<Down> Suc 0 = [f n]"
by (simp add: i_drop_def i_take_def)

lemma i_take_take_eq1: "m \<le> n \<Longrightarrow> (f \<Down> n) \<down> m = f \<Down> m"
by (simp add: i_take_def take_map)

lemma i_take_take_eq2: "n \<le> m \<Longrightarrow> (f \<Down> n) \<down> m = f \<Down> n"
by (simp add: i_take_def take_map)

lemma i_take_take[simp]: "(f \<Down> n) \<down> m = f \<Down> min n m"
by (simp add: min_def i_take_take_eq1 i_take_take_eq2)

lemma i_drop_nth[simp]: "(s \<Up> n) x = s (n + x)"
by (simp add: i_drop_def)

lemma i_drop_nth_sub: "n \<le> x \<Longrightarrow> (s \<Up> n) (x - n) = s x"
by (simp add: i_drop_def)

theorem i_take_nth[simp]: "i < n \<Longrightarrow> (f \<Down> n) ! i = f i"
by (simp add: i_take_def)

lemma i_take_length[simp]: "length (f \<Down> n) = n"
by (simp add: i_take_def)

lemma i_take_0[simp]: "f \<Down> 0 = []"
by (simp add: i_take_def)

lemma i_drop_0[simp]: "f \<Up> 0 = f"
by (simp add: i_drop_def)

lemma i_take_eq_Nil[simp]: "(f \<Down> n = []) = (n = 0)"
by (simp add: length_0_conv[symmetric] del: length_0_conv)

lemma i_take_not_empty_conv: "(f \<Down> n \<noteq> []) = (0 < n)"
by simp

lemma last_i_take: "last (f \<Down> Suc n) = f n"
by (simp add: last_nth)

lemma last_i_take2: "0 < n \<Longrightarrow> last (f \<Down> n) = f (n - Suc 0)"
by (simp add: last_i_take[of _ f, symmetric])

lemma nth_0_i_drop: "(f \<Up> n) 0 = f n"
by simp

lemma i_take_const[simp]: "(\<lambda>n. x) \<Down> i = replicate i x"
by (simp add: expand_list_eq)

lemma i_drop_const[simp]: "(\<lambda>n. x) \<Up> i = (\<lambda>n. x)"
by (simp add: expand_ilist_eq)

lemma i_append_i_take_eq1: "
  n \<le> length xs \<Longrightarrow> (xs \<frown> f) \<Down> n = xs \<down> n"
by (simp add: expand_list_eq)

lemma i_append_i_take_eq2: "
  length xs \<le> n \<Longrightarrow> (xs \<frown> f) \<Down> n = xs @ (f \<Down> (n - length xs))"
by (simp add: expand_list_eq nth_append)

lemma i_append_i_take_if: "
  (xs \<frown> f) \<Down> n = (if n \<le> length xs then xs \<down> n else xs @ (f \<Down> (n - length xs)))"
by (simp add: i_append_i_take_eq1 i_append_i_take_eq2)

lemma i_append_i_take[simp]: "
  (xs \<frown> f) \<Down> n = (xs \<down> n) @ (f \<Down> (n - length xs))"
by (simp add: i_append_i_take_if)

lemma i_append_i_drop_eq1: "
  n \<le> length xs \<Longrightarrow> (xs \<frown> f) \<Up> n = (xs \<up> n) \<frown> f"
by (simp add: expand_ilist_eq i_append_nth less_diff_conv add.commute[of _ n])

lemma i_append_i_drop_eq2: "
  length xs \<le> n \<Longrightarrow> (xs \<frown> f) \<Up> n = f \<Up> (n - length xs)"
by (simp add: expand_ilist_eq i_append_nth)

lemma i_append_i_drop_if: "
  (xs \<frown> f) \<Up> n = (if n < length xs then (xs \<up> n) \<frown> f else f \<Up> (n - length xs))"
by (simp add: i_append_i_drop_eq1 i_append_i_drop_eq2)

lemma i_append_i_drop[simp]: "(xs \<frown> f) \<Up> n = (xs \<up> n) \<frown> (f \<Up> (n - length xs))"
by (simp add: i_append_i_drop_if)

lemma i_append_i_take_i_drop_id[simp]: "(f \<Down> n) \<frown> (f \<Up> n) = f"
by (simp add: expand_ilist_eq i_append_nth)

lemma ilist_i_take_i_drop_imp_eq: "
  \<lbrakk> f \<Down> n  = g \<Down> n; f \<Up> n = g \<Up> n \<rbrakk> \<Longrightarrow> f = g"
apply (subst i_append_i_take_i_drop_id[of n f, symmetric])
apply (subst i_append_i_take_i_drop_id[of n g, symmetric])
apply simp
done

lemma ilist_i_take_i_drop_eq_conv: "
  (f = g) = (\<exists>n. (f \<Down> n = g \<Down> n \<and> f \<Up> n = g \<Up> n))"
apply (rule iffI, simp)
apply (blast intro: ilist_i_take_i_drop_imp_eq)
done

lemma ilist_i_take_eq_conv: "(f = g) = (\<forall>n. f \<Down> n = g \<Down> n)"
apply (rule iffI, simp)
apply (clarsimp simp: expand_ilist_eq, rename_tac i)
apply (drule_tac x="Suc i" in spec)
apply (drule_tac f="\<lambda>xs. xs ! i" in arg_cong)
apply simp
done

lemma ilist_i_drop_eq_conv: "(f = g) = (\<forall>n. f \<Up> n = g \<Up> n)"
apply (rule iffI, simp)
apply (drule_tac x=0 in spec)
apply simp
done

lemma i_take_the_conv: "
  f \<Down> k = (THE xs. length xs = k \<and> (\<exists>g. xs \<frown> g = f))"
apply (rule the1I2)
 apply (rule_tac a="f \<Down> k" in ex1I)
 apply (fastforce intro: i_append_i_take_i_drop_id)+
done

lemma i_drop_the_conv: "
  f \<Up> k = (THE g. (\<exists>xs. length xs = k \<and> xs \<frown> g = f))"
apply (rule sym, rule the1_equality)
 apply (rule_tac a="f \<Up> k" in ex1I)
  apply (rule_tac x="f \<Down> k" in exI, simp)
 apply clarsimp
apply (rule_tac x="f \<Down> k" in exI, simp)
done

lemma i_take_Suc_append[simp]: "
  ((x # xs) \<frown> f) \<Down> Suc n = x # ((xs \<frown> f) \<Down> n)"
by (simp add: expand_list_eq)

corollary i_take_Suc_Cons: "([x] \<frown> f) \<Down> Suc n = x # (f \<Down> n)"
by simp

lemma i_drop_Suc_append[simp]: "((x # xs) \<frown> f) \<Up> Suc n = ((xs \<frown> f) \<Up> n)"
by (simp add: expand_list_eq)

corollary i_drop_Suc_Cons: "([x] \<frown> f) \<Up> Suc n = f \<Up> n"
by simp

lemma i_take_Suc: "f \<Down> Suc n = f 0 # (f \<Up> Suc 0 \<Down> n)"
by (simp add: expand_list_eq nth_Cons')

lemma i_take_Suc_conv_app_nth: "f \<Down> Suc n = (f \<Down> n) @ [f n]"
by (simp add: i_take_def)

lemma i_drop_i_drop[simp]: "s \<Up> a \<Up> b = s \<Up> (a + b)"
by (simp add: i_drop_def add.assoc)

corollary i_drop_Suc: "f \<Up> Suc 0 \<Up> n = f \<Up> Suc n"
by simp

lemma i_take_commute: "s \<Down> a \<down> b = s \<Down> b \<down> a"
by (simp add: ac_simps)

lemma i_drop_commute: "s \<Up> a \<Up> b = s \<Up> b \<Up> a"
by (simp add: add.commute[of a])

corollary i_drop_tl: "f \<Up> Suc 0 \<Up> n = f \<Up> n \<Up> Suc 0"
by simp

lemma nth_via_i_drop: "(f \<Up> n) 0 = x \<Longrightarrow> f n = x"
by simp

lemma i_drop_Suc_conv_tl: "[f n] \<frown> (f \<Up> Suc n) = f \<Up> n"
by (simp add: expand_ilist_eq i_append_nth)

lemma i_drop_Suc_conv_tl': "([f n] \<frown> f) \<Up> Suc n = f \<Up> n"
by (simp add: i_drop_Suc_Cons)

lemma i_take_i_drop: "f \<Up> m \<Down> n = f \<Down> (n + m) \<up> m"
by (simp add: expand_list_eq)


text \<open>Appending an interval of a function\<close>
lemma i_take_int_append: "
  m \<le> n \<Longrightarrow> (f \<Down> m) @ map f [m..<n] = f \<Down> n"
by (simp add: expand_list_eq nth_append)

lemma i_take_drop_map_empty_iff: "(f \<Down> n \<up> m = []) = (n \<le> m)"
by simp

lemma i_take_drop_map: "f \<Down> n \<up> m = map f [m..<n]"
by (simp add: expand_list_eq)

corollary i_take_drop_append[simp]: "
  m \<le> n \<Longrightarrow> (f \<Down> m) @ (f \<Down> n \<up> m) = f \<Down> n"
by (simp add: i_take_drop_map i_take_int_append)

lemma i_take_drop: "f \<Down> n \<up> m = f \<Up> m \<Down> (n - m)"
by (simp add: expand_list_eq)

lemma i_take_o[simp]: "(f \<circ> g) \<Down> n = map f (g \<Down> n)"
by (simp add: expand_list_eq)

lemma i_drop_o[simp]: "(f \<circ> g) \<Up> n = f \<circ> (g \<Up> n)"
by (simp add: expand_ilist_eq)

lemma set_i_take_subset: "set (f \<Down> n) \<subseteq> range f"
by (fastforce simp: in_set_conv_nth)

lemma range_i_drop_subset: "range (f \<Up> n) \<subseteq> range f"
by fastforce

lemma in_set_i_takeD: "x \<in> set (f \<Down> n) \<Longrightarrow> x \<in> range f"
by (rule subsetD[OF set_i_take_subset])

lemma in_range_i_takeD: "x \<in> range (f \<Up> n) \<Longrightarrow> x \<in> range f"
by (rule subsetD[OF range_i_drop_subset])

lemma i_append_eq_conv_conj: "
  ((xs \<frown> f) = g) = (xs = g \<Down> length xs \<and> f = g \<Up> length xs)"
apply (simp add: expand_ilist_eq expand_list_eq i_append_nth)
apply (rule iffI)
 apply (clarsimp, rename_tac x)
 apply (drule_tac x="length xs + x" in spec)
 apply simp
apply simp
done

lemma i_take_add: "f \<Down> (i + j) = (f \<Down> i) @ (f \<Up> i \<Down> j)"
by (simp add: expand_list_eq nth_append)

lemma i_append_eq_i_append_conv_if_aux: "
  length xs \<le> length ys \<Longrightarrow>
  (xs \<frown> f = ys \<frown> g) = (xs = ys \<down> length xs \<and> f = (ys \<up> length xs) \<frown> g)"
apply (simp add: expand_list_eq expand_ilist_eq i_append_nth min_eqR)
apply (rule iffI)
 apply simp
 apply (clarify, rename_tac x)
 apply (drule_tac x="length xs + x" in spec)
 apply (simp add: less_diff_conv add.commute[of _ "length xs"])
apply simp
done

lemma i_append_eq_i_append_conv_if: "
  (xs \<frown> f = ys \<frown> g) =
  (if length xs \<le> length ys
   then xs = ys \<down> length xs \<and> f = (ys \<up> length xs) \<frown> g
   else xs \<down> length ys = ys \<and> (xs \<up> length ys) \<frown> f = g)"
apply (split if_split, intro conjI impI)
 apply (simp add: i_append_eq_i_append_conv_if_aux)
apply (force simp: eq_commute[of "xs \<frown> f"] i_append_eq_i_append_conv_if_aux)
done

lemma i_take_hd_i_drop: "(f \<Down> n) @ [(f \<Up> n) 0] = f \<Down> Suc n"
by (simp add: i_take_Suc_conv_app_nth)

lemma id_i_take_nth_i_drop: "f = (f \<Down> n) \<frown> (([f n] \<frown> f) \<Up> Suc n)"
by (simp add: i_drop_Suc_Cons)

lemma upd_conv_i_take_nth_i_drop: "
  f (n := x) = (f \<Down> n) \<frown> ([x] \<frown> (f \<Up> Suc n))"
by (simp add: expand_ilist_eq nth_append i_append_nth)

theorem i_take_induct: "
  \<lbrakk> P (f \<Down> 0); \<And>n. P (f \<Down> n) \<Longrightarrow> P ( f \<Down> Suc n) \<rbrakk> \<Longrightarrow> P ( f \<Down> n)"
by (rule nat.induct)

theorem take_induct[rule_format]: "
  \<lbrakk> P (s \<down> 0);
    \<And>n.  \<lbrakk> Suc n < length s; P (s \<down> n) \<rbrakk> \<Longrightarrow> P ( s \<down> Suc n);
    i < length s\<rbrakk>
  \<Longrightarrow> P (s \<down> i)"
by (induct i, simp+)

theorem i_drop_induct: "
  \<lbrakk> P (f \<Up> 0); \<And>n. P (f \<Up> n) \<Longrightarrow> P ( f \<Up> Suc n) \<rbrakk> \<Longrightarrow> P ( f \<Up> n)"
by (rule nat.induct)

theorem f_drop_induct[rule_format]: "
  \<lbrakk> P (s \<up> 0);
    \<And>n.  \<lbrakk> Suc n < length s; P (s \<up> n) \<rbrakk> \<Longrightarrow> P ( s \<up> Suc n);
    i < length s\<rbrakk>
  \<Longrightarrow> P (s \<up> i)"
by (induct i, simp+)


lemma i_take_drop_eq_map: "f \<Up> m \<Down> n = map f [m..<m+n]"
by (simp add: expand_list_eq)

lemma o_eq_i_append_imp: "
  f \<circ> g = ys \<frown> i \<Longrightarrow>
  \<exists>xs h. g = xs \<frown> h \<and> map f xs = ys \<and> f \<circ> h = i"
apply (rule_tac x="g \<Down> (length ys)" in exI)
apply (rule_tac x="g \<Up> (length ys)" in exI)
apply (frule arg_cong[where f="\<lambda>x. x \<Down> length ys"])
apply (drule arg_cong[where f="\<lambda>x. x \<Up> length ys"])
apply simp
done

corollary o_eq_i_append_conv: "
  (f \<circ> g = ys \<frown> i) =
  (\<exists>xs h. g = xs \<frown> h \<and> map f xs = ys \<and> f \<circ> h = i)"
by (fastforce simp: o_eq_i_append_imp)
corollary i_append_eq_o_conv: "
  (ys \<frown> i = f \<circ> g) =
  (\<exists>xs h. g = xs \<frown> h \<and> map f xs = ys \<and> f \<circ> h = i)"
by (fastforce simp: o_eq_i_append_imp)


subsubsection \<open>@{term zip} for infinite lists\<close>

definition i_zip :: "'a ilist \<Rightarrow> 'b ilist \<Rightarrow> ('a \<times> 'b) ilist"
  where "i_zip f g \<equiv> \<lambda>n. (f n, g n)"

lemma i_zip_nth: "(i_zip f g) n = (f n, g n)"
by (simp add: i_zip_def)

lemma i_zip_swap: "(\<lambda>(y, x). (x, y)) \<circ> i_zip g f = i_zip f g"
by (simp add: expand_ilist_eq i_zip_nth)

lemma i_zip_i_take: "(i_zip f g) \<Down> n = zip (f \<Down> n) (g \<Down> n)"
by (simp add: expand_list_eq i_zip_nth)

lemma i_zip_i_drop: "(i_zip f g) \<Up> n = i_zip (f \<Up> n) (g \<Up> n)"
by (simp add: expand_ilist_eq i_zip_nth)

lemma fst_o_izip: "fst \<circ> (i_zip f g) = f"
by (simp add: expand_ilist_eq i_zip_nth)

lemma snd_o_i_zip: "snd \<circ> (i_zip f g) = g"
by (simp add: expand_ilist_eq i_zip_nth)

lemma update_i_zip: "
  (i_zip f g)(n := xy) = i_zip (f(n := fst xy)) (g(n := snd xy))"
by (simp add: expand_ilist_eq i_zip_nth)

lemma i_zip_Cons_Cons: "
  i_zip ([x] \<frown> f) ([y] \<frown> g) = [(x, y)] \<frown> (i_zip f g)"
by (simp add: expand_ilist_eq i_zip_nth i_append_nth)

lemma i_zip_i_append1: "
  i_zip (xs \<frown> f) g = zip xs (g \<Down> length xs) \<frown> (i_zip f (g \<Up> length xs))"
by (simp add: expand_ilist_eq i_zip_nth i_append_nth)

lemma i_zip_i_append2: "
  i_zip f (ys \<frown> g) = zip (f \<Down> length ys) ys \<frown> (i_zip (f \<Up> length ys) g)"
by (simp add: expand_ilist_eq i_zip_nth i_append_nth)

lemma i_zip_append: "
  length xs = length ys \<Longrightarrow>
  i_zip (xs \<frown> f) (ys \<frown> g) = zip xs ys \<frown> (i_zip f g)"
by (simp add: expand_ilist_eq i_zip_nth i_append_nth)

lemma i_zip_range: "range (i_zip f g) = { (f n, g n)| n. True }"
by (fastforce simp: i_zip_nth)

lemma i_zip_update: "
  i_zip (f(n := x)) (g(n := y)) = (i_zip f g)( n := (x, y))"
by (simp add: update_i_zip)

lemma i_zip_const: "i_zip (\<lambda>n. x) (\<lambda>n. y) = (\<lambda>n. (x, y))"
by (simp add: expand_ilist_eq i_zip_nth)


subsubsection \<open>Mapping functions with two arguments to infinite lists\<close>

definition i_map2 :: "
  \<comment> \<open>Function taking two parameters\<close>
  ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow>
  \<comment> \<open>Lists of parameters\<close>
  'a ilist \<Rightarrow> 'b ilist \<Rightarrow>
  'c ilist"
where
  "i_map2 f xs ys \<equiv> \<lambda>n. f (xs n) (ys n)"

lemma i_map2_nth: "(i_map2 f xs ys) n = f (xs n) (ys n)"
by (simp add: i_map2_def)

lemma i_map2_Cons_Cons: "
  i_map2 f ([x] \<frown> xs) ([y] \<frown> ys) =
  [f x y] \<frown> (i_map2 f xs ys)"
by (simp add: fun_eq_iff i_map2_nth i_append_nth_Cons')

lemma i_map2_take_ge: "
  n \<le> n1 \<Longrightarrow>
  i_map2 f xs ys \<Down> n =
  map2 f (xs \<Down> n) (ys \<Down> n1)"
by (simp add: expand_list_eq map2_length i_map2_nth map2_nth)
lemma i_map2_take_take: "
  i_map2 f xs ys \<Down> n =
  map2 f (xs \<Down> n) (ys \<Down> n)"
by (rule i_map2_take_ge[OF le_refl])

lemma i_map2_drop: "
  (i_map2 f xs ys) \<Up> n =
  (i_map2 f (xs \<Up> n) (ys \<Up> n))"
by (simp add: fun_eq_iff i_map2_nth)

lemma i_map2_append_append: "
  length xs1 = length ys1 \<Longrightarrow>
  i_map2 f (xs1 \<frown> xs) (ys1 \<frown> ys) =
  map2 f xs1 ys1 \<frown> i_map2 f xs ys"
by (simp add: fun_eq_iff i_map2_nth i_append_nth map2_length map2_nth)

lemma i_map2_Cons_left: "
  i_map2 f ([x] \<frown> xs) ys =
  [f x (ys 0)] \<frown> i_map2 f xs (ys \<Up> Suc 0)"
by (simp add: fun_eq_iff i_map2_nth i_append_nth_Cons')
lemma i_map2_Cons_right: "
  i_map2 f xs ([y] \<frown> ys) =
  [f (xs 0) y] \<frown> i_map2 f (xs \<Up> Suc 0) ys"
by (simp add: fun_eq_iff i_map2_nth i_append_nth_Cons')


lemma i_map2_append_take_drop_left: "
  i_map2 f (xs1 \<frown> xs) ys =
  map2 f xs1 (ys \<Down> length xs1) \<frown>
  i_map2 f xs (ys \<Up> length xs1)"
by (simp add: fun_eq_iff map2_nth i_map2_nth i_append_nth map2_length)
lemma i_map2_append_take_drop_right: "
  i_map2 f xs (ys1 \<frown> ys) =
  map2 f (xs \<Down> length ys1) ys1 \<frown>
  i_map2 f (xs \<Up> length ys1) ys"
by (simp add: fun_eq_iff map2_nth i_map2_nth i_append_nth map2_length)

lemma i_map2_cong: "
  \<lbrakk> xs1 = xs2; ys1 = ys2;
    \<And>x y. \<lbrakk> x \<in> range xs2; y \<in> range ys2 \<rbrakk> \<Longrightarrow> f x y = g x y \<rbrakk> \<Longrightarrow>
  i_map2 f xs1 ys1 = i_map2 g xs2 ys2"
by (simp add: fun_eq_iff i_map2_nth)

lemma i_map2_eq_conv: "
  (i_map2 f xs ys = i_map2 g xs ys) = (\<forall>i. f (xs i) (ys i) = g (xs i) (ys i))"
by (simp add: fun_eq_iff i_map2_nth)

lemma i_map2_replicate: "i_map2 f (\<lambda>n. x) (\<lambda>n. y)  = (\<lambda>n. f x y)"
by (simp add: fun_eq_iff i_map2_nth)

lemma i_map2_i_zip_conv: "
  i_map2 f xs ys = (\<lambda>(x,y). f x y) \<circ> (i_zip xs ys)"
by (simp add: fun_eq_iff i_map2_nth i_zip_nth)


subsection \<open>Generalised lists as combination of finite and infinite lists\<close>

subsubsection \<open>Basic definitions\<close>

datatype (gset: 'a) glist = FL "'a list" | IL "'a ilist" for map: gmap

definition glength :: "'a glist \<Rightarrow> enat"
where
  "glength a \<equiv> case a of
    FL xs \<Rightarrow> enat (length xs) |
    IL f  \<Rightarrow> \<infinity>"

definition gCons :: "'a \<Rightarrow> 'a glist \<Rightarrow> 'a glist"  (infixr "#\<^sub>g" 65)
where
  "x #\<^sub>g a \<equiv> case a of
    FL xs \<Rightarrow> FL (x # xs) |
    IL g  \<Rightarrow> IL ([x] \<frown> g)"

definition gappend :: "'a glist \<Rightarrow> 'a glist \<Rightarrow> 'a glist"  (infixr "@\<^sub>g" 65)
where
  "gappend a b \<equiv> case a of
    FL xs \<Rightarrow> (case b of FL ys \<Rightarrow> FL (xs @ ys) | IL f \<Rightarrow> IL (xs \<frown> f)) |
    IL f  \<Rightarrow> IL f"

definition gtake :: "enat \<Rightarrow> 'a glist \<Rightarrow> 'a glist"
where
  "gtake n a \<equiv> case n of
    enat m \<Rightarrow> FL (case a of
      FL xs \<Rightarrow> xs \<down> m |
      IL f  \<Rightarrow> f \<Down> m) |
    \<infinity> \<Rightarrow> a"

definition gdrop :: "enat \<Rightarrow> 'a glist \<Rightarrow> 'a glist"
where
  "gdrop n a \<equiv> case n of
    enat m \<Rightarrow> (case a of
      FL xs \<Rightarrow> FL (xs \<up> m) |
      IL f  \<Rightarrow> IL (f \<Up> m)) |
    \<infinity> \<Rightarrow> FL []"

definition gnth :: "'a glist \<Rightarrow> nat \<Rightarrow> 'a"  (infixl "!\<^sub>g" 100)
where
  "a !\<^sub>g n \<equiv> case a of
    FL xs \<Rightarrow> xs ! n |
    IL f  \<Rightarrow> f n"

abbreviation g_take' :: "'a glist \<Rightarrow> enat \<Rightarrow> 'a glist"  (infixl "\<down>\<^sub>g" 100)
  where "a \<down>\<^sub>g n \<equiv> gtake n a"

abbreviation g_drop' :: "'a glist \<Rightarrow> enat \<Rightarrow> 'a glist"  (infixl "\<up>\<^sub>g" 100)
  where "a \<up>\<^sub>g n \<equiv> gdrop n a"


subsubsection \<open>\<open>glength\<close>\<close>

lemma glength_fin[simp]: "glength (FL xs) = enat (length xs)"
by (simp add: glength_def)

lemma glength_infin[simp]: "glength (IL f) = \<infinity>"
by (simp add: glength_def)

lemma gappend_glength[simp]: "glength (a @\<^sub>g b) = glength a + glength b"
by (unfold gappend_def, case_tac a, case_tac b, simp+)

lemma gmap_glength[simp]: "glength (gmap f a) = glength a"
by (case_tac a, simp+)

lemma glength_0_conv[simp]: "(glength a = 0) = (a = FL [])"
by (unfold glength_def, case_tac a, simp+)

lemma glength_greater_0_conv[simp]: "(0 < glength a) = (a \<noteq> FL [])"
by (simp add: glength_0_conv[symmetric])

lemma glength_gSuc_conv: "
  (glength a = eSuc n) =
  (\<exists>x b. a = x #\<^sub>g b \<and> glength b = n)"
apply (unfold glength_def gCons_def, rule iffI)
 apply (case_tac a, rename_tac a')
  apply (case_tac n, rename_tac n')
   apply (rule_tac x="hd a'" in exI)
   apply (rule_tac x="FL (tl a')" in exI)
   apply (simp add: eSuc_enat)
   apply (subgoal_tac "a' \<noteq> []")
    prefer 2
    apply (rule ccontr, simp)
   apply simp
  apply simp
 apply (rename_tac f)
 apply (case_tac n, simp add: eSuc_enat)
 apply (rule_tac x="f 0" in exI)
 apply (rule_tac x="IL (f \<Up> Suc 0)" in exI)
 apply (simp add: i_take_first[symmetric])
apply (clarsimp, rename_tac x b)
apply (case_tac a)
 apply (case_tac b)
  apply (simp add: eSuc_enat)+
apply (case_tac b)
apply (simp add: eSuc_enat)+
done

lemma gSuc_glength_conv: "
  (eSuc n = glength a) =
  (\<exists>x b. a = x #\<^sub>g b \<and> glength b = n)"
by (simp add: eq_commute[of _ "glength a"] glength_gSuc_conv)



subsubsection \<open>\<open>@\<close>\ensuremath{{}_g} -- gappend\<close>

lemma gappend_Nil[simp]: "(FL []) @\<^sub>g a = a"
by (unfold gappend_def, case_tac a, simp+)

lemma gappend_Nil2[simp]: "a @\<^sub>g (FL [])= a"
by (unfold gappend_def, case_tac a, simp+)

lemma gappend_is_Nil_conv[simp]: "(a @\<^sub>g b = FL []) = (a = FL [] \<and> b = FL [])"
by (unfold gappend_def, case_tac a, case_tac b, simp+)

lemma Nil_is_gappend_conv[simp]: "(FL [] = a @\<^sub>g b) = (a = FL [] \<and> b = FL [])"
by (simp add: eq_commute[of "FL []"])

lemma gappend_assoc[simp]: "(a @\<^sub>g b) @\<^sub>g c = a @\<^sub>g b @\<^sub>g c"
by (unfold gappend_def, case_tac a, case_tac b, case_tac c, simp+)

lemma gappend_infin[simp]: "IL f @\<^sub>g b = IL f"
by (simp add: gappend_def)

lemma same_gappend_eq_disj[simp]: "(a @\<^sub>g b = a @\<^sub>g c) = (glength a = \<infinity> \<or> b = c)"
apply (case_tac a)
 apply simp
 apply (case_tac b, case_tac c)
 apply (simp add: gappend_def)+
 apply (case_tac c)
 apply simp+
done
lemma same_gappend_eq: "
  glength a < \<infinity> \<Longrightarrow> (a @\<^sub>g b = a @\<^sub>g c) = (b = c)"
by fastforce


subsubsection \<open>\<open>gmap\<close>\<close>

lemma gmap_gappend[simp]: "gmap f (a @\<^sub>g b) = gmap f a @\<^sub>g gmap f b"
by (unfold gappend_def, induct a, induct b, simp+)

lemmas gmap_gmap[simp] = glist.map_comp

lemma gmap_eq_conv[simp]: "(gmap f a = gmap g a) = (\<forall>x\<in>gset a. f x = g x)"
apply (case_tac a)
apply (simp add: o_eq_conv)+
done

lemmas gmap_cong = glist.map_cong

lemma gmap_is_Nil_conv: "(gmap f a = FL []) = (a = FL [])"
by (simp add: glength_0_conv[symmetric])

lemma gmap_eq_imp_glength_eq: "
  gmap f a = gmap f b \<Longrightarrow> glength a = glength b"
by (drule arg_cong[where f=glength], simp)


subsubsection \<open>\<open>gset\<close>\<close>

lemma gset_gappend[simp]: "
  gset (a @\<^sub>g b) =
  (case a of FL a' \<Rightarrow> set a' \<union> gset b | IL a'  \<Rightarrow> range a')"
by (unfold gappend_def, case_tac a, case_tac b, simp+)

lemma gset_gappend_if: "
  gset (a @\<^sub>g b) =
  (if glength a < \<infinity> then gset a \<union> gset b else gset a)"
by (unfold gappend_def, case_tac a, case_tac b, simp+)

lemma gset_empty[simp]: "(gset a = {}) = (a = FL [])"
by (case_tac a, simp+)

lemmas gset_gmap[simp] = glist.set_map

lemma icard_glength: "icard (gset a) \<le> glength a"
apply (unfold icard_def glength_def)
apply (case_tac a)
apply (simp add: card_length)+
done


subsubsection \<open>\<open>!\<close>\ensuremath{{}_g} -- gnth\<close>

lemma gnth_gCons_0[simp]: "(x #\<^sub>g a) !\<^sub>g 0 = x"
by (unfold gCons_def gnth_def, case_tac a, simp+)

lemma gnth_gCons_Suc[simp]: "(x #\<^sub>g a) !\<^sub>g Suc n = a !\<^sub>g n"
by (unfold gCons_def gnth_def, case_tac a, simp+)

lemma gnth_gappend: "
  (a @\<^sub>g b) !\<^sub>g n =
  (if enat n < glength a then a !\<^sub>g n
  else b !\<^sub>g (n - the_enat (glength a)))"
apply (unfold glength_def gappend_def gCons_def gnth_def)
apply (case_tac a, case_tac b)
apply (simp add: nth_append)+
done

lemma gnth_gappend_length_plus[simp]: "(FL xs @\<^sub>g b) !\<^sub>g (length xs + n) = b !\<^sub>g n"
by (simp add: gnth_gappend)

lemma gmap_gnth[simp]: "enat n < glength a \<Longrightarrow> gmap f a !\<^sub>g n = f (a !\<^sub>g n)"
by (unfold gnth_def, case_tac a, simp+)

lemma in_gset_cong_gnth: "(x \<in> gset a) = (\<exists>i. enat i < glength a \<and> a !\<^sub>g i = x)"
apply (unfold gnth_def, case_tac a)
apply (fastforce simp: in_set_conv_nth)+
done


subsubsection \<open>\<open>gtake\<close> and \<open>gdrop\<close>\<close>

lemma gtake_0[simp]: "a \<down>\<^sub>g 0 = FL []"
by (unfold gtake_def, case_tac a, simp+)

lemma gdrop_0[simp]: "a \<up>\<^sub>g 0 = a"
by (unfold gdrop_def, case_tac a, simp+)

lemma gtake_Infty[simp]: "a \<down>\<^sub>g \<infinity> = a"
by (unfold gtake_def, case_tac a, simp+)

lemma gdrop_Infty[simp]: "a \<up>\<^sub>g \<infinity> = FL []"
by (unfold gdrop_def, case_tac a, simp+)

lemma gtake_all[simp]: "glength a \<le> n \<Longrightarrow> a \<down>\<^sub>g n = a"
by (unfold gtake_def, case_tac a, case_tac n, simp+)

lemma gdrop_all[simp]: "glength a \<le> n \<Longrightarrow> a \<up>\<^sub>g n = FL []"
by (unfold gdrop_def, case_tac a, case_tac n, simp+)

lemma gtake_eSuc_gCons[simp]: "(x #\<^sub>g a) \<down>\<^sub>g (eSuc n) = x #\<^sub>g a \<down>\<^sub>g n"
by (unfold gtake_def gCons_def, case_tac n, case_tac a, simp_all add: eSuc_enat)

lemma gdrop_eSuc_gCons[simp]: "(x #\<^sub>g a) \<up>\<^sub>g (eSuc n) = a \<up>\<^sub>g n"
by (unfold gdrop_def gCons_def, case_tac n, case_tac a, simp_all add: eSuc_enat)

lemma gtake_eSuc: "a \<noteq> FL [] \<Longrightarrow> a \<down>\<^sub>g (eSuc n) = a !\<^sub>g 0 #\<^sub>g (a \<up>\<^sub>g (eSuc 0) \<down>\<^sub>g n)"
apply (unfold gtake_def gdrop_def gnth_def gCons_def)
apply (case_tac n)
 apply (case_tac a)
 apply (simp add: eSuc_enat take_Suc hd_eq_first take_drop i_take_Suc)+
apply (case_tac a)
apply (simp add: hd_eq_first drop_eq_tl i_drop_Suc_conv_tl)+
done

lemma gdrop_eSuc: "a \<up>\<^sub>g (eSuc n) = a \<up>\<^sub>g (eSuc 0) \<up>\<^sub>g n"
by (unfold gtake_def gdrop_def gnth_def gCons_def, case_tac n, case_tac a, simp_all add: eSuc_enat)

lemma gnth_via_grop: "a \<up>\<^sub>g (enat n) = x #\<^sub>g b \<Longrightarrow> a !\<^sub>g n = x"
apply (unfold gdrop_def gnth_def gCons_def)
apply (case_tac a, case_tac b)
apply (simp add: nth_via_drop)+
apply (case_tac b)
apply (fastforce intro: nth_via_i_drop)+
done

lemma gtake_eSuc_conv_gapp_gnth: "
  enat n < glength a \<Longrightarrow> a \<down>\<^sub>g enat (Suc n) = a \<down>\<^sub>g (enat n) @\<^sub>g FL [a !\<^sub>g n]"
apply (unfold glength_def gtake_def gappend_def gnth_def)
apply (case_tac a)
apply (simp add: take_Suc_conv_app_nth i_take_Suc_conv_app_nth)+
done

lemma gdrop_eSuc_conv_tl: "
  enat n < glength a \<Longrightarrow> a !\<^sub>g n #\<^sub>g a \<up>\<^sub>g enat (Suc n) = a \<up>\<^sub>g enat n"
apply (unfold glength_def gdrop_def gappend_def gnth_def gCons_def)
apply (case_tac a)
apply (simp add: Cons_nth_drop_Suc i_drop_Suc_conv_tl)+
done

lemma glength_gtake[simp]: "glength (a \<down>\<^sub>g n) = min (glength a) n"
by (unfold glength_def gtake_def, case_tac n, case_tac a, simp+)

lemma glength_drop[simp]: "glength (a \<up>\<^sub>g (enat n)) = glength a - (enat n)"
by (unfold glength_def gdrop_def, case_tac a, case_tac n, simp+)

end
