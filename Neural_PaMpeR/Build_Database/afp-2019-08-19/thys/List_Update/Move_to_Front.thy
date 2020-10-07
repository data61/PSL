(* Author: Tobias Nipkow *)

section "Deterministic List Update"

theory Move_to_Front
imports
  Swaps
  On_Off
  Competitive_Analysis
begin

declare Let_def[simp]

subsection "Function \<open>mtf\<close>"

definition mtf :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"mtf x xs =
 (if x \<in> set xs then x # (take (index xs x) xs) @ drop (index xs x + 1) xs
  else xs)"

lemma mtf_id[simp]: "x \<notin> set xs \<Longrightarrow> mtf x xs = xs"
by(simp add: mtf_def)

lemma mtf0[simp]: "x \<in> set xs \<Longrightarrow> mtf x xs ! 0 = x"
by(auto simp: mtf_def)

lemma before_in_mtf: assumes "z \<in> set xs"
shows "x < y in mtf z xs  \<longleftrightarrow>
      (y \<noteq> z \<and> (if x=z then y \<in> set xs else x < y in xs))"
proof-
  have 0: "index xs z < size xs" by (metis assms index_less_size_conv)
  let ?xs = "take (index xs z) xs @ xs ! index xs z # drop (Suc (index xs z)) xs"
  have "x < y in mtf z xs = (y \<noteq> z \<and> (if x=z then y \<in> set ?xs else x < y in ?xs))"
    using assms
    by(auto simp add: mtf_def before_in_def index_append)
      (metis add_lessD1 index_less_size_conv length_take less_Suc_eq not_less_eq)
  with id_take_nth_drop[OF 0, symmetric] show ?thesis by(simp)
qed

lemma Inv_mtf: "set xs = set ys \<Longrightarrow> z : set ys \<Longrightarrow> Inv xs (mtf z ys) =
 Inv xs ys \<union> {(x,z)|x. x < z in xs \<and> x < z in ys}
 - {(z,x)|x. z < x in xs \<and> x < z in ys}"
by(auto simp add: Inv_def before_in_mtf not_before_in dest: before_in_setD1)

lemma set_mtf[simp]: "set(mtf x xs) = set xs"
by(simp add: mtf_def)
  (metis append_take_drop_id Cons_nth_drop_Suc index_less le_refl Un_insert_right nth_index set_append set_simps(2))

lemma length_mtf[simp]: "size (mtf x xs) = size xs"
by (auto simp add: mtf_def min_def) (metis index_less_size_conv leD)

lemma distinct_mtf[simp]: "distinct (mtf x xs) = distinct xs"
by (metis length_mtf set_mtf card_distinct distinct_card)


subsection "Function \<open>mtf2\<close>"

definition mtf2 :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"mtf2 n x xs =
 (if x : set xs then swaps [index xs x - n..<index xs x] xs else xs)"

lemma mtf_eq_mtf2: "mtf x xs = mtf2 (length xs - 1) x xs"
proof -
  have "x : set xs \<Longrightarrow> index xs x - (size xs - Suc 0) = 0"
    by (auto simp: less_Suc_eq_le[symmetric])
  thus ?thesis
    by(auto simp: mtf_def mtf2_def swaps_eq_nth_take_drop)
qed

lemma mtf20[simp]: "mtf2 0 x xs = xs"
by(auto simp add: mtf2_def)

lemma length_mtf2[simp]: "length (mtf2 n x xs) = length xs"
by (auto simp: mtf2_def index_less_size_conv[symmetric]
  simp del:index_conv_size_if_notin)

lemma set_mtf2[simp]: "set(mtf2 n x xs) = set xs"
by (auto simp: mtf2_def index_less_size_conv[symmetric]
  simp del:index_conv_size_if_notin)

lemma distinct_mtf2[simp]: "distinct (mtf2 n x xs) = distinct xs"
by (metis length_mtf2 set_mtf2 card_distinct distinct_card)

lemma card_Inv_mtf2: "xs!j = ys!0 \<Longrightarrow> j < length xs \<Longrightarrow> dist_perm xs ys \<Longrightarrow>
   card (Inv (swaps [i..<j] xs) ys) = card (Inv xs ys) - int(j-i)"
proof(induction j arbitrary: xs)
  case (Suc j)
  show ?case
  proof cases
    assume "i > j" thus ?thesis by simp
  next
    assume [arith]: "\<not> i > j"
    have 0: "Suc j < length ys" by (metis Suc.prems(2,3) distinct_card)
    have 1: "(ys ! 0, xs ! j) : Inv ys xs"
    proof (auto simp: Inv_def)
      show "ys ! 0 < xs ! j in ys" using Suc.prems
        by (metis Suc_lessD n_not_Suc_n not_before0 not_before_in nth_eq_iff_index_eq nth_mem)
      show "xs ! j < ys ! 0 in xs" using Suc.prems
        by (metis Suc_lessD before_id lessI)
    qed
    have 2: "card(Inv ys xs) \<noteq> 0" using 1 by auto
    have "int(card (Inv (swaps [i..<Suc j] xs) ys)) =
          card (Inv (swap j xs) ys) - int (j-i)" using Suc by simp
    also have "\<dots> = card (Inv ys (swap j xs)) - int (j-i)"
      by(simp add: card_Inv_sym)
    also have "\<dots> = card (Inv ys xs - {(ys ! 0, xs ! j)}) - int (j - i)"
      using Suc.prems 0 by(simp add: Inv_swap)
    also have "\<dots> = int(card (Inv ys xs) - 1) - (j - i)"
      using 1 by(simp add: card_Diff_singleton)
    also have "\<dots> = card (Inv ys xs) - int (Suc j - i)" using 2 by arith
    also have "\<dots> = card (Inv xs ys) - int (Suc j - i)" by(simp add: card_Inv_sym)
    finally show ?thesis .
  qed
qed simp





subsection "Function Lxy"


definition Lxy :: "'a list \<Rightarrow> 'a set \<Rightarrow> 'a list" where
  "Lxy xs S = filter (\<lambda>z. z\<in>S) xs" 
thm inter_set_filter

lemma Lxy_length_cons: "length (Lxy xs S) \<le> length (Lxy (x#xs) S)"
unfolding Lxy_def by(simp)

lemma Lxy_empty[simp]: "Lxy [] S = []"
unfolding Lxy_def by simp

lemma Lxy_set_filter: "set (Lxy xs S) = S \<inter> set xs" 
by (simp add: Lxy_def inter_set_filter)

lemma Lxy_distinct: "distinct xs \<Longrightarrow> distinct (Lxy xs S)"
by (simp add: Lxy_def)

lemma Lxy_append: "Lxy (xs@ys) S = Lxy xs S @ Lxy ys S"
by(simp add: Lxy_def)

lemma Lxy_snoc: "Lxy (xs@[x]) S = (if x\<in>S then Lxy xs S @ [x] else Lxy xs S)"
by(simp add: Lxy_def)

lemma Lxy_not: "S \<inter> set xs = {} \<Longrightarrow> Lxy xs S = []"
unfolding Lxy_def apply(induct xs) by simp_all



lemma Lxy_notin: "set xs \<inter> S = {} \<Longrightarrow> Lxy xs S = []"
apply(induct xs) by(simp_all add: Lxy_def)

lemma Lxy_in: "x\<in>S \<Longrightarrow> Lxy [x] S = [x]"
by(simp add: Lxy_def)



lemma Lxy_project: 
  assumes "x\<noteq>y" "x \<in> set xs"  "y\<in>set xs" "distinct xs" 
    and "x < y in xs"
  shows "Lxy xs {x,y} = [x,y]"
proof -
  from assms have ij: "index xs x < index xs y"
        and xinxs: "index xs x < length xs"
        and yinxs: "index xs y < length xs" unfolding before_in_def by auto  
  from xinxs obtain a as where dec1: "a @ [xs!index xs x] @ as = xs"
        and "a = take (index xs x) xs" and "as = drop (Suc (index xs x)) xs"
        and length_a: "length a = index xs x" and length_as: "length as = length xs - index xs x- 1"
        using id_take_nth_drop by fastforce 
  have "index xs y\<ge>length (a @ [xs!index xs x])" using length_a ij by auto
  then have "((a @ [xs!index xs x]) @ as) ! index xs y = as ! (index xs y-length (a @ [xs ! index xs x]))" using nth_append[where xs="a @ [xs!index xs x]" and ys="as"]
    by(simp)
  then have xsj: "xs ! index xs y = as ! (index xs y-index xs x-1)" using dec1 length_a by auto   
  have las: "(index xs y-index xs x-1) < length as" using length_as yinxs ij by simp
  obtain b c where dec2: "b @ [xs!index xs y] @ c = as"
            and "b = take (index xs y-index xs x-1) as" "c=drop (Suc (index xs y-index xs x-1)) as"
            and length_b: "length b = index xs y-index xs x-1" using id_take_nth_drop[OF las] xsj by force
  have xs_dec: "a @ [xs!index xs x] @ b @ [xs!index xs y] @ c = xs" using dec1 dec2 by auto 
   
  from xs_dec assms(4) have "distinct ((a @ [xs!index xs x] @ b @ [xs!index xs y]) @ c)" by simp
  then have c_empty: "set c \<inter> {x,y} = {}"
      and b_empty: "set b \<inter> {x,y} = {}"and a_empty: "set a \<inter> {x,y} = {}" by(auto simp add: assms(2,3))

  have "Lxy (a @ [xs!index xs x] @ b @ [xs!index xs y] @ c) {x,y} = [x,y]"
    apply(simp only: Lxy_append)
    apply(simp add: assms(2,3))
    using a_empty b_empty c_empty by(simp add: Lxy_notin Lxy_in)

  with xs_dec show ?thesis by auto
qed


lemma Lxy_mono: "{x,y} \<subseteq> set xs \<Longrightarrow> distinct xs \<Longrightarrow> x < y in xs = x < y in Lxy xs {x,y}"
apply(cases "x=y")
  apply(simp add: before_in_irefl)
proof -
  assume xyset: "{x,y} \<subseteq> set xs"
  assume dxs: "distinct xs"
  assume xy: "x\<noteq>y" 
  {
    fix x y
    assume 1: "{x,y} \<subseteq> set xs" 
    assume xny: "x\<noteq>y"
    assume 3: "x < y in xs" 
    have "Lxy xs {x,y} = [x,y]" apply(rule Lxy_project) 
          using xny 1 3 dxs by(auto)
    then have "x < y in Lxy xs {x,y}" using xny by(simp add: before_in_def)
  } note aha=this
  have a: "x < y in xs \<Longrightarrow> x < y in Lxy xs {x,y}"
    apply(subst Lxy_project) 
      using xy xyset dxs by(simp_all add: before_in_def)
  have t: "{x,y}={y,x}" by(auto)
  have f: "~ x < y in xs \<Longrightarrow> y < x in Lxy xs {x,y}"
    unfolding t
    apply(rule aha)
      using xyset apply(simp)
      using xy apply(simp)
      using xy xyset by(simp add: not_before_in)
  have b: "~ x < y in xs \<Longrightarrow> ~ x < y in Lxy xs {x,y}"
  proof -
    assume "~ x < y in xs"
    then have "y < x in Lxy xs {x,y}" using f by auto
    then have "~ x < y in Lxy xs {x,y}" using xy by(simp add: not_before_in)
    then show ?thesis .
  qed
  from a b
  show ?thesis by metis
qed


subsection "List Update as Online/Offline Algorithm"

type_synonym 'a state = "'a list"
type_synonym answer = "nat * nat list"

definition step :: "'a state \<Rightarrow> 'a \<Rightarrow> answer \<Rightarrow> 'a state" where
"step s r a =
  (let (k,sws) = a in mtf2 k r (swaps sws s))"

definition t :: "'a state \<Rightarrow> 'a \<Rightarrow> answer \<Rightarrow> nat" where
"t s r a = (let (mf,sws) = a in index (swaps sws s) r + 1 + size sws)"

definition static where "static s rs = (set rs \<subseteq> set s)"

interpretation On_Off step t static .

type_synonym 'a alg_off = "'a state \<Rightarrow> 'a list \<Rightarrow> answer list"
type_synonym ('a,'is) alg_on = "('a state,'is,'a,answer) alg_on"

lemma T_ge_len: "length as = length rs \<Longrightarrow> T s rs as \<ge> length rs"
by(induction arbitrary: s rule: list_induct2)
  (auto simp: t_def trans_le_add2)

lemma T_off_neq0: "(\<And>rs s0. size(alg s0 rs) = length rs) \<Longrightarrow>
  rs \<noteq> [] \<Longrightarrow> T_off alg s0 rs \<noteq> 0"
apply(erule_tac x=rs in meta_allE)
apply(erule_tac x=s0 in meta_allE)
apply (auto simp: neq_Nil_conv length_Suc_conv t_def)
done

lemma length_step[simp]: "length (step s r as) = length s"
by(simp add: step_def split_def)

lemma step_Nil_iff[simp]: "step xs r act = [] \<longleftrightarrow> xs = []"
by(auto simp add: step_def mtf2_def split: prod.splits)

lemma set_step2: "set(step s r (mf,sws)) = set s"
by(auto simp add: step_def)

lemma set_step: "set(step s r act) = set s"
by(cases act)(simp add: set_step2)

lemma distinct_step: "distinct(step s r as) = distinct s"
by (auto simp: step_def split_def)


subsection "Online Algorithm Move-to-Front is 2-Competitive"

definition MTF :: "('a,unit) alg_on" where
"MTF = (\<lambda>_. (), \<lambda>s r. ((size (fst s) - 1,[]), ()))"

text\<open>It was first proved by Sleator and Tarjan~\cite{SleatorT-CACM85} that
the Move-to-Front algorithm is 2-competitive.\<close>

(* The core idea with upper bounds: *)
lemma potential:
fixes t :: "nat \<Rightarrow> 'a::linordered_ab_group_add" and p :: "nat \<Rightarrow> 'a"
assumes p0: "p 0 = 0" and ppos: "\<And>n. p n \<ge> 0"
and ub: "\<And>n. t n + p(n+1) - p n \<le> u n"
shows "(\<Sum>i<n. t i) \<le> (\<Sum>i<n. u i)"
proof-
  let ?a = "\<lambda>n. t n + p(n+1) - p n"
  have 1: "(\<Sum>i<n. t i) = (\<Sum>i<n. ?a i) - p(n)"
    by(induction n) (simp_all add: p0)
  thus ?thesis
    by (metis (erased, lifting) add.commute diff_add_cancel le_add_same_cancel2 order.trans ppos sum_mono ub)
qed

lemma potential2:
fixes t :: "nat \<Rightarrow> 'a::linordered_ab_group_add" and p :: "nat \<Rightarrow> 'a"
assumes p0: "p 0 = 0" and ppos: "\<And>n. p n \<ge> 0"
and ub: "\<And>m. m<n \<Longrightarrow> t m + p(m+1) - p m \<le> u m"
shows "(\<Sum>i<n. t i) \<le> (\<Sum>i<n. u i)"
proof-
  let ?a = "\<lambda>n. t n + p(n+1) - p n"
  have "(\<Sum>i<n. t i) = (\<Sum>i<n. ?a i) - p(n)" by(induction n) (simp_all add: p0)
  also have      "\<dots> \<le> (\<Sum>i<n. ?a i)" using ppos by auto
  also have      "\<dots> \<le> (\<Sum>i<n. u i)" apply(rule sum_mono) apply(rule ub) by auto
  finally show ?thesis .
qed


abbreviation "before x xs \<equiv> {y. y < x in xs}"
abbreviation "after x xs \<equiv> {y. x < y in xs}"

lemma finite_before[simp]: "finite (before x xs)"
apply(rule finite_subset[where B = "set xs"])
apply (auto dest: before_in_setD1)
done

lemma finite_after[simp]: "finite (after x xs)"
apply(rule finite_subset[where B = "set xs"])
apply (auto dest: before_in_setD2)
done

lemma before_conv_take:
  "x : set xs \<Longrightarrow> before x xs = set(take (index xs x) xs)"
by (auto simp add: before_in_def set_take_if_index index_le_size) (metis index_take leI)

lemma card_before: "distinct xs \<Longrightarrow> x : set xs \<Longrightarrow> card (before x xs) = index xs x"
using  index_le_size[of xs x]
by(simp add: before_conv_take distinct_card[OF distinct_take] min_def)

lemma before_Un: "set xs = set ys \<Longrightarrow> x : set xs \<Longrightarrow>
  before x ys = before x xs \<inter> before x ys Un after x xs \<inter> before x ys"
by(auto)(metis before_in_setD1 not_before_in)

lemma phi_diff_aux:
  "card (Inv xs ys \<union>
             {(y, x) |y. y < x in xs \<and> y < x in ys} -
             {(x, y) |y. x < y in xs \<and> y < x in ys}) =
   card(Inv xs ys) + card(before x xs \<inter> before x ys)
   - int(card(after x xs \<inter> before x ys))"
  (is "card(?I \<union> ?B - ?A) = card ?I + card ?b - int(card ?a)")
proof-
  have 1: "?I \<inter> ?B = {}" by(auto simp: Inv_def) (metis no_before_inI)
  have 2: "?A \<subseteq> ?I \<union> ?B" by(auto simp: Inv_def)
  have 3: "?A \<subseteq> ?I" by(auto simp: Inv_def)
  have "int(card(?I \<union> ?B - ?A)) = int(card ?I + card ?B) - int(card ?A)"
    using  card_mono[OF _ 3]
    by(simp add: card_Un_disjoint[OF _ _ 1] card_Diff_subset[OF _ 2])
  also have "card ?B = card (fst ` ?B)" by(auto simp: card_image inj_on_def)
  also have "fst ` ?B = ?b" by force
  also have "card ?A = card (snd ` ?A)" by(auto simp: card_image inj_on_def)
  also have "snd ` ?A = ?a" by force
  finally show ?thesis .
qed

lemma not_before_Cons[simp]: "\<not> x < y in y # xs"
by (simp add: before_in_def)

lemma before_Cons[simp]:
  "y \<in> set xs \<Longrightarrow> y \<noteq> x \<Longrightarrow> before y (x#xs) = insert x (before y xs)"
by(auto simp: before_in_def)

lemma card_before_le_index: "card (before x xs) \<le> index xs x"
apply(cases "x \<in> set xs")
 prefer 2 apply (simp add: before_in_def)
apply(induction xs)
 apply (simp add: before_in_def)
apply (auto simp: card_insert_if)
done

lemma config_config_length: "length (fst (config A init qs)) = length init"
apply (induct rule: config_induct) by (simp_all)

lemma config_config_distinct: 
  shows " distinct (fst (config A init qs)) = distinct init" 
apply (induct rule: config_induct) by (simp_all add: distinct_step)

lemma config_config_set: 
  shows "set (fst (config A init qs)) = set init"
apply(induct rule: config_induct) by(simp_all add: set_step)

lemma config_config:
  "set (fst (config A init qs)) = set init
        \<and> distinct (fst (config A init qs)) = distinct init
        \<and> length (fst (config A init qs)) = length init"
using config_config_distinct config_config_set config_config_length by metis

lemma config_dist_perm:
  "distinct init \<Longrightarrow> dist_perm (fst (config A init qs)) init"
using config_config_distinct config_config_set by metis
 


lemma config_rand_length: "\<forall>x\<in>set_pmf (config_rand  A init qs). length (fst x) = length init"
apply (induct rule: config_rand_induct) by (simp_all)

lemma config_rand_distinct: 
  shows "\<forall>x \<in> (config_rand  A init qs). distinct (fst x) = distinct init" 
apply (induct rule: config_rand_induct) by (simp_all add: distinct_step)

lemma config_rand_set: 
  shows " \<forall>x \<in> (config_rand   A init qs). set (fst x) = set init"
apply(induct rule: config_rand_induct) by(simp_all add: set_step)

lemma config_rand:
  "\<forall>x \<in> (config_rand   A  init qs). set (fst x) = set init
        \<and> distinct (fst x) = distinct init \<and> length (fst x) = length init"
using config_rand_distinct config_rand_set config_rand_length by metis

lemma config_rand_dist_perm:
  "distinct init \<Longrightarrow> \<forall>x \<in> (config_rand A init qs). dist_perm (fst x) init"
using config_rand_distinct config_rand_set  by metis




(*fixme start from Inv*)

lemma amor_mtf_ub: assumes "x : set ys" "set xs = set ys"
shows "int(card(before x xs Int before x ys)) - card(after x xs Int before x ys)
  \<le> 2 * int(index xs x) - card (before x ys)" (is "?m - ?n \<le> 2 * ?j - ?k")
proof-
  have xxs: "x \<in> set xs" using assms(1,2) by simp
  let ?bxxs = "before x xs" let ?bxys = "before x ys" let ?axxs = "after x xs"
  have 0: "?bxxs \<inter> ?axxs = {}" by (auto simp: before_in_def)
  hence 1: "(?bxxs \<inter> ?bxys) \<inter> (?axxs \<inter> ?bxys) = {}" by blast
  have "(?bxxs \<inter> ?bxys) \<union> (?axxs \<inter> ?bxys) = ?bxys"
    using assms(2) before_Un xxs by fastforce
  hence "?m + ?n = ?k"
    using card_Un_disjoint[OF _ _ 1] by simp
  hence "?m - ?n = 2 * ?m - ?k" by arith
  also have "?m \<le> ?j"
    using card_before_le_index[of x xs] card_mono[of ?bxxs, OF _ Int_lower1]
    by(auto intro: order_trans)
  finally show ?thesis by auto
qed

locale MTF_Off =
fixes as :: "answer list"
fixes rs :: "'a list"
fixes s0 :: "'a list"
assumes dist_s0[simp]: "distinct s0"
assumes len_as: "length as = length rs"
begin

definition mtf_A :: "nat list" where
"mtf_A = map fst as"

definition sw_A :: "nat list list" where
"sw_A = map snd as"

fun s_A :: "nat \<Rightarrow> 'a list" where
"s_A 0 = s0" |
"s_A(Suc n) = step (s_A n) (rs!n) (mtf_A!n, sw_A!n)"

lemma length_s_A[simp]: "length(s_A n) = length s0"
by (induction n) simp_all

lemma dist_s_A[simp]: "distinct(s_A n)" 
by(induction n) (simp_all add: step_def)

lemma set_s_A[simp]: "set(s_A n) = set s0"
by(induction n) (simp_all add: step_def)


fun s_mtf :: "nat \<Rightarrow> 'a list" where
"s_mtf 0 = s0" |
"s_mtf (Suc n) = mtf (rs!n) (s_mtf n)"

definition t_mtf :: "nat \<Rightarrow> int" where
"t_mtf n = index (s_mtf n) (rs!n) + 1"

definition T_mtf :: "nat \<Rightarrow> int" where
"T_mtf n = (\<Sum>i<n. t_mtf i)"

definition c_A :: "nat \<Rightarrow> int" where
"c_A n = index (swaps (sw_A!n) (s_A n)) (rs!n) + 1"

definition f_A :: "nat \<Rightarrow> int" where
"f_A n = min (mtf_A!n) (index (swaps (sw_A!n) (s_A n)) (rs!n))"

definition p_A :: "nat \<Rightarrow> int" where
"p_A n = size(sw_A!n)"

definition t_A :: "nat \<Rightarrow> int" where
"t_A n = c_A n + p_A n"

definition T_A :: "nat \<Rightarrow> int" where
"T_A n = (\<Sum>i<n. t_A i)"

lemma length_s_mtf[simp]: "length(s_mtf n) = length s0"
by (induction n) simp_all

lemma dist_s_mtf[simp]: "distinct(s_mtf n)"
apply(induction n)
 apply (simp)
apply (auto simp: mtf_def index_take set_drop_if_index)
apply (metis set_drop_if_index index_take less_Suc_eq_le linear)
done

lemma set_s_mtf[simp]: "set (s_mtf n) = set s0"
by (induction n) (simp_all)

lemma dperm_inv: "dist_perm (s_A n) (s_mtf n)"
by (metis dist_s_mtf dist_s_A set_s_mtf set_s_A)

definition Phi :: "nat \<Rightarrow> int" ("\<Phi>") where
"Phi n = card(Inv (s_A n) (s_mtf n))"

lemma phi0: "Phi 0 = 0"
by(simp add: Phi_def)

lemma phi_pos: "Phi n \<ge> 0"
by(simp add: Phi_def)

lemma mtf_ub: "t_mtf n + Phi (n+1) - Phi n \<le> 2 * c_A n - 1 + p_A n - f_A n"
proof -
  let ?xs = "s_A n" let ?ys = "s_mtf n" let ?x = "rs!n"
  let ?xs' = "swaps (sw_A!n) ?xs" let ?ys' = "mtf ?x ?ys"
  show ?thesis
  proof cases
  assume xin: "?x \<in> set ?ys"
  let ?bb = "before ?x ?xs \<inter> before ?x ?ys"
  let ?ab = "after ?x ?xs \<inter> before ?x ?ys"
  have phi_mtf:
    "card(Inv ?xs' ?ys') - int(card (Inv ?xs' ?ys))
   \<le> 2 * int(index ?xs' ?x) - int(card (before ?x ?ys))"
      using xin by(simp add: Inv_mtf phi_diff_aux amor_mtf_ub)
  have phi_sw: "card(Inv ?xs' ?ys) \<le> Phi n + length(sw_A!n)"
  proof -
    have "int(card (Inv ?xs' ?ys)) \<le> card(Inv ?xs' ?xs) + int(card(Inv ?xs ?ys))"
      using card_Inv_tri_ineq[of ?xs' ?xs ?ys] xin by (simp)
    also have "card(Inv ?xs' ?xs) = card(Inv ?xs ?xs')"
      by (rule card_Inv_sym)
    also have "card(Inv ?xs ?xs') \<le> size(sw_A!n)"
      by (metis card_Inv_swaps_le dist_s_A)
    finally show ?thesis by(fastforce simp: Phi_def)
  qed
  have phi_free: "card(Inv ?xs' ?ys') - Phi (Suc n) = f_A n" using xin
    by(simp add: Phi_def mtf2_def step_def card_Inv_mtf2 index_less_size_conv f_A_def)
  show ?thesis using xin phi_sw phi_mtf phi_free card_before[of "s_mtf n"]
    by(simp add: t_mtf_def c_A_def p_A_def)
  next
    assume notin: "?x \<notin> set ?ys"
    have "int (card (Inv ?xs' ?ys)) - card (Inv ?xs ?ys) \<le> card(Inv ?xs ?xs')"
      using card_Inv_tri_ineq[OF _ dperm_inv, of ?xs' n]
            swaps_inv[of "sw_A!n" "s_A n"]
      by(simp add: card_Inv_sym)
    also have "\<dots> \<le> size(sw_A!n)"
      by(simp add: card_Inv_swaps_le dperm_inv)
    finally show ?thesis using notin
      by(simp add: t_mtf_def step_def c_A_def p_A_def f_A_def Phi_def mtf2_def)
  qed
qed

theorem Sleator_Tarjan: "T_mtf n \<le> (\<Sum>i<n. 2*c_A i + p_A i - f_A i) - n"
proof-
  have "(\<Sum>i<n. t_mtf i) \<le> (\<Sum>i<n. 2*c_A i - 1 + p_A i - f_A i)"
    by(rule potential[where p=Phi,OF phi0 phi_pos mtf_ub])
  also have "\<dots> = (\<Sum>i<n. (2*c_A i + p_A i - f_A i) - 1)"
    by (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>i<n. 2*c_A i + p_A i - f_A i) - n"
    by(simp add: sumr_diff_mult_const2[symmetric])
  finally show ?thesis by(simp add: T_mtf_def)
qed

corollary Sleator_Tarjan': "T_mtf n \<le> 2*T_A n - n"
proof -
  have "T_mtf n \<le> (\<Sum>i<n. 2*c_A i + p_A i - f_A i) - n" by (fact Sleator_Tarjan)
  also have "(\<Sum>i<n. 2*c_A i + p_A i - f_A i) \<le> (\<Sum>i<n. 2*(c_A i + p_A i))"
    by(intro sum_mono) (simp add: p_A_def f_A_def)
  also have "\<dots> \<le> 2* T_A n" by (simp add: sum_distrib_left T_A_def t_A_def)
  finally show "T_mtf n \<le> 2* T_A n - n" by auto
qed

lemma T_A_nneg: "0 \<le> T_A n"
by(auto simp add: sum_nonneg T_A_def t_A_def c_A_def p_A_def)

lemma T_mtf_ub: "\<forall>i<n. rs!i \<in> set s0 \<Longrightarrow> T_mtf n \<le> n * size s0"
proof(induction n)
  case 0 show ?case by(simp add: T_mtf_def)
next
  case (Suc n)  thus ?case
    using index_less_size_conv[of "s_mtf n" "rs!n"]
      by(simp add: T_mtf_def t_mtf_def less_Suc_eq del: index_less)
qed

corollary T_mtf_competitive: assumes "s0 \<noteq> []" and "\<forall>i<n. rs!i \<in> set s0"
shows "T_mtf n \<le> (2 - 1/(size s0)) * T_A n"
proof cases
  assume 0: "real_of_int(T_A n) \<le> n * (size s0)"
  have "T_mtf n \<le> 2 * T_A n - n"
  proof -
    have "T_mtf n \<le> (\<Sum>i<n. 2*c_A i + p_A i - f_A i) - n" by(rule Sleator_Tarjan)
    also have "(\<Sum>i<n. 2*c_A i + p_A i - f_A i) \<le> (\<Sum>i<n. 2*(c_A i + p_A i))"
      by(intro sum_mono) (simp add: p_A_def f_A_def)
    also have "\<dots> \<le> 2 * T_A n" by (simp add: sum_distrib_left T_A_def t_A_def)
    finally show ?thesis by simp
  qed
  hence "real_of_int(T_mtf n) \<le> 2 * of_int(T_A n) - n" by simp
  also have "\<dots> = 2 * of_int(T_A n) - (n * size s0) / size s0"
    using assms(1) by simp
  also have "\<dots> \<le> 2 * real_of_int(T_A n) - T_A n / size s0"
    by(rule diff_left_mono[OF divide_right_mono[OF 0]]) simp
  also have "\<dots> = (2 - 1 / size s0) * T_A n" by algebra
  finally show ?thesis .
next
  assume 0: "\<not> real_of_int(T_A n) \<le> n * (size s0)"
  have "2 - 1 / size s0 \<ge> 1" using assms(1)
    by (auto simp add: field_simps neq_Nil_conv)
  have "real_of_int (T_mtf n) \<le> n * size s0" using T_mtf_ub[OF assms(2)] by linarith
  also have "\<dots> < of_int(T_A n)" using 0 by simp
  also have "\<dots> \<le> (2 - 1 / size s0) * T_A n" using assms(1) T_A_nneg[of n]
    by(auto simp add: mult_le_cancel_right1 field_simps neq_Nil_conv)
  finally show ?thesis by linarith
qed

lemma t_A_t: "n < length rs \<Longrightarrow> t_A n = int (t (s_A n) (rs ! n) (as ! n))"
by(simp add: t_A_def t_def c_A_def p_A_def sw_A_def len_as split: prod.split)

lemma T_A_eq_lem: "(\<Sum>i=0..<length rs. t_A i) =
  T (s_A 0) (drop 0 rs) (drop 0 as)"
proof(induction rule: zero_induct[of _ "size rs"])
  case 1 thus ?case by (simp add: len_as)
next
  case (2 n)
  show ?case
  proof cases
    assume "n < length rs"
    thus ?case using 2
    by(simp add: Cons_nth_drop_Suc[symmetric,where i=n] len_as sum.atLeast_Suc_lessThan
      t_A_t mtf_A_def sw_A_def)
  next
    assume "\<not> n < length rs" thus ?case by (simp add: len_as)
  qed
qed

lemma T_A_eq: "T_A (length rs) = T s0 rs as"
using T_A_eq_lem by(simp add: T_A_def atLeast0LessThan)

lemma nth_off_MTF: "n < length rs \<Longrightarrow> off2 MTF s rs ! n = (size(fst s) - 1,[])"
by(induction rs arbitrary: s n)(auto simp add: MTF_def nth_Cons' Step_def)

lemma t_mtf_MTF: "n < length rs \<Longrightarrow>
  t_mtf n = int (t (s_mtf n) (rs ! n) (off MTF s rs ! n))"
by(simp add: t_mtf_def t_def nth_off_MTF split: prod.split)

lemma mtf_MTF: "n < length rs \<Longrightarrow> length s = length s0 \<Longrightarrow> mtf (rs ! n) s =
       step s (rs ! n) (off MTF s0 rs ! n)"
by(auto simp add: nth_off_MTF step_def mtf_eq_mtf2)

lemma T_mtf_eq_lem: "(\<Sum>i=0..<length rs. t_mtf i) =
  T (s_mtf 0) (drop 0 rs) (drop 0 (off MTF s0 rs))"
proof(induction rule: zero_induct[of _ "size rs"])
  case 1 thus ?case by (simp add: len_as)
next
  case (2 n)
  show ?case
  proof cases
    assume "n < length rs"
    thus ?case using 2
      by(simp add: Cons_nth_drop_Suc[symmetric,where i=n] len_as sum.atLeast_Suc_lessThan
        t_mtf_MTF[where s=s0] mtf_A_def sw_A_def mtf_MTF)
  next
    assume "\<not> n < length rs" thus ?case by (simp add: len_as)
  qed
qed

lemma T_mtf_eq: "T_mtf (length rs) = T_on MTF s0 rs"
using T_mtf_eq_lem by(simp add: T_mtf_def atLeast0LessThan)

corollary MTF_competitive2: "s0 \<noteq> [] \<Longrightarrow> \<forall>i<length rs. rs!i \<in> set s0 \<Longrightarrow>
  T_on MTF s0 rs \<le> (2 - 1/(size s0)) * T s0 rs as"
by (metis T_mtf_competitive T_A_eq T_mtf_eq of_int_of_nat_eq)

corollary MTF_competitive': "T_on MTF s0 rs \<le> 2 * T s0 rs as"
using Sleator_Tarjan'[of "length rs"] T_A_eq T_mtf_eq
by auto

end

theorem compet_MTF: assumes "s0 \<noteq> []" "distinct s0" "set rs \<subseteq> set s0"
shows "T_on MTF s0 rs \<le> (2 - 1/(size s0)) * T_opt s0 rs"
proof-
  from assms(3) have 1: "\<forall>i < length rs. rs!i \<in> set s0" by auto
  { fix as :: "answer list" assume len: "length as = length rs"
    interpret MTF_Off as rs s0 proof qed (auto simp: assms(2) len)
    from MTF_competitive2[OF assms(1) 1] assms(1)
    have "T_on MTF s0 rs / (2 - 1 / (length s0)) \<le> of_int(T s0 rs as)"
      by(simp add: field_simps length_greater_0_conv[symmetric]
        del: length_greater_0_conv) }
  hence "T_on MTF s0 rs / (2 - 1/(size s0)) \<le> T_opt s0 rs"
    apply(simp add: T_opt_def Inf_nat_def)
    apply(rule LeastI2_wellorder)
    using length_replicate[of "length rs" undefined] apply fastforce
    apply auto
    done
  thus ?thesis using assms by(simp add: field_simps
    length_greater_0_conv[symmetric] del: length_greater_0_conv)
qed

theorem compet_MTF': assumes "distinct s0"
shows "T_on MTF s0 rs \<le> (2::real) * T_opt s0 rs"
proof- 
  { fix as :: "answer list" assume len: "length as = length rs"
    interpret MTF_Off as rs s0 proof qed (auto simp: assms(1) len)
    from MTF_competitive'
    have "T_on MTF s0 rs / 2 \<le> of_int(T s0 rs as)"
      by(simp add: field_simps length_greater_0_conv[symmetric]
        del: length_greater_0_conv) }
  hence "T_on MTF s0 rs / 2 \<le> T_opt s0 rs"
    apply(simp add: T_opt_def Inf_nat_def)
    apply(rule LeastI2_wellorder)
    using length_replicate[of "length rs" undefined] apply fastforce
    apply auto
    done
  thus ?thesis using assms by(simp add: field_simps
    length_greater_0_conv[symmetric] del: length_greater_0_conv)
qed
 
theorem MTF_is_2_competitive: "compet MTF 2 {s . distinct s}"
unfolding compet_def using compet_MTF' by fastforce 


subsection "Lower Bound for Competitiveness"

text\<open>This result is independent of MTF
but is based on the list update problem defined in this theory.\<close>

lemma rat_fun_lem:
   fixes l c :: real
   assumes [simp]: "F \<noteq> bot"
   assumes "0 < l"
   assumes ev: 
     "eventually (\<lambda>n. l \<le> f n / g n) F"
     "eventually (\<lambda>n. (f n + c) / (g n + d) \<le> u) F"
   and
     g: "LIM n F. g n :> at_top"
   shows "l \<le> u"
proof (rule dense_le_bounded[OF \<open>0 < l\<close>])
   fix x assume x: "0 < x" "x < l"

   define m where "m = (x - l) / 2"
   define k where "k = l / (x - m)"
   have "x = l / k + m" "1 < k" "m < 0"
     unfolding k_def m_def using x by (auto simp: divide_simps)
   
   from \<open>1 < k\<close> have "LIM n F. (k - 1) * g n :> at_top"
     by (intro filterlim_tendsto_pos_mult_at_top[OF tendsto_const _ g]) (simp add: field_simps)
   then have "eventually (\<lambda>n. d \<le> (k - 1) * g n) F"
     by (simp add: filterlim_at_top)
   moreover have "eventually (\<lambda>n. 1 \<le> g n) F" "eventually (\<lambda>n. 1 - d \<le> g n) F" "eventually (\<lambda>n. c / m - d \<le> g n) F"
     using g by (auto simp add: filterlim_at_top)
   ultimately have "eventually (\<lambda>n. x \<le> u) F"
     using ev
   proof eventually_elim
     fix n assume d: "d \<le> (k - 1) * g n" "1 \<le> g n" "1 - d \<le> g n" "c / m - d \<le> g n"
       and l: "l \<le> f n / g n" and u: "(f n + c) / (g n + d) \<le> u"
     from d have "g n + d \<le> k * g n"
       by (simp add: field_simps)
     from d have g: "0 < g n" "0 < g n + d"
       by (auto simp: field_simps)
     with \<open>0 < l\<close> l have "0 < f n"
       by (auto simp: field_simps intro: mult_pos_pos less_le_trans)

     note \<open>x = l / k + m\<close>
     also have "l / k \<le> f n / (k * g n)"
       using l \<open>1 < k\<close> by (simp add: field_simps)
     also have "\<dots> \<le> f n / (g n + d)"
       using d \<open>1 < k\<close> \<open>0 < f n\<close> by (intro divide_left_mono mult_pos_pos) (auto simp: field_simps)
     also have "m \<le> c / (g n + d)"
       using \<open>c / m - d \<le> g n\<close> \<open>0 < g n\<close> \<open>0 < g n + d\<close> \<open>m < 0\<close> by (simp add: field_simps)
     also have "f n / (g n + d) + c / (g n + d) = (f n + c) / (g n + d)"
       using \<open>0 < g n + d\<close> by (auto simp: add_divide_distrib)
     also note u
     finally show "x \<le> u" by simp
   qed
   then show "x \<le> u" by auto
qed


lemma compet_lb0:
fixes a Aon Aoff cruel 
defines "f s0 rs == real(T_on Aon s0 rs)"
defines "g s0 rs == real(T_off Aoff s0 rs)"
assumes "\<And>rs s0. size(Aoff s0 rs) = length rs" and "\<And>n. cruel n \<noteq> []"
assumes "compet Aon c S0" and "c\<ge>0" and "s0 \<in> S0"
 and l: "eventually (\<lambda>n. f s0 (cruel n) / (g s0 (cruel n) + a) \<ge> l) sequentially"
 and g: "LIM n sequentially. g s0 (cruel n) :> at_top"
 and "l > 0" and "\<And>n. static s0 (cruel n)"
shows "l \<le> c"
proof-
  let ?h = "\<lambda>b s0 rs. (f s0 rs - b) / g s0 rs"
  have g': "LIM n sequentially. g s0 (cruel n) + a :> at_top"
    using filterlim_tendsto_add_at_top[OF tendsto_const g]
    by (simp add: ac_simps)
  from competE[OF assms(5) \<open>c\<ge>0\<close> _ \<open>s0 \<in> S0\<close>] assms(3) obtain b where
    "\<forall>rs. static s0 rs \<and> rs \<noteq> [] \<longrightarrow> ?h b s0 rs \<le> c "
    by (fastforce simp del: neq0_conv simp: neq0_conv[symmetric]
        field_simps f_def g_def T_off_neq0[of Aoff, OF assms(3)])
  hence "\<forall>n. (?h b s0 o cruel) n \<le> c" using assms(4,11) by simp
  with rat_fun_lem[OF sequentially_bot \<open>l>0\<close> _ _ g', of "f s0 o cruel" "-b" "- a" c] assms(7) l
  show "l \<le> c" by (auto)
qed

text \<open>Sorting\<close>

fun ins_sws where
"ins_sws k x [] = []" |
"ins_sws k x (y#ys) = (if k x \<le> k y then [] else map Suc (ins_sws k x ys) @ [0])"

fun sort_sws where
"sort_sws k [] = []" |
"sort_sws k (x#xs) =
  ins_sws k x (sort_key k xs) @  map Suc (sort_sws k xs)"

lemma length_ins_sws: "length(ins_sws k x xs) \<le> length xs"
by(induction xs) auto

lemma length_sort_sws_le: "length(sort_sws k xs) \<le> length xs ^ 2"
proof(induction xs)
  case (Cons x xs) thus ?case
    using length_ins_sws[of k x "sort_key k xs"] by (simp add: numeral_eq_Suc)
qed simp

lemma swaps_ins_sws:
  "swaps (ins_sws k x xs) (x#xs) = insort_key k x xs"
by(induction xs)(auto simp: swap_def[of 0])

lemma swaps_sort_sws[simp]:
  "swaps (sort_sws k xs) xs = sort_key k xs"
by(induction xs)(auto simp: swaps_ins_sws)

text\<open>The cruel adversary:\<close>

fun cruel :: "('a,'is) alg_on \<Rightarrow> 'a state * 'is \<Rightarrow> nat \<Rightarrow> 'a list" where
"cruel A s 0 = []" |
"cruel A s (Suc n) = last (fst s) # cruel A (Step A s (last (fst s))) n"

definition adv :: "('a,'is) alg_on \<Rightarrow> ('a::linorder) alg_off" where
"adv A s rs = (if rs=[] then [] else
  let crs = cruel A (Step A (s, fst A s) (last s)) (size rs - 1)
  in (0,sort_sws (\<lambda>x. size rs - 1 - count_list crs x) s) # replicate (size rs - 1) (0,[]))"

lemma set_cruel: "s \<noteq> [] \<Longrightarrow> set(cruel A (s,is) n) \<subseteq> set s"
apply(induction n arbitrary: s "is")
apply(auto simp: step_def Step_def split: prod.split)
by (metis empty_iff swaps_inv last_in_set list.set(1) rev_subsetD set_mtf2)

lemma static_cruel: "s \<noteq> [] \<Longrightarrow> static s (cruel A (s,is) n)"
by(simp add: set_cruel static_def)

(* Do not convert into structured proof - eta conversion screws it up! *)
lemma T_cruel:
  "s \<noteq> [] \<Longrightarrow> distinct s \<Longrightarrow>
  T s (cruel A (s,is) n) (off2 A (s,is) (cruel A (s,is) n)) \<ge> n*(length s)"
apply(induction n arbitrary: s "is")
 apply(simp)
apply(erule_tac x = "fst(Step A (s, is) (last s))" in meta_allE)
apply(erule_tac x = "snd(Step A (s, is) (last s))" in meta_allE)
apply(frule_tac sws = "snd(fst(snd A (s,is) (last s)))" in index_swaps_last_size)
apply(simp add: distinct_step t_def split_def Step_def
        length_greater_0_conv[symmetric] del: length_greater_0_conv)
done

lemma length_cruel[simp]: "length (cruel A s n) = n"
by (induction n arbitrary: s) (auto)

lemma t_sort_sws: "t s r (mf, sort_sws k s) \<le> size s ^ 2 + size s + 1"
using length_sort_sws_le[of k s] index_le_size[of "sort_key k s" r]
by (simp add: t_def add_mono index_le_size algebra_simps)

lemma T_noop:
  "n = length rs \<Longrightarrow> T s rs (replicate n (0, [])) = (\<Sum>r\<leftarrow>rs. index s r + 1)"
by(induction rs arbitrary: s n)(auto simp: t_def step_def)


lemma sorted_asc: "j\<le>i \<Longrightarrow> i<size ss \<Longrightarrow> \<forall>x \<in> set ss. \<forall>y \<in> set ss. k(x) \<le> k(y) \<longrightarrow> f y \<le> f x
  \<Longrightarrow> sorted (map k ss) \<Longrightarrow> f (ss ! i) \<le> f (ss ! j)"
by (auto simp: sorted_iff_nth_mono)


lemma sorted_weighted_gauss_Ico_div2:
  fixes f :: "nat \<Rightarrow> nat"
  assumes "\<And>i j. i \<le> j \<Longrightarrow> j < n \<Longrightarrow> f i \<ge> f j"
  shows "(\<Sum>i=0..<n. (i + 1) * f i) \<le> (n + 1) * sum f {0..<n} div 2"
proof (cases n)
  case 0
  then show ?thesis
    by simp
next
  case (Suc n)
  with assms have "Suc n * (\<Sum>i=0..<Suc n. Suc i * f i) \<le> (\<Sum>i=0..<Suc n. Suc i) * sum f {0..<Suc n}"
    by (intro Chebyshev_sum_upper_nat [of "Suc n" Suc f]) auto
  then have "Suc n * (2 * (\<Sum>i=0..n. Suc i * f i)) \<le> 2 * (\<Sum>i=0..n. Suc i) * sum f {0..n}"
    by (simp add: atLeastLessThanSuc_atLeastAtMost)
  also have "2 * (\<Sum>i=0..n. Suc i) = Suc n * (n + 2)"
    using arith_series_nat [of 1 1 n] by simp
  finally have "2 * (\<Sum>i=0..n. Suc i * f i) \<le> (n + 2) * sum f {0..n}"
    by (simp only: ac_simps Suc_mult_le_cancel1)
  with Suc show ?thesis
    by (simp only: atLeastLessThanSuc_atLeastAtMost) simp
qed

lemma T_adv: assumes "l \<noteq> 0"
shows "T_off (adv A) [0..<l] (cruel A ([0..<l],fst A [0..<l]) (Suc n))
  \<le> l\<^sup>2 + l + 1 + (l + 1) * n div 2"  (is "?l \<le> ?r")
proof-
  let ?s = "[0..<l]"
  let ?r = "last ?s"
  let ?S' = "Step A (?s,fst A ?s) ?r"
  let ?s' = "fst ?S'"
  let ?cr = "cruel A ?S' n"
  let ?c = "count_list ?cr"
  let ?k = "\<lambda>x. n - ?c x"
  let ?sort = "sort_key ?k ?s"
  have 1: "set ?s' = {0..<l}"
    by(simp add: set_step Step_def split: prod.split)
  have 3: "\<And>x. x < l \<Longrightarrow> ?c x \<le> n"
    by(simp) (metis count_le_length length_cruel)
  have "?l = t ?s (last ?s) (0, sort_sws ?k ?s) + (\<Sum>x\<in>set ?s'. ?c x * (index ?sort x + 1))"
    using assms
    apply(simp add:  adv_def T_noop sum_list_map_eq_sum_count2[OF set_cruel] Step_def
      split: prod.split)
    apply(subst (3) step_def)
    apply(simp)
    done
  also have "(\<Sum>x\<in>set ?s'. ?c x * (index ?sort x + 1)) = (\<Sum>x\<in>{0..<l}. ?c x * (index ?sort x + 1))"
    by (simp add: 1)
  also have "\<dots> = (\<Sum>x\<in>{0..<l}. ?c (?sort ! x) * (index ?sort (?sort ! x) + 1))"
    by(rule sum.reindex_bij_betw[where ?h = "nth ?sort", symmetric])
      (simp add: bij_betw_imageI inj_on_nth nth_image)
  also have "\<dots> = (\<Sum>x\<in>{0..<l}. ?c (?sort ! x) * (x+1))"
    by(simp add: index_nth_id)
  also have "\<dots> \<le> (\<Sum>x\<in>{0..<l}. (x+1) * ?c (?sort ! x))"
    by (simp add: algebra_simps)
  also(ord_eq_le_subst) have "\<dots> \<le> (l+1) * (\<Sum>x\<in>{0..<l}. ?c (?sort ! x)) div 2"
    apply(rule sorted_weighted_gauss_Ico_div2)
    apply(erule sorted_asc[where k = "\<lambda>x. n - count_list (cruel A ?S' n) x"])
    apply(auto simp add: index_nth_id dest!: 3)
    using assms [[linarith_split_limit = 20]] by simp
  also have "(\<Sum>x\<in>{0..<l}. ?c (?sort ! x)) = (\<Sum>x\<in>{0..<l}. ?c (?sort ! (index ?sort x)))"
    by(rule sum.reindex_bij_betw[where ?h = "index ?sort", symmetric])
      (simp add: bij_betw_imageI inj_on_index2 index_image)
  also have "\<dots> = (\<Sum>x\<in>{0..<l}. ?c x)" by(simp)
  also have "\<dots> = length ?cr"
    using set_cruel[of ?s' A _ n] assms 1
    by(auto simp add: sum_count_set Step_def split: prod.split)
  also have "\<dots> = n" by simp
  also have "t ?s (last ?s) (0, sort_sws ?k ?s) \<le> (length ?s)^2 + length ?s + 1"
    by(rule t_sort_sws)
  also have "\<dots> = l^2 + l + 1" by simp
  finally show "?l \<le> l\<^sup>2 + l + 1 + (l + 1) * n div 2" by auto
qed

text \<open>The main theorem:\<close>

theorem compet_lb2:
assumes "compet A c {xs::nat list. size xs = l}" and "l \<noteq> 0" and "c \<ge> 0"
shows "c \<ge> 2*l/(l+1)"
proof (rule compet_lb0[OF _ _ assms(1) \<open>c\<ge>0\<close>])
  let ?S0 = "{xs::nat list. size xs = l}"
  let ?s0 = "[0..<l]"
  let ?cruel = "cruel A (?s0,fst A ?s0) o Suc"
  let ?on = "\<lambda>n. T_on A ?s0 (?cruel n)"
  let ?off = "\<lambda>n. T_off (adv A) ?s0 (?cruel n)"
  show "\<And>s0 rs. length (adv A s0 rs) = length rs" by(simp add: adv_def)
  show "\<And>n. ?cruel n \<noteq> []" by auto
  show "?s0 \<in> ?S0" by simp
  { fix Z::real and n::nat assume "n \<ge> nat(ceiling Z)"
    have "?off n \<ge> length(?cruel n)" by(rule T_ge_len) (simp add: adv_def)
    hence "?off n > n" by simp
    hence "Z \<le> ?off n" using \<open>n \<ge> nat(ceiling Z)\<close> by linarith }
  thus "LIM n sequentially. real (?off n) :> at_top"
    by(auto simp only: filterlim_at_top eventually_sequentially)
  let ?a = "- (l^2 + l + 1)"
  { fix n assume "n \<ge> l^2 + l + 1"
    have "2*l/(l+1) = 2*l*(n+1) / ((l+1)*(n+1))"
      by (simp del: One_nat_def)
    also have "\<dots> = 2*real(l*(n+1)) / ((l+1)*(n+1))" by simp
    also have "l * (n+1) \<le> ?on n"
      using T_cruel[of ?s0 "Suc n"] \<open>l \<noteq> 0\<close>
      by (simp add: ac_simps)
    also have "2*real(?on n) / ((l+1)*(n+1)) \<le> 2*real(?on n)/(2*(?off n + ?a))"
    proof -
      have 0: "2*real(?on n) \<ge> 0" by simp
      have 1: "0 < real ((l + 1) * (n + 1))" by (simp del: of_nat_Suc)
      have "?off n \<ge> length(?cruel n)"
        by(rule T_ge_len) (simp add: adv_def)
      hence "?off n > n" by simp
      hence "?off n + ?a > 0" using \<open>n \<ge> l^2 + l + 1\<close> by linarith
      hence 2: "real_of_int(2*(?off n + ?a)) > 0"
        by(simp only: of_int_0_less_iff zero_less_mult_iff zero_less_numeral simp_thms)
      have "?off n + ?a \<le> (l+1)*(n) div 2"
        using T_adv[OF \<open>l\<noteq>0\<close>, of A n]
        by (simp only: o_apply of_nat_add of_nat_le_iff)
      also have "\<dots> \<le> (l+1)*(n+1) div 2" by (simp)
      finally have "2*(?off n + ?a) \<le> (l+1)*(n+1)"
        by (simp add: zdiv_int)
      hence "of_int(2*(?off n + ?a)) \<le> real((l+1)*(n+1))" by (simp only: of_int_le_iff)
      from divide_left_mono[OF this 0 mult_pos_pos[OF 1 2]] show ?thesis .
    qed
    also have "\<dots> = ?on n / (?off n + ?a)"
      by (simp del: distrib_left_numeral One_nat_def cruel.simps)
    finally have "2*l/(l+1) \<le> ?on n / (real (?off n) + ?a)"
      by (auto simp: divide_right_mono)
  }
  thus "eventually (\<lambda>n. (2 * l) / (l + 1) \<le> ?on n / (real(?off n) + ?a)) sequentially"
    by(auto simp add: filterlim_at_top eventually_sequentially)
  show "0 < 2*l / (l+1)" using \<open>l \<noteq> 0\<close> by(simp)
  show "\<And>n. static ?s0 (?cruel n)" using \<open>l \<noteq> 0\<close> by(simp add: static_cruel del: cruel.simps)
qed


end
