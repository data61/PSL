(* Author: Alexander Maletzky *)

section \<open>Direct Decompositions and Hilbert Functions\<close>

theory Hilbert_Function
  imports Dube_Prelims Degree_Section "HOL-Library.Permutation"
begin

subsection \<open>Direct Decompositions\<close>

text \<open>The main reason for defining \<open>direct_decomp\<close> in terms of lists rather than sets is that
  lemma \<open>direct_decomp_direct_decomp\<close> can be proved easier. At some point one could invest the time
  to re-define \<open>direct_decomp\<close> in terms of sets (possibly adding a couple of further assumptions to
  \<open>direct_decomp_direct_decomp\<close>).\<close>

definition direct_decomp :: "'a set \<Rightarrow> 'a::comm_monoid_add set list \<Rightarrow> bool"
  where "direct_decomp A ss \<longleftrightarrow> bij_betw sum_list (listset ss) A"

lemma direct_decompI:
  "inj_on sum_list (listset ss) \<Longrightarrow> sum_list ` listset ss = A \<Longrightarrow> direct_decomp A ss"
  by (simp add: direct_decomp_def bij_betw_def)

lemma direct_decompI_alt:
  "(\<And>qs. qs \<in> listset ss \<Longrightarrow> sum_list qs \<in> A) \<Longrightarrow> (\<And>a. a \<in> A \<Longrightarrow> \<exists>!qs\<in>listset ss. a = sum_list qs) \<Longrightarrow>
    direct_decomp A ss"
  by (auto simp: direct_decomp_def intro!: bij_betwI') blast

lemma direct_decompD:
  assumes "direct_decomp A ss"
  shows "qs \<in> listset ss \<Longrightarrow> sum_list qs \<in> A" and "inj_on sum_list (listset ss)"
    and "sum_list ` listset ss = A"
  using assms by (auto simp: direct_decomp_def bij_betw_def)

lemma direct_decompE:
  assumes "direct_decomp A ss" and "a \<in> A"
  obtains qs where "qs \<in> listset ss" and "a = sum_list qs"
  using assms by (auto simp: direct_decomp_def bij_betw_def)

lemma direct_decomp_unique:
  "direct_decomp A ss \<Longrightarrow> qs \<in> listset ss \<Longrightarrow> qs' \<in> listset ss \<Longrightarrow> sum_list qs = sum_list qs' \<Longrightarrow>
    qs = qs'"
  by (auto dest: direct_decompD simp: inj_on_def)

lemma direct_decomp_singleton: "direct_decomp A [A]"
proof (rule direct_decompI_alt)
  fix qs
  assume "qs \<in> listset [A]"
  then obtain q where "q \<in> A" and "qs = [q]" by (rule listset_singletonE)
  thus "sum_list qs \<in> A" by simp
next
  fix a
  assume "a \<in> A"
  show "\<exists>!qs\<in>listset [A]. a = sum_list qs"
  proof (intro ex1I conjI allI impI)
    from \<open>a \<in> A\<close> refl show "[a] \<in> listset [A]" by (rule listset_singletonI)
  next
    fix qs
    assume "qs \<in> listset [A] \<and> a = sum_list qs"
    hence a: "a = sum_list qs" and "qs \<in> listset [A]" by simp_all
    from this(2) obtain b where qs: "qs = [b]" by (rule listset_singletonE)
    with a show "qs = [a]" by simp
  qed simp_all
qed

(* TODO: Move. *)
lemma mset_bij:
  assumes "bij_betw f {..<length xs} {..<length ys}" and "\<And>i. i < length xs \<Longrightarrow> xs ! i = ys ! f i"
  shows "mset xs = mset ys"
proof -
  from assms(1) have 1: "inj_on f {0..<length xs}" and 2: "f ` {0..<length xs} = {0..<length ys}"
    by (simp_all add: bij_betw_def lessThan_atLeast0)
  let ?f = "(!) ys \<circ> f"
  have "xs = map ?f [0..<length xs]" unfolding list_eq_iff_nth_eq
  proof (intro conjI allI impI)
    fix i
    assume "i < length xs"
    hence "xs ! i = ys ! f i" by (rule assms(2))
    also from \<open>i < length xs\<close> have "\<dots> = map ((!) ys \<circ> f) [0..<length xs] ! i" by simp
    finally show "xs ! i = map ((!) ys \<circ> f) [0..<length xs] ! i" .
  qed simp
  hence "mset xs = mset (map ?f [0..<length xs])" by (rule arg_cong)
  also have "\<dots> = image_mset ((!) ys) (image_mset f (mset_set {0..<length xs}))"
    by (simp flip: image_mset.comp)
  also from 1 have "\<dots> = image_mset ((!) ys) (mset_set {0..<length ys})"
    by (simp add: image_mset_mset_set 2)
  also have "\<dots> = mset (map ((!) ys) [0..<length ys])" by simp
  finally show "mset xs = mset ys" by (simp only: map_nth)
qed

lemma direct_decomp_perm:
  assumes "direct_decomp A ss1" and "perm ss1 ss2"
  shows "direct_decomp A ss2"
proof -
  from assms(2) have len_ss1: "length ss1 = length ss2" by (rule perm_length)
  from assms(2) have "\<exists>f. bij_betw f {..<length ss1} {..<length ss2} \<and> (\<forall>i<length ss1. ss1 ! i = ss2 ! f i)"
    by (rule permutation_Ex_bij)
  then obtain f where f_bij: "bij_betw f {..<length ss2} {..<length ss1}"
    and f: "\<And>i. i < length ss2 \<Longrightarrow> ss1 ! i = ss2 ! f i" unfolding len_ss1 by blast
  define g where "g = inv_into {..<length ss2} f"
  from f_bij have g_bij: "bij_betw g {..<length ss1} {..<length ss2}"
    unfolding g_def len_ss1 by (rule bij_betw_inv_into)
  have f_g: "f (g i) = i" if "i < length ss1" for i
  proof -
    from that f_bij have "i \<in> f ` {..<length ss2}" by (simp add: bij_betw_def len_ss1)
    thus ?thesis by (simp only: f_inv_into_f g_def)
  qed
  have g_f: "g (f i) = i" if "i < length ss2" for i
  proof -
    from f_bij have "inj_on f {..<length ss2}" by (simp only: bij_betw_def)
    moreover from that have "i \<in> {..<length ss2}" by simp
    ultimately show ?thesis by (simp add: g_def)
  qed
  have g: "ss2 ! i = ss1 ! g i" if "i < length ss1" for i
  proof -
    from that have "i \<in> {..<length ss2}" by (simp add: len_ss1)
    hence "g i \<in> g ` {..<length ss2}" by (rule imageI)
    also from g_bij have "\<dots> = {..<length ss2}" by (simp only: len_ss1 bij_betw_def)
    finally have "g i < length ss2" by simp
    hence "ss1 ! g i = ss2 ! f (g i)" by (rule f)
    with that show ?thesis by (simp only: f_g)
  qed
  show ?thesis
  proof (rule direct_decompI_alt)
    fix qs2
    assume "qs2 \<in> listset ss2"
    then obtain qs1 where qs1_in: "qs1 \<in> listset ss1" and len_qs1: "length qs1 = length qs2"
      and *: "\<And>i. i < length qs2 \<Longrightarrow> qs1 ! i = qs2 ! f i" using f_bij f by (rule listset_permE) blast+
    from \<open>qs2 \<in> listset ss2\<close> have "length qs2 = length ss2" by (rule listsetD)
    with f_bij have "bij_betw f {..<length qs1} {..<length qs2}" by (simp only: len_qs1 len_ss1)
    hence "mset qs1 = mset qs2" using * by (rule mset_bij) (simp only: len_qs1)
    hence "sum_list qs2 = sum_list qs1" by (simp flip: sum_mset_sum_list)
    also from assms(1) qs1_in have "\<dots> \<in> A" by (rule direct_decompD)
    finally show "sum_list qs2 \<in> A" .
  next
    fix a
    assume "a \<in> A"
    with assms(1) obtain qs where a: "a = sum_list qs" and qs_in: "qs \<in> listset ss1"
      by (rule direct_decompE)
    from qs_in obtain qs2 where qs2_in: "qs2 \<in> listset ss2" and len_qs2: "length qs2 = length qs"
      and 1: "\<And>i. i < length qs \<Longrightarrow> qs2 ! i = qs ! g i" using g_bij g by (rule listset_permE) blast+
    show "\<exists>!qs\<in>listset ss2. a = sum_list qs"
    proof (intro ex1I conjI allI impI)
      from qs_in have len_qs: "length qs = length ss1" by (rule listsetD)
      with g_bij have g_bij2: "bij_betw g {..<length qs2} {..<length qs}" by (simp only: len_qs2 len_ss1)
      hence "mset qs2 = mset qs" using 1 by (rule mset_bij) (simp only: len_qs2)
      thus a2: "a = sum_list qs2" by (simp only: a flip: sum_mset_sum_list)

      fix qs'
      assume "qs' \<in> listset ss2 \<and> a = sum_list qs'"
      hence qs'_in: "qs' \<in> listset ss2" and a': "a = sum_list qs'" by simp_all
      from this(1) obtain qs1 where qs1_in: "qs1 \<in> listset ss1" and len_qs1: "length qs1 = length qs'"
      and 2: "\<And>i. i < length qs' \<Longrightarrow> qs1 ! i = qs' ! f i" using f_bij f by (rule listset_permE) blast+
      from \<open>qs' \<in> listset ss2\<close> have "length qs' = length ss2" by (rule listsetD)
      with f_bij have "bij_betw f {..<length qs1} {..<length qs'}" by (simp only: len_qs1 len_ss1)
      hence "mset qs1 = mset qs'" using 2 by (rule mset_bij) (simp only: len_qs1)
      hence "sum_list qs1 = sum_list qs'" by (simp flip: sum_mset_sum_list)
      hence "sum_list qs1 = sum_list qs" by (simp only: a flip: a')
      with assms(1) qs1_in qs_in have "qs1 = qs" by (rule direct_decomp_unique)
      show "qs' = qs2" unfolding list_eq_iff_nth_eq
      proof (intro conjI allI impI)
        from qs'_in have "length qs' = length ss2" by (rule listsetD)
        thus eq: "length qs' = length qs2" by (simp only: len_qs2 len_qs len_ss1)

        fix i
        assume "i < length qs'"
        hence "i < length qs2" by (simp only: eq)
        hence "i \<in> {..<length qs2}" and "i < length qs" and "i < length ss1"
          by (simp_all add: len_qs2 len_qs)
        from this(1) have "g i \<in> g ` {..<length qs2}" by (rule imageI)
        also from g_bij2 have "\<dots> = {..<length qs}" by (simp only: bij_betw_def)
        finally have "g i < length qs'" by (simp add: eq len_qs2)
        from \<open>i < length qs\<close> have "qs2 ! i = qs ! g i" by (rule 1)
        also have "\<dots> = qs1 ! g i" by (simp only: \<open>qs1 = qs\<close>)
        also from \<open>g i < length qs'\<close> have "\<dots> = qs' ! f (g i)" by (rule 2)
        also from \<open>i < length ss1\<close> have "\<dots> = qs' ! i" by (simp only: f_g)
        finally show "qs' ! i = qs2 ! i" by (rule sym)
      qed
    qed fact
  qed
qed

lemma direct_decomp_split_map:
  "direct_decomp A (map f ss) \<Longrightarrow> direct_decomp A (map f (filter P ss) @ map f (filter (- P) ss))"
proof (rule direct_decomp_perm)
  show "perm (map f ss) (map f (filter P ss) @ map f (filter (- P) ss))"
  proof (induct ss)
    case Nil
    show ?case by simp
  next
    case (Cons s ss)
    show ?case
    proof (cases "P s")
      case True
      with Cons show ?thesis by simp
    next
      case False
      have "map f (s # ss) = f s # map f ss" by simp
      also from Cons have "perm (f s # map f ss) (f s # map f (filter P ss) @ map f (filter (- P) ss))"
        by (rule perm.intros)
      also have "perm \<dots> (map f (filter P ss) @ map f (s # filter (- P) ss))"
        by (simp add: perm_append_Cons)
      also(trans) from False have "\<dots> = map f (filter P (s # ss)) @ map f (filter (- P) (s # ss))"
        by simp
      finally show ?thesis .
    qed
  qed
qed

lemmas direct_decomp_split = direct_decomp_split_map[where f=id, simplified]

lemma direct_decomp_direct_decomp:
  assumes "direct_decomp A (s # ss)" and "direct_decomp s rs"
  shows "direct_decomp A (ss @ rs)" (is "direct_decomp A ?ss")
proof (rule direct_decompI_alt)
  fix qs
  assume "qs \<in> listset ?ss"
  then obtain qs1 qs2 where qs1: "qs1 \<in> listset ss" and qs2: "qs2 \<in> listset rs" and qs: "qs = qs1 @ qs2"
    by (rule listset_appendE)
  have "sum_list qs = sum_list ((sum_list qs2) # qs1)" by (simp add: qs add.commute)
  also from assms(1) have "\<dots> \<in> A"
  proof (rule direct_decompD)
    from assms(2) qs2 have "sum_list qs2 \<in> s" by (rule direct_decompD)
    thus "sum_list qs2 # qs1 \<in> listset (s # ss)" using qs1 refl by (rule listset_ConsI)
  qed
  finally show "sum_list qs \<in> A" .
next
  fix a
  assume "a \<in> A"
  with assms(1) obtain qs1 where qs1_in: "qs1 \<in> listset (s # ss)" and a: "a = sum_list qs1"
    by (rule direct_decompE)
  from qs1_in obtain qs11 qs12 where "qs11 \<in> s" and qs12_in: "qs12 \<in> listset ss"
    and qs1: "qs1 = qs11 # qs12" by (rule listset_ConsE)
  from assms(2) this(1) obtain qs2 where qs2_in: "qs2 \<in> listset rs" and qs11: "qs11 = sum_list qs2"
    by (rule direct_decompE)
  let ?qs = "qs12 @ qs2"
  show "\<exists>!qs\<in>listset ?ss. a = sum_list qs"
  proof (intro ex1I conjI allI impI)
    from qs12_in qs2_in refl show "?qs \<in> listset ?ss" by (rule listset_appendI)

    show "a = sum_list ?qs" by (simp add: a qs1 qs11 add.commute)

    fix qs0
    assume "qs0 \<in> listset ?ss \<and> a = sum_list qs0"
    hence qs0_in: "qs0 \<in> listset ?ss" and a2: "a = sum_list qs0" by simp_all
    from this(1) obtain qs01 qs02 where qs01_in: "qs01 \<in> listset ss" and qs02_in: "qs02 \<in> listset rs"
      and qs0: "qs0 = qs01 @ qs02" by (rule listset_appendE)
    note assms(1)
    moreover from _ qs01_in refl have "(sum_list qs02) # qs01 \<in> listset (s # ss)" (is "?qs' \<in> _")
    proof (rule listset_ConsI)
      from assms(2) qs02_in show "sum_list qs02 \<in> s" by (rule direct_decompD)
    qed
    moreover note qs1_in
    moreover from a2 have "sum_list ?qs' = sum_list qs1" by (simp add: qs0 a add.commute)
    ultimately have "?qs' = qs11 # qs12" unfolding qs1 by (rule direct_decomp_unique)
    hence "qs11 = sum_list qs02" and 1: "qs01 = qs12" by simp_all
    from this(1) have "sum_list qs02 = sum_list qs2" by (simp only: qs11)
    with assms(2) qs02_in qs2_in have "qs02 = qs2" by (rule direct_decomp_unique)
    thus "qs0 = qs12 @ qs2" by (simp only: 1 qs0)
  qed
qed

lemma sum_list_map_times: "sum_list (map ((*) x) xs) = (x::'a::semiring_0) * sum_list xs"
  by (induct xs) (simp_all add: algebra_simps)

lemma direct_decomp_image_times:
  assumes "direct_decomp (A::'a::semiring_0 set) ss" and "\<And>a b. x * a = x * b \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> a = b"
  shows "direct_decomp ((*) x ` A) (map ((`) ((*) x)) ss)" (is "direct_decomp ?A ?ss")
proof (rule direct_decompI_alt)
  fix qs
  assume "qs \<in> listset ?ss"
  then obtain qs0 where qs0_in: "qs0 \<in> listset ss" and qs: "qs = map ((*) x) qs0"
    by (rule listset_map_imageE)
  have "sum_list qs = x * sum_list qs0" by (simp only: qs sum_list_map_times)
  moreover from assms(1) qs0_in have "sum_list qs0 \<in> A" by (rule direct_decompD)
  ultimately show "sum_list qs \<in> (*) x ` A" by (rule image_eqI)
next
  fix a
  assume "a \<in> ?A"
  then obtain a' where "a' \<in> A" and a: "a = x * a'" ..
  from assms(1) this(1) obtain qs' where qs'_in: "qs' \<in> listset ss" and a': "a' = sum_list qs'"
    by (rule direct_decompE)
  define qs where "qs = map ((*) x) qs'"
  show "\<exists>!qs\<in>listset ?ss. a = sum_list qs"
  proof (intro ex1I conjI allI impI)
    from qs'_in qs_def show "qs \<in> listset ?ss" by (rule listset_map_imageI)

    fix qs0
    assume "qs0 \<in> listset ?ss \<and> a = sum_list qs0"
    hence "qs0 \<in> listset ?ss" and a0: "a = sum_list qs0" by simp_all
    from this(1) obtain qs1 where qs1_in: "qs1 \<in> listset ss" and qs0: "qs0 = map ((*) x) qs1"
      by (rule listset_map_imageE)
    show "qs0 = qs"
    proof (cases "x = 0")
      case True
      from qs1_in have "length qs1 = length ss" by (rule listsetD)
      moreover from qs'_in have "length qs' = length ss" by (rule listsetD)
      ultimately show ?thesis by (simp add: qs_def qs0 list_eq_iff_nth_eq True)
    next
      case False
      have "x * sum_list qs1 = a" by (simp only: a0 qs0 sum_list_map_times)
      also have "\<dots> = x * sum_list qs'" by (simp only: a' a)
      finally have "sum_list qs1 = sum_list qs'" using False by (rule assms(2))
      with assms(1) qs1_in qs'_in have "qs1 = qs'" by (rule direct_decomp_unique)
      thus ?thesis by (simp only: qs0 qs_def)
    qed
  qed (simp only: a a' qs_def sum_list_map_times)
qed

lemma direct_decomp_appendD:
  assumes "direct_decomp A (ss1 @ ss2)"
  shows "{} \<notin> set ss2 \<Longrightarrow> direct_decomp (sum_list ` listset ss1) ss1" (is "_ \<Longrightarrow> ?thesis1")
    and "{} \<notin> set ss1 \<Longrightarrow> direct_decomp (sum_list ` listset ss2) ss2" (is "_ \<Longrightarrow> ?thesis2")
    and "direct_decomp A [sum_list ` listset ss1, sum_list ` listset ss2]" (is "direct_decomp _ ?ss")
proof -
  have rl: "direct_decomp (sum_list ` listset ts1) ts1"
    if "direct_decomp A (ts1 @ ts2)" and "{} \<notin> set ts2" for ts1 ts2
  proof (intro direct_decompI inj_onI refl)
    fix qs1 qs2
    assume qs1: "qs1 \<in> listset ts1" and qs2: "qs2 \<in> listset ts1"
    assume eq: "sum_list qs1 = sum_list qs2"
    from that(2) have "listset ts2 \<noteq> {}" by (simp add: listset_empty_iff)
    then obtain qs3 where qs3: "qs3 \<in> listset ts2" by blast
    note that(1)
    moreover from qs1 qs3 refl have "qs1 @ qs3 \<in> listset (ts1 @ ts2)" by (rule listset_appendI)
    moreover from qs2 qs3 refl have "qs2 @ qs3 \<in> listset (ts1 @ ts2)" by (rule listset_appendI)
    moreover have "sum_list (qs1 @ qs3) = sum_list (qs2 @ qs3)" by (simp add: eq)
    ultimately have "qs1 @ qs3 = qs2 @ qs3" by (rule direct_decomp_unique)
    thus "qs1 = qs2" by simp
  qed

  {
    assume "{} \<notin> set ss2"
    with assms show ?thesis1 by (rule rl)
  }

  {
    from assms perm_append_swap have "direct_decomp A (ss2 @ ss1)" by (rule direct_decomp_perm)
    moreover assume "{} \<notin> set ss1"
    ultimately show ?thesis2 by (rule rl)
  }

  show "direct_decomp A ?ss"
  proof (rule direct_decompI_alt)
    fix qs
    assume "qs \<in> listset ?ss"
    then obtain q1 q2 where q1: "q1 \<in> sum_list ` listset ss1" and q2: "q2 \<in> sum_list ` listset ss2"
      and qs: "qs = [q1, q2]" by (rule listset_doubletonE)
    from q1 obtain qs1 where qs1: "qs1 \<in> listset ss1" and q1: "q1 = sum_list qs1" ..
    from q2 obtain qs2 where qs2: "qs2 \<in> listset ss2" and q2: "q2 = sum_list qs2" ..
    from qs1 qs2 refl have "qs1 @ qs2 \<in> listset (ss1 @ ss2)" by (rule listset_appendI)
    with assms have "sum_list (qs1 @ qs2) \<in> A" by (rule direct_decompD)
    thus "sum_list qs \<in> A" by (simp add: qs q1 q2)
  next
    fix a
    assume "a \<in> A"
    with assms obtain qs0 where qs0_in: "qs0 \<in> listset (ss1 @ ss2)" and a: "a = sum_list qs0"
      by (rule direct_decompE)
    from this(1) obtain qs1 qs2 where qs1: "qs1 \<in> listset ss1" and qs2: "qs2 \<in> listset ss2"
      and qs0: "qs0 = qs1 @ qs2" by (rule listset_appendE)
    from qs1 have len_qs1: "length qs1 = length ss1" by (rule listsetD)
    define qs where "qs = [sum_list qs1, sum_list qs2]"
    show "\<exists>!qs\<in>listset ?ss. a = sum_list qs"
    proof (intro ex1I conjI)
      from qs1 have "sum_list qs1 \<in> sum_list ` listset ss1" by (rule imageI)
      moreover from qs2 have "sum_list qs2 \<in> sum_list ` listset ss2" by (rule imageI)
      ultimately show "qs \<in> listset ?ss" using qs_def by (rule listset_doubletonI)

      fix qs'
      assume "qs' \<in> listset ?ss \<and> a = sum_list qs'"
      hence "qs' \<in> listset ?ss" and a': "a = sum_list qs'" by simp_all
      from this(1) obtain q1 q2 where q1: "q1 \<in> sum_list ` listset ss1"
        and q2: "q2 \<in> sum_list ` listset ss2" and qs': "qs' = [q1, q2]" by (rule listset_doubletonE)
      from q1 obtain qs1' where qs1': "qs1' \<in> listset ss1" and q1: "q1 = sum_list qs1'" ..
      from q2 obtain qs2' where qs2': "qs2' \<in> listset ss2" and q2: "q2 = sum_list qs2'" ..
      from qs1' have len_qs1': "length qs1' = length ss1" by (rule listsetD)
      note assms
      moreover from qs1' qs2' refl have "qs1' @ qs2' \<in> listset (ss1 @ ss2)" by (rule listset_appendI)
      moreover note qs0_in
      moreover have "sum_list (qs1' @ qs2') = sum_list qs0" by (simp add: a' qs' flip: a q1 q2)
      ultimately have "qs1' @ qs2' = qs0" by (rule direct_decomp_unique)
      also have "\<dots> = qs1 @ qs2" by fact
      finally show "qs' = qs" by (simp add: qs_def qs' q1 q2 len_qs1 len_qs1')
    qed (simp add: qs_def a qs0)
  qed
qed

lemma direct_decomp_Cons_zeroI:
  assumes "direct_decomp A ss"
  shows "direct_decomp A ({0} # ss)"
proof (rule direct_decompI_alt)
  fix qs
  assume "qs \<in> listset ({0} # ss)"
  then obtain q qs' where "q \<in> {0}" and "qs' \<in> listset ss" and "qs = q # qs'"
    by (rule listset_ConsE)
  from this(1, 3) have "sum_list qs = sum_list qs'" by simp
  also from assms \<open>qs' \<in> listset ss\<close> have "\<dots> \<in> A" by (rule direct_decompD)
  finally show "sum_list qs \<in> A" .
next
  fix a
  assume "a \<in> A"
  with assms obtain qs' where qs': "qs' \<in> listset ss" and a: "a = sum_list qs'"
    by (rule direct_decompE)
  define qs where "qs = 0 # qs'"
  show "\<exists>!qs. qs \<in> listset ({0} # ss) \<and> a = sum_list qs"
  proof (intro ex1I conjI)
    from _ qs' qs_def show "qs \<in> listset ({0} # ss)" by (rule listset_ConsI) simp
  next
    fix qs0
    assume "qs0 \<in> listset ({0} # ss) \<and> a = sum_list qs0"
    hence "qs0 \<in> listset ({0} # ss)" and a0: "a = sum_list qs0" by simp_all
    from this(1) obtain q0 qs0' where "q0 \<in> {0}" and qs0': "qs0' \<in> listset ss"
      and qs0: "qs0 = q0 # qs0'" by (rule listset_ConsE)
    from this(1, 3) have "sum_list qs0' = sum_list qs'" by (simp add: a0 flip: a)
    with assms qs0' qs' have "qs0' = qs'" by (rule direct_decomp_unique)
    with \<open>q0 \<in> {0}\<close> show "qs0 = qs" by (simp add: qs_def qs0)
  qed (simp add: qs_def a)
qed

lemma direct_decomp_Cons_zeroD:
  assumes "direct_decomp A ({0} # ss)"
  shows "direct_decomp A ss"
proof -
  have "direct_decomp {0} []" by (simp add: direct_decomp_def bij_betw_def)
  with assms have "direct_decomp A (ss @ [])" by (rule direct_decomp_direct_decomp)
  thus ?thesis by simp
qed

lemma direct_decomp_Cons_subsetI:
  assumes "direct_decomp A (s # ss)" and "\<And>s0. s0 \<in> set ss \<Longrightarrow> 0 \<in> s0"
  shows "s \<subseteq> A"
proof
  fix x
  assume "x \<in> s"
  moreover from assms(2) have "map (\<lambda>_. 0) ss \<in> listset ss"
    by (induct ss, auto simp del: listset.simps(2) intro: listset_ConsI)
  ultimately have "x # (map (\<lambda>_. 0) ss) \<in> listset (s # ss)" using refl by (rule listset_ConsI)
  with assms(1) have "sum_list (x # (map (\<lambda>_. 0) ss)) \<in> A" by (rule direct_decompD)
  thus "x \<in> A" by simp
qed

lemma direct_decomp_Int_zero:
  assumes "direct_decomp A ss" and "i < j" and "j < length ss" and "\<And>s. s \<in> set ss \<Longrightarrow> 0 \<in> s"
  shows "ss ! i \<inter> ss ! j = {0}"
proof -
  from assms(2, 3) have "i < length ss" by (rule less_trans)
  hence i_in: "ss ! i \<in> set ss" by simp
  from assms(3) have j_in: "ss ! j \<in> set ss" by simp
  show ?thesis
  proof
    show "ss ! i \<inter> ss ! j \<subseteq> {0}"
    proof
      fix x
      assume "x \<in> ss ! i \<inter> ss ! j"
      hence x_i: "x \<in> ss ! i" and x_j: "x \<in> ss ! j" by simp_all
      have 1: "(map (\<lambda>_. 0) ss)[k := y] \<in> listset ss" if "k < length ss" and "y \<in> ss ! k" for k y
        using assms(4) that
      proof (induct ss arbitrary: k)
        case Nil
        from Nil(2) show ?case by simp
      next
        case (Cons s ss)
        have *: "\<And>s'. s' \<in> set ss \<Longrightarrow> 0 \<in> s'" by (rule Cons.prems) simp
        show ?case
        proof (cases k)
          case k: 0
          with Cons.prems(3) have "y \<in> s" by simp
          moreover from * have "map (\<lambda>_. 0) ss \<in> listset ss"
            by (induct ss) (auto simp del: listset.simps(2) intro: listset_ConsI)
          moreover have "(map (\<lambda>_. 0) (s # ss))[k := y] = y # map (\<lambda>_. 0) ss" by (simp add: k)
          ultimately show ?thesis by (rule listset_ConsI)
        next
          case k: (Suc k')
          have "0 \<in> s" by (rule Cons.prems) simp
          moreover from * have "(map (\<lambda>_. 0) ss)[k' := y] \<in> listset ss"
          proof (rule Cons.hyps)
            from Cons.prems(2) show "k' < length ss" by (simp add: k)
          next
            from Cons.prems(3) show "y \<in> ss ! k'" by (simp add: k)
          qed
          moreover have "(map (\<lambda>_. 0) (s # ss))[k := y] = 0 # (map (\<lambda>_. 0) ss)[k' := y]"
            by (simp add: k)
          ultimately show ?thesis by (rule listset_ConsI)
        qed
      qed
      have 2: "sum_list ((map (\<lambda>_. 0) ss)[k := y]) = y" if "k < length ss" for k and y::'a
        using that by (induct ss arbitrary: k) (auto simp: add_ac split: nat.split)
      define qs1 where "qs1 = (map (\<lambda>_. 0) ss)[i := x]"
      define qs2 where "qs2 = (map (\<lambda>_. 0) ss)[j := x]"
      note assms(1)
      moreover from \<open>i < length ss\<close> x_i have "qs1 \<in> listset ss" unfolding qs1_def by (rule 1)
      moreover from assms(3) x_j have "qs2 \<in> listset ss" unfolding qs2_def by (rule 1)
      thm sum_list_update
      moreover from \<open>i < length ss\<close> assms(3) have "sum_list qs1 = sum_list qs2"
        by (simp add: qs1_def qs2_def 2)
      ultimately have "qs1 = qs2" by (rule direct_decomp_unique)
      hence "qs1 ! i = qs2 ! i" by simp
      with \<open>i < length ss\<close> assms(2, 3) show "x \<in> {0}" by (simp add: qs1_def qs2_def)
    qed
  next
    from i_in have "0 \<in> ss ! i" by (rule assms(4))
    moreover from j_in have "0 \<in> ss ! j" by (rule assms(4))
    ultimately show "{0} \<subseteq> ss ! i \<inter> ss ! j" by simp
  qed
qed

corollary direct_decomp_pairwise_zero:
  assumes "direct_decomp A ss" and "\<And>s. s \<in> set ss \<Longrightarrow> 0 \<in> s"
  shows "pairwise (\<lambda>s1 s2. s1 \<inter> s2 = {0}) (set ss)"
proof (rule pairwiseI)
  fix s1 s2
  assume "s1 \<in> set ss"
  then obtain i where "i < length ss" and s1: "s1 = ss ! i" by (metis in_set_conv_nth)
  assume "s2 \<in> set ss"
  then obtain j where "j < length ss" and s2: "s2 = ss ! j" by (metis in_set_conv_nth)
  assume "s1 \<noteq> s2"
  hence "i < j \<or> j < i" by (auto simp: s1 s2)
  thus "s1 \<inter> s2 = {0}"
  proof
    assume "i < j"
    with assms(1) show ?thesis unfolding s1 s2 using \<open>j < length ss\<close> assms(2)
      by (rule direct_decomp_Int_zero)
  next
    assume "j < i"
    with assms(1) have "s2 \<inter> s1 = {0}" unfolding s1 s2 using \<open>i < length ss\<close> assms(2)
      by (rule direct_decomp_Int_zero)
    thus ?thesis by (simp only: Int_commute)
  qed
qed

corollary direct_decomp_repeated_eq_zero:
  assumes "direct_decomp A ss" and "1 < count_list ss X" and "\<And>s. s \<in> set ss \<Longrightarrow> 0 \<in> s"
  shows "X = {0}"
proof -
  from assms(2) obtain i j where "i < j" and "j < length ss" and 1: "ss ! i = X" and 2: "ss ! j = X"
    by (rule count_list_gr_1_E)
  from assms(1) this(1, 2) assms(3) have "ss ! i \<inter> ss ! j = {0}" by (rule direct_decomp_Int_zero)
  thus ?thesis by (simp add: 1 2)
qed

corollary direct_decomp_map_Int_zero:
  assumes "direct_decomp A (map f ss)" and "s1 \<in> set ss" and "s2 \<in> set ss" and "s1 \<noteq> s2"
    and "\<And>s. s \<in> set ss \<Longrightarrow> 0 \<in> f s"
  shows "f s1 \<inter> f s2 = {0}"
proof -
  from assms(2) obtain i where "i < length ss" and s1: "s1 = ss ! i" by (metis in_set_conv_nth)
  from this(1) have i: "i < length (map f ss)" by simp
  from assms(3) obtain j where "j < length ss" and s2: "s2 = ss ! j" by (metis in_set_conv_nth)
  from this(1) have j: "j < length (map f ss)" by simp
  have *: "0 \<in> s" if "s \<in> set (map f ss)" for s
  proof -
    from that obtain s' where "s' \<in> set ss" and s: "s = f s'" unfolding set_map ..
    from this(1) show "0 \<in> s" unfolding s by (rule assms(5))
  qed
  show ?thesis
  proof (rule linorder_cases)
    assume "i < j"
    with assms(1) have "(map f ss) ! i \<inter> (map f ss) ! j = {0}"
      using j * by (rule direct_decomp_Int_zero)
    with i j show ?thesis by (simp add: s1 s2)
  next
    assume "j < i"
    with assms(1) have "(map f ss) ! j \<inter> (map f ss) ! i = {0}"
      using i * by (rule direct_decomp_Int_zero)
    with i j show ?thesis by (simp add: s1 s2 Int_commute)
  next
    assume "i = j"
    with assms(4) show ?thesis by (simp add: s1 s2)
  qed
qed

subsection \<open>Direct Decompositions and Vector Spaces\<close>

definition (in vector_space) is_basis :: "'b set \<Rightarrow> 'b set \<Rightarrow> bool"
  where "is_basis V B \<longleftrightarrow> (B \<subseteq> V \<and> independent B \<and> V \<subseteq> span B \<and> card B = dim V)"

definition (in vector_space) some_basis :: "'b set \<Rightarrow> 'b set"
  where "some_basis V = Eps (local.is_basis V)"

hide_const (open) real_vector.is_basis real_vector.some_basis

context vector_space
begin

lemma dim_empty [simp]: "dim {} = 0"
  using dim_span_eq_card_independent independent_empty by fastforce

lemma dim_zero [simp]: "dim {0} = 0"
  using dim_span_eq_card_independent independent_empty by fastforce

lemma independent_UnI:
  assumes "independent A" and "independent B" and "span A \<inter> span B = {0}"
  shows "independent (A \<union> B)"
proof
  from span_superset have "A \<inter> B \<subseteq> span A \<inter> span B" by blast
  hence "A \<inter> B = {}" unfolding assms(3) using assms(1, 2) dependent_zero by blast
  assume "dependent (A \<union> B)"
  then obtain T u v where "finite T" and "T \<subseteq> A \<union> B" and eq: "(\<Sum>v\<in>T. u v *s v) = 0"
    and "v \<in> T" and "u v \<noteq> 0" unfolding dependent_explicit by blast
  define TA where "TA = T \<inter> A"
  define TB where "TB = T \<inter> B"
  from \<open>T \<subseteq> A \<union> B\<close> have T: "T = TA \<union> TB" by (auto simp: TA_def TB_def)
  from \<open>finite T\<close> have "finite TA" and "TA \<subseteq> A" by (simp_all add: TA_def)
  from \<open>finite T\<close> have "finite TB" and "TB \<subseteq> B" by (simp_all add: TB_def)
  from \<open>A \<inter> B = {}\<close> \<open>TA \<subseteq> A\<close> this(2) have "TA \<inter> TB = {}" by blast
  have "0 = (\<Sum>v\<in>TA \<union> TB. u v *s v)" by (simp only: eq flip: T)
  also have "\<dots> = (\<Sum>v\<in>TA. u v *s v) + (\<Sum>v\<in>TB. u v *s v)" by (rule sum.union_disjoint) fact+
  finally have "(\<Sum>v\<in>TA. u v *s v) = (\<Sum>v\<in>TB. (- u) v *s v)" (is "?x = ?y")
    by (simp add: sum_negf eq_neg_iff_add_eq_0)
  from \<open>finite TB\<close> \<open>TB \<subseteq> B\<close> have "?y \<in> span B" by (auto simp: span_explicit simp del: uminus_apply)
  moreover from \<open>finite TA\<close> \<open>TA \<subseteq> A\<close> have "?x \<in> span A" by (auto simp: span_explicit)
  ultimately have "?y \<in> span A \<inter> span B" by (simp add: \<open>?x = ?y\<close>)
  hence "?x = 0" and "?y = 0" by (simp_all add: \<open>?x = ?y\<close> assms(3))
  from \<open>v \<in> T\<close> have "v \<in> TA \<union> TB" by (simp only: T)
  hence "u v = 0"
  proof
    assume "v \<in> TA"
    with assms(1) \<open>finite TA\<close> \<open>TA \<subseteq> A\<close> \<open>?x = 0\<close> show "u v = 0" by (rule independentD)
  next
    assume "v \<in> TB"
    with assms(2) \<open>finite TB\<close> \<open>TB \<subseteq> B\<close> \<open>?y = 0\<close> have "(- u) v = 0" by (rule independentD)
    thus "u v = 0" by simp
  qed
  with \<open>u v \<noteq> 0\<close> show False ..
qed

lemma subspace_direct_decomp:
  assumes "direct_decomp A ss" and "\<And>s. s \<in> set ss \<Longrightarrow> subspace s"
  shows "subspace A"
proof (rule subspaceI)
  let ?qs = "map (\<lambda>_. 0) ss"
  from assms(2) have "?qs \<in> listset ss"
    by (induct ss) (auto simp del: listset.simps(2) dest: subspace_0 intro: listset_ConsI)
  with assms(1) have "sum_list ?qs \<in> A" by (rule direct_decompD)
  thus "0 \<in> A" by simp
next
  fix p q
  assume "p \<in> A"
  with assms(1) obtain ps where ps: "ps \<in> listset ss" and p: "p = sum_list ps" by (rule direct_decompE)
  assume "q \<in> A"
  with assms(1) obtain qs where qs: "qs \<in> listset ss" and q: "q = sum_list qs" by (rule direct_decompE)
  from ps qs have l: "length ps = length qs" by (simp only: listsetD)
  from ps qs have "map2 (+) ps qs \<in> listset ss" (is "?qs \<in> _")
    by (rule listset_closed_map2) (auto dest: assms(2) subspace_add)
  with assms(1) have "sum_list ?qs \<in> A" by (rule direct_decompD)
  thus "p + q \<in> A" using l by (simp only: p q sum_list_map2_plus)
next
  fix c p
  assume "p \<in> A"
  with assms(1) obtain ps where "ps \<in> listset ss" and p: "p = sum_list ps" by (rule direct_decompE)
  from this(1) have "map ((*s) c) ps \<in> listset ss" (is "?qs \<in> _")
    by (rule listset_closed_map) (auto dest: assms(2) subspace_scale)
  with assms(1) have "sum_list ?qs \<in> A" by (rule direct_decompD)
  also have "sum_list ?qs = c *s sum_list ps" by (induct ps) (simp_all add: scale_right_distrib)
  finally show "c *s p \<in> A" by (simp only: p)
qed

lemma is_basis_alt: "subspace V \<Longrightarrow> is_basis V B \<longleftrightarrow> (independent B \<and> span B = V)"
  by (metis (full_types) is_basis_def dim_eq_card span_eq span_eq_iff)

lemma is_basis_finite: "is_basis V A \<Longrightarrow> is_basis V B \<Longrightarrow> finite A \<longleftrightarrow> finite B"
  unfolding is_basis_def using independent_span_bound by auto

lemma some_basis_is_basis: "is_basis V (some_basis V)"
proof -
  obtain B where "B \<subseteq> V" and "independent B" and "V \<subseteq> span B" and "card B = dim V"
    by (rule basis_exists)
  hence "is_basis V B" by (simp add: is_basis_def)
  thus ?thesis unfolding some_basis_def by (rule someI)
qed

corollary
  shows some_basis_subset: "some_basis V \<subseteq> V"
    and independent_some_basis: "independent (some_basis V)"
    and span_some_basis_supset: "V \<subseteq> span (some_basis V)"
    and card_some_basis: "card (some_basis V) = dim V"
  using some_basis_is_basis[of V] by (simp_all add: is_basis_def)

lemma some_basis_not_zero: "0 \<notin> some_basis V"
  using independent_some_basis dependent_zero by blast

lemma span_some_basis: "subspace V \<Longrightarrow> span (some_basis V) = V"
  by (simp add: span_subspace some_basis_subset span_some_basis_supset)

lemma direct_decomp_some_basis_pairwise_disjnt:
  assumes "direct_decomp A ss" and "\<And>s. s \<in> set ss \<Longrightarrow> subspace s"
  shows "pairwise (\<lambda>s1 s2. disjnt (some_basis s1) (some_basis s2)) (set ss)"
proof (rule pairwiseI)
  fix s1 s2
  assume "s1 \<in> set ss" and "s2 \<in> set ss" and "s1 \<noteq> s2"
  have "some_basis s1 \<inter> some_basis s2 \<subseteq> s1 \<inter> s2" using some_basis_subset by blast
  also from direct_decomp_pairwise_zero have "\<dots> = {0}"
  proof (rule pairwiseD)
    fix s
    assume "s \<in> set ss"
    hence "subspace s" by (rule assms(2))
    thus "0 \<in> s" by (rule subspace_0)
  qed fact+
  finally have "some_basis s1 \<inter> some_basis s2 \<subseteq> {0}" .
  with some_basis_not_zero show "disjnt (some_basis s1) (some_basis s2)"
    unfolding disjnt_def by blast
qed

lemma direct_decomp_span_some_basis:
  assumes "direct_decomp A ss" and "\<And>s. s \<in> set ss \<Longrightarrow> subspace s"
  shows "span (\<Union>(some_basis ` set ss)) = A"
proof -
  from assms(1) have eq0[symmetric]: "sum_list ` listset ss = A" by (rule direct_decompD)
  show ?thesis unfolding eq0 using assms(2)
  proof (induct ss)
    case Nil
    show ?case by simp
  next
    case (Cons s ss)
    have "subspace s" by (rule Cons.prems) simp
    hence eq1: "span (some_basis s) = s" by (rule span_some_basis)
    have "\<And>s'. s' \<in> set ss \<Longrightarrow> subspace s'" by (rule Cons.prems) simp
    hence eq2: "span (\<Union> (some_basis ` set ss)) = sum_list ` listset ss" by (rule Cons.hyps)
    have "span (\<Union> (some_basis ` set (s # ss))) = {x + y |x y. x \<in> s \<and> y \<in> sum_list ` listset ss}"
      by (simp add: span_Un eq1 eq2)
    also have "\<dots> = sum_list ` listset (s # ss)" (is "?A = ?B")
    proof
      show "?A \<subseteq> ?B"
      proof
        fix a
        assume "a \<in> ?A"
        then obtain x y where "x \<in> s" and "y \<in> sum_list ` listset ss" and a: "a = x + y" by blast
        from this(2) obtain qs where "qs \<in> listset ss" and y: "y = sum_list qs" ..
        from \<open>x \<in> s\<close> this(1) refl have "x # qs \<in> listset (s # ss)" by (rule listset_ConsI)
        hence "sum_list (x # qs) \<in> ?B" by (rule imageI)
        also have "sum_list (x # qs) = a" by (simp add: a y)
        finally show "a \<in> ?B" .
      qed
    next
      show "?B \<subseteq> ?A"
      proof
        fix a
        assume "a \<in> ?B"
        then obtain qs' where "qs' \<in> listset (s # ss)" and a: "a = sum_list qs'" ..
        from this(1) obtain x qs where "x \<in> s" and "qs \<in> listset ss" and qs': "qs' = x # qs"
          by (rule listset_ConsE)
        from this(2) have "sum_list qs \<in> sum_list ` listset ss" by (rule imageI)
        moreover have "a = x + sum_list qs" by (simp add: a qs')
        ultimately show "a \<in> ?A" using \<open>x \<in> s\<close> by blast
      qed
    qed
    finally show ?case .
  qed
qed

lemma direct_decomp_independent_some_basis:
  assumes "direct_decomp A ss" and "\<And>s. s \<in> set ss \<Longrightarrow> subspace s"
  shows "independent (\<Union>(some_basis ` set ss))"
  using assms
proof (induct ss arbitrary: A)
  case Nil
  from independent_empty show ?case by simp
next
  case (Cons s ss)
  have 1: "\<And>s'. s' \<in> set ss \<Longrightarrow> subspace s'" by (rule Cons.prems) simp
  have "subspace s" by (rule Cons.prems) simp
  hence "0 \<in> s" and eq1: "span (some_basis s) = s" by (rule subspace_0, rule span_some_basis)
  from Cons.prems(1) have *: "direct_decomp A ([s] @ ss)" by simp
  moreover from \<open>0 \<in> s\<close> have "{} \<notin> set [s]" by auto
  ultimately have 2: "direct_decomp (sum_list ` listset ss) ss" by (rule direct_decomp_appendD)
  hence eq2: "span (\<Union> (some_basis ` set ss)) = sum_list ` listset ss" using 1
    by (rule direct_decomp_span_some_basis)

  note independent_some_basis[of s]
  moreover from 2 1 have "independent (\<Union> (some_basis ` set ss))" by (rule Cons.hyps)
  moreover have "span (some_basis s) \<inter> span (\<Union> (some_basis ` set ss)) = {0}"
  proof -
    from * have "direct_decomp A [sum_list ` listset [s], sum_list ` listset ss]"
      by (rule direct_decomp_appendD)
    hence "direct_decomp A [s, sum_list ` listset ss]" by (simp add: image_image)
    moreover have "0 < (1::nat)" by simp
    moreover have "1 < length [s, sum_list ` listset ss]" by simp
    ultimately have "[s, sum_list ` listset ss] ! 0 \<inter> [s, sum_list ` listset ss] ! 1 = {0}"
      by (rule direct_decomp_Int_zero) (auto simp: \<open>0 \<in> s\<close> eq2[symmetric] span_zero)
    thus ?thesis by (simp add: eq1 eq2)
  qed
  ultimately have "independent (some_basis s \<union> (\<Union> (some_basis ` set ss)))"
    by (rule independent_UnI)
  thus ?case by simp
qed

corollary direct_decomp_is_basis:
  assumes "direct_decomp A ss" and "\<And>s. s \<in> set ss \<Longrightarrow> subspace s"
  shows "is_basis A (\<Union>(some_basis ` set ss))"
proof -
  from assms have "subspace A" by (rule subspace_direct_decomp)
  moreover from assms have "span (\<Union>(some_basis ` set ss)) = A"
    by (rule direct_decomp_span_some_basis)
  moreover from assms have "independent (\<Union>(some_basis ` set ss))"
    by (rule direct_decomp_independent_some_basis)
  ultimately show ?thesis by (simp add: is_basis_alt)
qed

lemma dim_direct_decomp:
  assumes "direct_decomp A ss" and "finite B" and "A \<subseteq> span B" and "\<And>s. s \<in> set ss \<Longrightarrow> subspace s"
  shows "dim A = (\<Sum>s\<in>set ss. dim s)"
proof -
  from assms(1, 4) have "is_basis A (\<Union>(some_basis ` set ss))"
    (is "is_basis A ?B") by (rule direct_decomp_is_basis)
  hence "dim A = card ?B" and "independent ?B" and "?B \<subseteq> A" by (simp_all add: is_basis_def)
  from this(3) assms(3) have "?B \<subseteq> span B" by (rule subset_trans)
  with assms(2) \<open>independent ?B\<close> have "finite ?B" using independent_span_bound by blast
  note \<open>dim A = card ?B\<close>
  also from finite_set have "card ?B = (\<Sum>s\<in>set ss. card (some_basis s))"
  proof (intro card_UN_disjoint ballI impI)
    fix s
    assume "s \<in> set ss"
    with \<open>finite ?B\<close> show "finite (some_basis s)" by auto
  next
    fix s1 s2
    have "pairwise (\<lambda>s t. disjnt (some_basis s) (some_basis t)) (set ss)"
      using assms(1, 4) by (rule direct_decomp_some_basis_pairwise_disjnt)
    moreover assume "s1 \<in> set ss" and "s2 \<in> set ss" and "s1 \<noteq> s2"
    thm pairwiseD
    ultimately have "disjnt (some_basis s1) (some_basis s2)" by (rule pairwiseD)
    thus "some_basis s1 \<inter> some_basis s2 = {}" by (simp only: disjnt_def)
  qed
  also from refl card_some_basis have "\<dots> = (\<Sum>s\<in>set ss. dim s)" by (rule sum.cong)
  finally show ?thesis .
qed

end (* vector_space *)

subsection \<open>Homogeneous Sets of Polynomials with Fixed Degree\<close>

lemma homogeneous_set_direct_decomp:
  assumes "direct_decomp A ss" and "\<And>s. s \<in> set ss \<Longrightarrow> homogeneous_set s"
  shows "homogeneous_set A"
proof (rule homogeneous_setI)
  fix a n
  assume "a \<in> A"
  with assms(1) obtain qs where "qs \<in> listset ss" and a: "a = sum_list qs" by (rule direct_decompE)
  have "hom_component a n = hom_component (sum_list qs) n" by (simp only: a)
  also have "\<dots> = sum_list (map (\<lambda>q. hom_component q n) qs)"
    by (induct qs) (simp_all add: hom_component_plus)
  also from assms(1) have "\<dots> \<in> A"
  proof (rule direct_decompD)
    show "map (\<lambda>q. hom_component q n) qs \<in> listset ss"
    proof (rule listset_closed_map)
      fix s q
      assume "s \<in> set ss"
      hence "homogeneous_set s" by (rule assms(2))
      moreover assume "q \<in> s"
      ultimately show "hom_component q n \<in> s" by (rule homogeneous_setD)
    qed fact
  qed
  finally show "hom_component a n \<in> A" .
qed

definition hom_deg_set :: "nat \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a) set \<Rightarrow> (('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::zero) set"
  where "hom_deg_set z A = (\<lambda>a. hom_component a z) ` A"

lemma hom_deg_setD:
  assumes "p \<in> hom_deg_set z A"
  shows "homogeneous p" and "p \<noteq> 0 \<Longrightarrow> poly_deg p = z"
proof -
  from assms obtain a where "a \<in> A" and p: "p = hom_component a z" unfolding hom_deg_set_def ..
  show *: "homogeneous p" by (simp only: p homogeneous_hom_component)

  assume "p \<noteq> 0"
  hence "keys p \<noteq> {}" by simp
  then obtain t where "t \<in> keys p" by blast
  with * have "deg_pm t = poly_deg p" by (rule homogeneousD_poly_deg)
  moreover from \<open>t \<in> keys p\<close> have "deg_pm t = z" unfolding p by (rule keys_hom_componentD)
  ultimately show "poly_deg p = z" by simp
qed

lemma zero_in_hom_deg_set:
  assumes "0 \<in> A"
  shows "0 \<in> hom_deg_set z A"
proof -
  have "0 = hom_component 0 z" by simp
  also from assms have "\<dots> \<in> hom_deg_set z A" unfolding hom_deg_set_def by (rule imageI)
  finally show ?thesis .
qed

lemma hom_deg_set_closed_uminus:
  assumes "\<And>a. a \<in> A \<Longrightarrow> - a \<in> A" and "p \<in> hom_deg_set z A"
  shows "- p \<in> hom_deg_set z A"
proof -
  from assms(2) obtain a where "a \<in> A" and p: "p = hom_component a z" unfolding hom_deg_set_def ..
  from this(1) have "- a \<in> A" by (rule assms(1))
  moreover have "- p = hom_component (- a) z" by (simp add: p)
  ultimately show ?thesis unfolding hom_deg_set_def by (rule rev_image_eqI)
qed

lemma hom_deg_set_closed_plus:
  assumes "\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> a1 + a2 \<in> A"
    and "p \<in> hom_deg_set z A" and "q \<in> hom_deg_set z A"
  shows "p + q \<in> hom_deg_set z A"
proof -
  from assms(2) obtain a1 where "a1 \<in> A" and p: "p = hom_component a1 z" unfolding hom_deg_set_def ..
  from assms(3) obtain a2 where "a2 \<in> A" and q: "q = hom_component a2 z" unfolding hom_deg_set_def ..
  from \<open>a1 \<in> A\<close> this(1) have "a1 + a2 \<in> A" by (rule assms(1))
  moreover have "p + q = hom_component (a1 + a2) z" by (simp only: p q hom_component_plus)
  ultimately show ?thesis unfolding hom_deg_set_def by (rule rev_image_eqI)
qed

lemma hom_deg_set_closed_minus:
  assumes "\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> a1 - a2 \<in> A"
    and "p \<in> hom_deg_set z A" and "q \<in> hom_deg_set z A"
  shows "p - q \<in> hom_deg_set z A"
proof -
  from assms(2) obtain a1 where "a1 \<in> A" and p: "p = hom_component a1 z" unfolding hom_deg_set_def ..
  from assms(3) obtain a2 where "a2 \<in> A" and q: "q = hom_component a2 z" unfolding hom_deg_set_def ..
  from \<open>a1 \<in> A\<close> this(1) have "a1 - a2 \<in> A" by (rule assms(1))
  moreover have "p - q = hom_component (a1 - a2) z" by (simp only: p q hom_component_minus)
  ultimately show ?thesis unfolding hom_deg_set_def by (rule rev_image_eqI)
qed

lemma hom_deg_set_closed_scalar:
  assumes "\<And>a. a \<in> A \<Longrightarrow> c \<cdot> a \<in> A" and "p \<in> hom_deg_set z A"
  shows "(c::'a::semiring_0) \<cdot> p \<in> hom_deg_set z A"
proof -
  from assms(2) obtain a where "a \<in> A" and p: "p = hom_component a z" unfolding hom_deg_set_def ..
  from this(1) have "c \<cdot> a \<in> A" by (rule assms(1))
  moreover have "c \<cdot> p = hom_component (c \<cdot> a) z"
    by (simp add: p punit.map_scale_eq_monom_mult hom_component_monom_mult)
  ultimately show ?thesis unfolding hom_deg_set_def by (rule rev_image_eqI)
qed

lemma hom_deg_set_closed_sum:
  assumes "0 \<in> A" and "\<And>a1 a2. a1 \<in> A \<Longrightarrow> a2 \<in> A \<Longrightarrow> a1 + a2 \<in> A"
    and "\<And>i. i \<in> I \<Longrightarrow> f i \<in> hom_deg_set z A"
  shows "sum f I \<in> hom_deg_set z A"
  using assms(3)
proof (induct I rule: infinite_finite_induct)
  case (infinite I)
  with assms(1) show ?case by (simp add: zero_in_hom_deg_set)
next
  case empty
  with assms(1) show ?case by (simp add: zero_in_hom_deg_set)
next
  case (insert j I)
  from insert.hyps(1, 2) have "sum f (insert j I) = f j + sum f I" by simp
  also from assms(2) have "\<dots> \<in> hom_deg_set z A"
  proof (intro hom_deg_set_closed_plus insert.hyps)
    show "f j \<in> hom_deg_set z A" by (rule insert.prems) simp
  next
    fix i
    assume "i \<in> I"
    hence "i \<in> insert j I" by simp
    thus "f i \<in> hom_deg_set z A" by (rule insert.prems)
  qed
  finally show ?case .
qed

lemma hom_deg_set_subset: "homogeneous_set A \<Longrightarrow> hom_deg_set z A \<subseteq> A"
  by (auto dest: homogeneous_setD simp: hom_deg_set_def)

lemma Polys_closed_hom_deg_set:
  assumes "A \<subseteq> P[X]"
  shows "hom_deg_set z A \<subseteq> P[X]"
proof
  fix p
  assume "p \<in> hom_deg_set z A"
  then obtain p' where "p' \<in> A" and p: "p = hom_component p' z" unfolding hom_deg_set_def ..
  from this(1) assms have "p' \<in> P[X]" ..
  have "keys p \<subseteq> keys p'" by (simp add: p keys_hom_component)
  also from \<open>p' \<in> P[X]\<close> have "\<dots> \<subseteq> .[X]" by (rule PolysD)
  finally show "p \<in> P[X]" by (rule PolysI)
qed

lemma hom_deg_set_alt_homogeneous_set:
  assumes "homogeneous_set A"
  shows "hom_deg_set z A = {p \<in> A. homogeneous p \<and> (p = 0 \<or> poly_deg p = z)}" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix h
    assume "h \<in> ?A"
    also from assms have "\<dots> \<subseteq> A" by (rule hom_deg_set_subset)
    finally show "h \<in> ?B" using \<open>h \<in> ?A\<close> by (auto dest: hom_deg_setD)
  qed
next
  show "?B \<subseteq> ?A"
  proof
    fix h
    assume "h \<in> ?B"
    hence "h \<in> A" and "homogeneous h" and "h = 0 \<or> poly_deg h = z" by simp_all
    from this(3) show "h \<in> ?A"
    proof
      assume "h = 0"
      with \<open>h \<in> A\<close> have "0 \<in> A" by simp
      thus ?thesis unfolding \<open>h = 0\<close> by (rule zero_in_hom_deg_set)
    next
      assume "poly_deg h = z"
      with \<open>homogeneous h\<close> have "h = hom_component h z" by (simp add: hom_component_of_homogeneous)
      with \<open>h \<in> A\<close> show ?thesis unfolding hom_deg_set_def by (rule rev_image_eqI)
    qed
  qed
qed

lemma hom_deg_set_sum_list_listset:
  assumes "A = sum_list ` listset ss"
  shows "hom_deg_set z A = sum_list ` listset (map (hom_deg_set z) ss)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix h
    assume "h \<in> ?A"
    then obtain a where "a \<in> A" and h: "h = hom_component a z" unfolding hom_deg_set_def ..
    from this(1) obtain qs where "qs \<in> listset ss" and a: "a = sum_list qs" unfolding assms ..
    have "h = hom_component (sum_list qs) z" by (simp only: a h)
    also have "\<dots> = sum_list (map (\<lambda>q. hom_component q z) qs)"
      by (induct qs) (simp_all add: hom_component_plus)
    also have "\<dots> \<in> ?B"
    proof (rule imageI)
      show "map (\<lambda>q. hom_component q z) qs \<in> listset (map (hom_deg_set z) ss)"
        unfolding hom_deg_set_def using \<open>qs \<in> listset ss\<close> refl by (rule listset_map_imageI)
    qed
    finally show "h \<in> ?B" .
  qed
next
  show "?B \<subseteq> ?A"
  proof
    fix h
    assume "h \<in> ?B"
    then obtain qs where "qs \<in> listset (map (hom_deg_set z) ss)" and h: "h = sum_list qs" ..
    from this(1) obtain qs' where "qs' \<in> listset ss" and qs: "qs = map (\<lambda>q. hom_component q z) qs'"
      unfolding hom_deg_set_def by (rule listset_map_imageE)
    have "h = sum_list (map (\<lambda>q. hom_component q z) qs')" by (simp only: h qs)
    also have "\<dots> = hom_component (sum_list qs') z" by (induct qs') (simp_all add: hom_component_plus)
    finally have "h = hom_component (sum_list qs') z" .
    moreover have "sum_list qs' \<in> A" unfolding assms using \<open>qs' \<in> listset ss\<close> by (rule imageI)
    ultimately show "h \<in> ?A" unfolding hom_deg_set_def by (rule image_eqI)
  qed
qed

lemma direct_decomp_hom_deg_set:
  assumes "direct_decomp A ss" and "\<And>s. s \<in> set ss \<Longrightarrow> homogeneous_set s"
  shows "direct_decomp (hom_deg_set z A) (map (hom_deg_set z) ss)"
proof (rule direct_decompI)
  from assms(1) have "sum_list ` listset ss = A" by (rule direct_decompD)
  from this[symmetric] show "sum_list ` listset (map (hom_deg_set z) ss) = hom_deg_set z A"
    by (simp only: hom_deg_set_sum_list_listset)
next
  from assms(1) have "inj_on sum_list (listset ss)" by (rule direct_decompD)
  moreover have "listset (map (hom_deg_set z) ss) \<subseteq> listset ss"
  proof (rule listset_mono)
    fix i
    assume "i < length ss"
    hence "map (hom_deg_set z) ss ! i = hom_deg_set z (ss ! i)" by simp
    also from \<open>i < length ss\<close> have "\<dots> \<subseteq> ss ! i" by (intro hom_deg_set_subset assms(2) nth_mem)
    finally show "map (hom_deg_set z) ss ! i \<subseteq> ss ! i" .
  qed simp
  ultimately show "inj_on sum_list (listset (map (hom_deg_set z) ss))" by (rule inj_on_subset)
qed

subsection \<open>Interpreting Polynomial Rings as Vector Spaces over the Coefficient Field\<close>

text \<open>There is no need to set up any further interpretation, since interpretation \<open>phull\<close> is exactly
  what we need.\<close>

lemma subspace_ideal: "phull.subspace (ideal (F::('b::comm_powerprod \<Rightarrow>\<^sub>0 'a::field) set))"
  using ideal.span_zero ideal.span_add
proof (rule phull.subspaceI)
  fix c p
  assume "p \<in> ideal F"
  thus "c \<cdot> p \<in> ideal F" unfolding map_scale_eq_times by (rule ideal.span_scale)
qed

lemma subspace_Polys: "phull.subspace (P[X]::(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) set)"
  using zero_in_Polys Polys_closed_plus Polys_closed_map_scale by (rule phull.subspaceI)

lemma subspace_hom_deg_set:
  assumes "phull.subspace A"
  shows "phull.subspace (hom_deg_set z A)" (is "phull.subspace ?A")
proof (rule phull.subspaceI)
  from assms have "0 \<in> A" by (rule phull.subspace_0)
  thus "0 \<in> ?A" by (rule zero_in_hom_deg_set)
next
  fix p q
  assume "p \<in> ?A" and "q \<in> ?A"
  with phull.subspace_add show "p + q \<in> ?A" by (rule hom_deg_set_closed_plus) (rule assms)
next
  fix c p
  assume "p \<in> ?A"
  with phull.subspace_scale show "c \<cdot> p \<in> ?A" by (rule hom_deg_set_closed_scalar) (rule assms)
qed

lemma hom_deg_set_Polys_eq_span:
  "hom_deg_set z P[X] = phull.span (monomial (1::'a::field) ` deg_sect X z)" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix p
    assume "p \<in> ?A"
    also from this have "\<dots> = {p \<in> P[X]. homogeneous p \<and> (p = 0 \<or> poly_deg p = z)}"
      by (simp only: hom_deg_set_alt_homogeneous_set[OF homogeneous_set_Polys])
    finally have "p \<in> P[X]" and "homogeneous p" and "p \<noteq> 0 \<Longrightarrow> poly_deg p = z" by simp_all
    thus "p \<in> ?B"
    proof (induct p rule: poly_mapping_plus_induct)
      case 1
      from phull.span_zero show ?case .
    next
      case (2 p c t)
      let ?m = "monomial c t"
      from 2(1) have "t \<in> keys ?m" by simp
      hence "t \<in> keys (?m + p)" using 2(2) by (rule in_keys_plusI1)
      hence "?m + p \<noteq> 0" by auto
      hence "poly_deg (monomial c t + p) = z" by (rule 2)
      from 2(4) have "keys (?m + p) \<subseteq> .[X]" by (rule PolysD)
      with \<open>t \<in> keys (?m + p)\<close> have "t \<in> .[X]" ..
      hence "?m \<in> P[X]" by (rule Polys_closed_monomial)
      have "t \<in> deg_sect X z"
      proof (rule deg_sectI)
        from 2(5) \<open>t \<in> keys (?m + p)\<close> have "deg_pm t = poly_deg (?m + p)"
          by (rule homogeneousD_poly_deg)
        also have "\<dots> = z" by fact
        finally show "deg_pm t = z" .
      qed fact
      hence "monomial 1 t \<in> monomial 1 ` deg_sect X z" by (rule imageI)
      hence "monomial 1 t \<in> ?B" by (rule phull.span_base)
      hence "c \<cdot> monomial 1 t \<in> ?B" by (rule phull.span_scale)
      hence "?m \<in> ?B" by simp
      moreover have "p \<in> ?B"
      proof (rule 2)
        from 2(4) \<open>?m \<in> P[X]\<close> have "(?m + p) - ?m \<in> P[X]" by (rule Polys_closed_minus)
        thus "p \<in> P[X]" by simp
      next
        have 1: "deg_pm s = z" if "s \<in> keys p" for s
        proof -
          from that 2(2) have "s \<noteq> t" by blast
          hence "s \<notin> keys ?m" by simp
          with that have "s \<in> keys (?m + p)" by (rule in_keys_plusI2)
          with 2(5) have "deg_pm s = poly_deg (?m + p)" by (rule homogeneousD_poly_deg)
          also have "\<dots> = z" by fact
          finally show ?thesis .
        qed
        show "homogeneous p" by (rule homogeneousI) (simp add: 1)

        assume "p \<noteq> 0"
        show "poly_deg p = z"
        proof (rule antisym)
          show "poly_deg p \<le> z" by (rule poly_deg_leI) (simp add: 1)
        next
          from \<open>p \<noteq> 0\<close> have "keys p \<noteq> {}" by simp
          then obtain s where "s \<in> keys p" by blast
          hence "z = deg_pm s" by (simp only: 1)
          also from \<open>s \<in> keys p\<close> have "\<dots> \<le> poly_deg p" by (rule poly_deg_max_keys)
          finally show "z \<le> poly_deg p" .
        qed
      qed
      ultimately show ?case by (rule phull.span_add)
    qed
  qed
next
  show "?B \<subseteq> ?A"
  proof
    fix p
    assume "p \<in> ?B"
    then obtain M u where "M \<subseteq> monomial 1 ` deg_sect X z" and "finite M" and p: "p = (\<Sum>m\<in>M. u m \<cdot> m)"
      by (auto simp: phull.span_explicit)
    from this(1) obtain T where "T \<subseteq> deg_sect X z" and M: "M = monomial 1 ` T"
      and inj: "inj_on (monomial (1::'a)) T" by (rule subset_imageE_inj)
    define c where "c = (\<lambda>t. u (monomial 1 t))"
    from inj have "p = (\<Sum>t\<in>T. monomial (c t) t)" by (simp add: p M sum.reindex c_def)
    also have "\<dots> \<in> ?A"
    proof (intro hom_deg_set_closed_sum zero_in_Polys Polys_closed_plus)
      fix t
      assume "t \<in> T"
      hence "t \<in> deg_sect X z" using \<open>T \<subseteq> deg_sect X z\<close> ..
      hence "t \<in> .[X]" and eq: "deg_pm t = z" by (rule deg_sectD)+
      from this(1) have "monomial (c t) t \<in> P[X]" (is "?m \<in> _") by (rule Polys_closed_monomial)
      thus "?m \<in> ?A"
        by (simp add: hom_deg_set_alt_homogeneous_set[OF homogeneous_set_Polys] poly_deg_monomial
            monomial_0_iff eq)
    qed
    finally show "p \<in> ?A" .
  qed
qed

subsection \<open>(Projective) Hilbert Function\<close>

interpretation phull: vector_space map_scale
  apply standard
  subgoal by (fact map_scale_distrib_left)
  subgoal by (fact map_scale_distrib_right)
  subgoal by (fact map_scale_assoc)
  subgoal by (fact map_scale_one_left)
  done

definition Hilbert_fun :: "(('x \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) set \<Rightarrow> nat \<Rightarrow> nat"
  where "Hilbert_fun A z = phull.dim (hom_deg_set z A)"

lemma Hilbert_fun_empty [simp]: "Hilbert_fun {} = 0"
  by (rule ext) (simp add: Hilbert_fun_def hom_deg_set_def)

lemma Hilbert_fun_zero [simp]: "Hilbert_fun {0} = 0"
  by (rule ext) (simp add: Hilbert_fun_def hom_deg_set_def)

lemma Hilbert_fun_direct_decomp:
  assumes "finite X" and "A \<subseteq> P[X]" and "direct_decomp (A::(('x::countable \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::field) set) ps"
    and "\<And>s. s \<in> set ps \<Longrightarrow> homogeneous_set s" and "\<And>s. s \<in> set ps \<Longrightarrow> phull.subspace s"
  shows "Hilbert_fun A z = (\<Sum>p\<in>set ps. Hilbert_fun p z)"
proof -
  from assms(3, 4) have dd: "direct_decomp (hom_deg_set z A) (map (hom_deg_set z) ps)"
    by (rule direct_decomp_hom_deg_set)
  have "Hilbert_fun A z = phull.dim (hom_deg_set z A)" by (fact Hilbert_fun_def)
  also from dd have "\<dots> = sum phull.dim (set (map (hom_deg_set z) ps))"
  proof (rule phull.dim_direct_decomp)
    from assms(1) have "finite (deg_sect X z)" by (rule finite_deg_sect)
    thus "finite (monomial (1::'a) ` deg_sect X z)" by (rule finite_imageI)
  next
    from assms(2) have "hom_deg_set z A \<subseteq> hom_deg_set z P[X]"
      unfolding hom_deg_set_def by (rule image_mono)
    thus "hom_deg_set z A \<subseteq> phull.span (monomial 1 ` deg_sect X z)"
      by (simp only: hom_deg_set_Polys_eq_span)
  next
    fix s
    assume "s \<in> set (map (hom_deg_set z) ps)"
    then obtain s' where "s' \<in> set ps" and s: "s = hom_deg_set z s'" unfolding set_map ..
    from this(1) have "phull.subspace s'" by (rule assms(5))
    thus "phull.subspace s" unfolding s by (rule subspace_hom_deg_set)
  qed
  also have "\<dots> = sum (phull.dim \<circ> hom_deg_set z) (set ps)" unfolding set_map using finite_set
  proof (rule sum.reindex_nontrivial)
    fix s1 s2
    note dd
    moreover assume "s1 \<in> set ps" and "s2 \<in> set ps" and "s1 \<noteq> s2"
    moreover have "0 \<in> hom_deg_set z s" if "s \<in> set ps" for s
    proof (rule zero_in_hom_deg_set)
      from that have "phull.subspace s" by (rule assms(5))
      thus "0 \<in> s" by (rule phull.subspace_0)
    qed
    ultimately have "hom_deg_set z s1 \<inter> hom_deg_set z s2 = {0}" by (rule direct_decomp_map_Int_zero)
    moreover assume "hom_deg_set z s1 = hom_deg_set z s2"
    ultimately show "phull.dim (hom_deg_set z s1) = 0" by simp
  qed
  also have "\<dots> = (\<Sum>p\<in>set ps. Hilbert_fun p z)" by (simp only: o_def Hilbert_fun_def)
  finally show ?thesis .
qed

context pm_powerprod
begin

lemma image_lt_hom_deg_set:
  assumes "homogeneous_set A"
  shows "lpp ` (hom_deg_set z A - {0}) = {t \<in> lpp ` (A - {0}). deg_pm t = z}" (is "?B = ?A")
proof (intro set_eqI iffI)
  fix t
  assume "t \<in> ?A"
  hence "t \<in> lpp ` (A - {0})" and deg_t[symmetric]: "deg_pm t = z" by simp_all
  from this(1) obtain p where "p \<in> A - {0}" and t: "t = lpp p" ..
  from this(1) have "p \<in> A" and "p \<noteq> 0" by simp_all
  from this(1) have 1: "hom_component p z \<in> hom_deg_set z A" (is "?p \<in> _")
    unfolding hom_deg_set_def by (rule imageI)
  from \<open>p \<noteq> 0\<close> have "?p \<noteq> 0" and "lpp ?p = t" unfolding t deg_t by (rule hom_component_lpp)+
  note this(2)[symmetric]
  moreover from 1 \<open>?p \<noteq> 0\<close> have "?p \<in> hom_deg_set z A - {0}" by simp
  ultimately show "t \<in> ?B" by (rule image_eqI)
next
  fix t
  assume "t \<in> ?B"
  then obtain p where "p \<in> hom_deg_set z A - {0}" and t: "t = lpp p" ..
  from this(1) have "p \<in> hom_deg_set z A" and "p \<noteq> 0" by simp_all
  with assms have "p \<in> A" and "homogeneous p" and "poly_deg p = z"
    by (simp_all add: hom_deg_set_alt_homogeneous_set)
  from this(1) \<open>p \<noteq> 0\<close> have "p \<in> A - {0}" by simp
  hence 1: "t \<in> lpp ` (A - {0})" using t by (rule rev_image_eqI)
  from \<open>p \<noteq> 0\<close> have "t \<in> keys p" unfolding t by (rule punit.lt_in_keys)
  with \<open>homogeneous p\<close> have "deg_pm t = poly_deg p" by (rule homogeneousD_poly_deg)
  with 1 show "t \<in> ?A" by (simp add: \<open>poly_deg p = z\<close>)
qed

lemma Hilbert_fun_alt:
  assumes "finite X" and "A \<subseteq> P[X]" and "phull.subspace A"
  shows "Hilbert_fun A z = card (lpp ` (hom_deg_set z A - {0}))" (is "_ = card ?A")
proof -
  have "?A \<subseteq> lpp ` (hom_deg_set z A - {0})" by simp
  then obtain B where sub: "B \<subseteq> hom_deg_set z A - {0}" and eq1: "?A = lpp ` B"
    and inj: "inj_on lpp B" by (rule subset_imageE_inj)
  have "Hilbert_fun A z = phull.dim (hom_deg_set z A)" by (fact Hilbert_fun_def)
  also have "\<dots> = card B"
  proof (rule phull.dim_eq_card)
    show "phull.span B = phull.span (hom_deg_set z A)"
    proof
      from sub have "B \<subseteq> hom_deg_set z A" by blast
      thus "phull.span B \<subseteq> phull.span (hom_deg_set z A)" by (rule phull.span_mono)
    next
      from assms(3) have "phull.subspace (hom_deg_set z A)" by (rule subspace_hom_deg_set)
      hence "phull.span (hom_deg_set z A) = hom_deg_set z A" by (simp only: phull.span_eq_iff)
      also have "\<dots> \<subseteq> phull.span B"
      proof (rule ccontr)
        assume "\<not> hom_deg_set z A \<subseteq> phull.span B"
        then obtain p0 where "p0 \<in> hom_deg_set z A - phull.span B" (is "_ \<in> ?B") by blast
        note assms(1) this
        moreover have "?B \<subseteq> P[X]"
        proof (rule subset_trans)
          from assms(2) show "hom_deg_set z A \<subseteq> P[X]" by (rule Polys_closed_hom_deg_set)
        qed blast
        ultimately obtain p where "p \<in> ?B" and p_min: "\<And>q. punit.ord_strict_p q p \<Longrightarrow> q \<notin> ?B"
          by (rule punit.ord_p_minimum_dgrad_p_set[OF dickson_grading_varnum, where m=0,
                    simplified dgrad_p_set_varnum]) blast
        from this(1) have "p \<in> hom_deg_set z A" and "p \<notin> phull.span B" by simp_all
        from phull.span_zero this(2) have "p \<noteq> 0" by blast
        with \<open>p \<in> hom_deg_set z A\<close> have "p \<in> hom_deg_set z A - {0}" by simp
        hence "lpp p \<in> lpp ` (hom_deg_set z A - {0})" by (rule imageI)
        also have "\<dots> = lpp ` B" by (simp only: eq1)
        finally obtain b where "b \<in> B" and eq2: "lpp p = lpp b" ..
        from this(1) sub have "b \<in> hom_deg_set z A - {0}" ..
        hence "b \<in> hom_deg_set z A" and "b \<noteq> 0" by simp_all
        from this(2) have lcb: "punit.lc b \<noteq> 0" by (rule punit.lc_not_0)
        from \<open>p \<noteq> 0\<close> have lcp: "punit.lc p \<noteq> 0" by (rule punit.lc_not_0)
        from \<open>b \<in> B\<close> have "b \<in> phull.span B" by (rule phull.span_base)
        hence "(punit.lc p / punit.lc b) \<cdot> b \<in> phull.span B" (is "?b \<in> _") by (rule phull.span_scale)
        with \<open>p \<notin> phull.span B\<close> have "p - ?b \<noteq> 0" by auto
        moreover from lcb lcp \<open>b \<noteq> 0\<close> have "lpp ?b = lpp p"
          by (simp add: punit.map_scale_eq_monom_mult punit.lt_monom_mult eq2)
        moreover from lcb have "punit.lc ?b = punit.lc p" by (simp add: punit.map_scale_eq_monom_mult)
        ultimately have "lpp (p - ?b) \<prec> lpp p" by (rule punit.lt_minus_lessI)
        hence "punit.ord_strict_p (p - ?b) p" by (rule punit.lt_ord_p)
        hence "p - ?b \<notin> ?B" by (rule p_min)
        hence "p - ?b \<notin> hom_deg_set z A \<or> p - ?b \<in> phull.span B" by simp
        thus False
        proof
          assume *: "p - ?b \<notin> hom_deg_set z A"
          from phull.subspace_scale have "?b \<in> hom_deg_set z A"
          proof (rule hom_deg_set_closed_scalar)
            show "phull.subspace A" by fact
          next
            show "b \<in> hom_deg_set z A" by fact
          qed
          with phull.subspace_diff \<open>p \<in> hom_deg_set z A\<close> have "p - ?b \<in> hom_deg_set z A"
            by (rule hom_deg_set_closed_minus) (rule assms(3))
          with * show ?thesis ..
        next
          assume "p - ?b \<in> phull.span B"
          hence "p - ?b + ?b \<in> phull.span B" using \<open>?b \<in> phull.span B\<close> by (rule phull.span_add)
          hence "p \<in> phull.span B" by simp
          with \<open>p \<notin> phull.span B\<close> show ?thesis ..
        qed
      qed
      finally show "phull.span (hom_deg_set z A) \<subseteq> phull.span B" .
    qed
  next
    show "phull.independent B"
    proof
      assume "phull.dependent B"
      then obtain B' u b' where "finite B'" and "B' \<subseteq> B" and "(\<Sum>b\<in>B'. u b \<cdot> b) = 0"
        and "b' \<in> B'" and "u b' \<noteq> 0" unfolding phull.dependent_explicit by blast
      define B0 where "B0 = {b \<in> B'. u b \<noteq> 0}"
      have "B0 \<subseteq> B'" by (simp add: B0_def)
      with \<open>finite B'\<close> have "(\<Sum>b\<in>B0. u b \<cdot> b) = (\<Sum>b\<in>B'. u b \<cdot> b)"
        by (rule sum.mono_neutral_left) (simp add: B0_def)
      also have "\<dots> = 0" by fact
      finally have eq: "(\<Sum>b\<in>B0. u b \<cdot> b) = 0" .
      define t where "t = ordered_powerprod_lin.Max (lpp ` B0)"
      from \<open>b' \<in> B'\<close> \<open>u b' \<noteq> 0\<close> have "b' \<in> B0" by (simp add: B0_def)
      hence "lpp b' \<in> lpp ` B0" by (rule imageI)
      hence "lpp ` B0 \<noteq> {}" by blast
      from \<open>B0 \<subseteq> B'\<close> \<open>finite B'\<close> have "finite B0" by (rule finite_subset)
      hence "finite (lpp ` B0)" by (rule finite_imageI)
      hence "t \<in> lpp ` B0" unfolding t_def using \<open>lpp ` B0 \<noteq> {}\<close>
        by (rule ordered_powerprod_lin.Max_in)
      then obtain b0 where "b0 \<in> B0" and t: "t = lpp b0" ..
      note this(1)
      moreover from \<open>B0 \<subseteq> B'\<close> \<open>B' \<subseteq> B\<close> have "B0 \<subseteq> B" by (rule subset_trans)
      also have "\<dots> \<subseteq> hom_deg_set z A - {0}" by fact
      finally have "b0 \<in> hom_deg_set z A - {0}" .
      hence "b0 \<noteq> 0" by simp
      hence "t \<in> keys b0" unfolding t by (rule punit.lt_in_keys)
      have "lookup (\<Sum>b\<in>B0. u b \<cdot> b) t = (\<Sum>b\<in>B0. u b * lookup b t)" by (simp add: lookup_sum)
      also from \<open>finite B0\<close> have "\<dots> = (\<Sum>b\<in>{b0}. u b * lookup b t)"
      proof (rule sum.mono_neutral_right)
        from \<open>b0 \<in> B0\<close> show "{b0} \<subseteq> B0" by simp
      next
        show "\<forall>b\<in>B0 - {b0}. u b * lookup b t = 0"
        proof
          fix b
          assume "b \<in> B0 - {b0}"
          hence "b \<in> B0" and "b \<noteq> b0" by simp_all
          from this(1) have "lpp b \<in> lpp ` B0" by (rule imageI)
          with \<open>finite (lpp ` B0)\<close> have "lpp b \<preceq> t" unfolding t_def
            by (rule ordered_powerprod_lin.Max_ge)
          have "t \<notin> keys b"
          proof
            assume "t \<in> keys b"
            hence "t \<preceq> lpp b" by (rule punit.lt_max_keys)
            with \<open>lpp b \<preceq> t\<close> have "lpp b = lpp b0"
              unfolding t by (rule ordered_powerprod_lin.antisym)
            from inj \<open>B0 \<subseteq> B\<close> have "inj_on lpp B0" by (rule inj_on_subset)
            hence "b = b0" using \<open>lpp b = lpp b0\<close> \<open>b \<in> B0\<close> \<open>b0 \<in> B0\<close> by (rule inj_onD)
            with \<open>b \<noteq> b0\<close> show False ..
          qed
          thus "u b * lookup b t = 0" by (simp add: in_keys_iff)
        qed
      qed
      also from \<open>t \<in> keys b0\<close> \<open>b0 \<in> B0\<close> have "\<dots> \<noteq> 0" by (simp add: B0_def in_keys_iff)
      finally show False by (simp add: eq)
    qed
  qed
  also have "\<dots> = card ?A" unfolding eq1 using inj by (rule card_image[symmetric])
  finally show ?thesis .
qed

end (* pm_powerprod *)

end (* theory *)
