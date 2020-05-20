section \<open>Partial state\<close>

theory Partial_State
  imports Quantum_Program Deep_Learning.Tensor_Matricization
begin

lemma nths_intersection_eq:
  assumes "{0..<length xs} \<subseteq> A"
  shows "nths xs B = nths xs (A \<inter> B)"
proof -
  have "\<And>x. x \<in> set (zip xs [0..<length xs]) \<Longrightarrow> snd x < length xs" 
    by (metis atLeastLessThan_iff atLeastLessThan_upt in_set_zip nth_mem)
  then have "\<And>x. x \<in> set (zip xs [0..<length xs]) \<Longrightarrow> snd x \<in> A" using assms by auto
  then have eqp: "\<And>x. x \<in> set (zip xs [0..<length xs]) \<Longrightarrow> snd x \<in> B = (snd x \<in> (A \<inter> B))" by simp
  then have "filter (\<lambda>p. snd p \<in> B) (zip xs [0..<length xs]) = filter (\<lambda>p. snd p \<in> (A \<inter> B)) (zip xs [0..<length xs])"
     using filter_cong[of "(zip xs [0..<length xs])" "(zip xs [0..<length xs])", OF _ eqp] by auto
  then show "nths xs B = nths xs (A \<inter> B)" unfolding nths_def by auto
qed

lemma nths_minus_eq:
  assumes "{0..<length xs} \<subseteq> A"
  shows "nths xs (-B) = nths xs (A - B)"
proof -
  have "\<And>x. x \<in> set (zip xs [0..<length xs]) \<Longrightarrow> snd x < length xs" 
    by (metis atLeastLessThan_iff atLeastLessThan_upt in_set_zip nth_mem)
  then have "\<And>x. x \<in> set (zip xs [0..<length xs]) \<Longrightarrow> snd x \<in> A" using assms by auto
  then have eqp: "\<And>x. x \<in> set (zip xs [0..<length xs]) \<Longrightarrow> snd x \<in> (-B) = (snd x \<in> (A - B))" by simp
  then have "filter (\<lambda>p. snd p \<in> (-B)) (zip xs [0..<length xs]) = filter (\<lambda>p. snd p \<in> (A-B)) (zip xs [0..<length xs])"
     using filter_cong[of "(zip xs [0..<length xs])" "(zip xs [0..<length xs])", OF _ eqp] by auto
   then show "nths xs (-B) = nths xs (A - B)" unfolding nths_def by auto
qed

lemma nths_split_complement_eq:
  assumes "A \<inter> B = {}"
  and "{0..<length xs} \<subseteq> A \<union> B"
shows "nths xs A = nths xs (-B)"
proof -
  have "nths xs (-B) = nths xs (A \<union> B - B)" using nths_minus_eq assms by auto
  moreover have "A \<union> B - B = A" using assms by auto
  ultimately show ?thesis by auto
qed

lemma lt_set_card_lt:
  fixes A :: "nat set"
  assumes "finite A" and "x \<in> A"
  shows "card {y. y \<in> A \<and> y < x} < card A"
proof -
  have "x \<notin> {y. y \<in> A \<and> y < x}" by auto
  then have "{y. y \<in> A \<and> y < x} \<subseteq> A - {x}" by auto
  then have "card {y. y \<in> A \<and> y < x} \<le> card (A - {x})" 
    using card_mono finite_Diff[OF assms(1)] by auto
  also have "\<dots> < card A" using card_Diff1_less[OF assms] by auto
  finally show ?thesis by auto
qed

definition ind_in_set where
  "ind_in_set A x = card {i. i \<in> A \<and> i < x}"


lemma bij_ind_in_set_bound:
  fixes M :: "nat" and v0 :: "nat set"
  assumes "\<And>x. f x = card {y. y \<in> v0 \<and> y < x}"
  shows "bij_betw f ({0..<M} \<inter> v0) {0..<card ({0..<M} \<inter> v0)}"
  unfolding bij_betw_def
proof
  let ?dom = "{0..<M} \<inter> v0"
  let ?ran = "{0..<card ({0..<M} \<inter> v0)}"
  {
    fix x1 x2 :: nat assume x1: "x1 \<in> ?dom" and x2: "x2 \<in> ?dom" and "f x1 = f x2"
    then have "card {y. y \<in> v0 \<and> y < x1} = card {y. y \<in> v0 \<and> y < x2}" using assms by auto
    then have "pick v0 (card {y. y \<in> v0 \<and> y < x1}) = pick v0 (card {y. y \<in> v0 \<and> y < x2})" by auto
    moreover have "pick v0 (card {y. y \<in> v0 \<and> y < x1}) = x1" using pick_card_in_set x1 by auto
    moreover have "pick v0 (card {y. y \<in> v0 \<and> y < x2}) = x2" using pick_card_in_set x2 by auto
    ultimately have "x1 = x2" by auto
  } 
  then show "inj_on f ?dom" unfolding inj_on_def by auto
  {
    fix x assume x: "x \<in> ?dom"
    then have "(y \<in> v0 \<and> y < x) = (y \<in> ?dom \<and> y < x)" for y using x by auto
    then have "card {y. y \<in> v0 \<and> y < x} = card {y. y \<in> ?dom \<and> y < x}" by auto
    moreover have "card {y. y \<in> ?dom \<and> y < x} < card ?dom" using x lt_set_card_lt[of ?dom] by auto
    ultimately have "f x \<in> ?ran" using assms by auto
  }
  then have sub: "(f ` ?dom) \<subseteq> ?ran" by auto
  {
    fix y assume y: "y \<in> ?ran"
    then have yle: "y < card ?dom" by auto
    then have pyindom: "pick ?dom y \<in> ?dom" using pick_in_set_le[of y ?dom] by auto
    then have "pick ?dom y < M" by auto
    then have "\<And>z. (z < pick ?dom y \<Longrightarrow> z \<in> v0 = (z \<in> ?dom))" by auto
    then have "{z. z \<in> v0 \<and> z < pick ?dom y} = {z. z \<in> ?dom \<and> z < pick ?dom y}" by auto
    then have "card {z. z \<in> v0 \<and> z < pick ?dom y} = card {z. z \<in> ?dom \<and> z < pick ?dom y}" by auto
    then have "f (pick ?dom y) = y" using card_pick_le[OF yle] assms by auto
    with pyindom have "\<exists>x\<in>?dom. f x = y" by auto
  }
  then have sup: "?ran \<subseteq> (f ` ?dom)" by fastforce
  show "(f ` ?dom) = ?ran" using sub sup by auto
qed

lemma ind_in_set_bound:
  fixes A :: "nat set" and M N :: "nat"
  assumes "N \<ge> M" 
  shows "ind_in_set A N \<notin> (ind_in_set A ` ({0..<M} \<inter> A))"
proof -
  have "{0..<M}\<inter>A \<subseteq> {i. i \<in> A \<and> i < N}" using assms by auto
  then have "card ({0..<M}\<inter>A) \<le> card {i. i \<in> A \<and> i < N}" 
    using card_mono[of "{i. i \<in> A \<and> i < N}"] by auto
  moreover have "ind_in_set A N = card {i. i \<in> A \<and> i < N}" unfolding ind_in_set_def by auto
  ultimately have "ind_in_set A N \<ge> card ({0..<M}\<inter>A)" by auto

  moreover have "y \<in> ind_in_set A ` (A \<inter> {0..<M}) \<Longrightarrow> y < card ({0..<M}\<inter>A)" for y
  proof -
    let ?dom = "{0..<M} \<inter> A"
    assume "y \<in> ind_in_set A ` (A \<inter> {0..<M})"
    then obtain x where x: "x \<in> ?dom" and y: "ind_in_set A x = y" by auto
    then have "(y \<in> A \<and> y < x) = (y \<in> ?dom \<and> y < x)" for y using x by auto
    then have "card {y. y \<in> A \<and> y < x} = card {y. y \<in> ?dom \<and> y < x}" by auto
    moreover have "card {y. y \<in> ?dom \<and> y < x} < card ?dom" using x lt_set_card_lt[of ?dom] by auto
    ultimately show "y < card ({0..<M}\<inter>A)" using y unfolding ind_in_set_def by auto
  qed
  ultimately show ?thesis by fastforce
qed

lemma bij_minus_subset:
  "bij_betw f A B \<Longrightarrow> C \<subseteq> A \<Longrightarrow> (f ` A) - (f ` C) = f ` (A - C)" 
  by (metis Diff_subset bij_betw_imp_inj_on bij_betw_imp_surj_on inj_on_image_set_diff)

lemma ind_in_set_minus_subset_bound:
  fixes A B :: "nat set" and M :: "nat"
  assumes "B \<subseteq> A"
  shows "(ind_in_set A ` ({0..<M} \<inter> A)) - (ind_in_set A ` B) = (ind_in_set A ` ({0..<M} \<inter> A)) \<inter> (ind_in_set A ` (A - B))"
proof -
  let ?dom = "{0..<M} \<inter> A"
  let ?ran = "{0..<card ({0..<M} \<inter> A)}"
  let ?f = "ind_in_set A"
  let ?C = "A - B"
  have bij: "bij_betw ?f ?dom ?ran" 
    using bij_ind_in_set_bound[of "?f" A M] unfolding ind_in_set_def by auto
  then have eq: "?f ` ?dom = ?ran" using bij_betw_imp_surj_on by fastforce

  have "(?f ` B) = (?f ` ({0..<M} \<inter> B)) \<union> (?f ` ({n. n \<ge> M} \<inter> B))"
    by fastforce
  then have "(?f ` ?dom) - (?f ` B) 
    = (?f ` ?dom) - (?f ` ({n. n \<ge> M} \<inter> B)) - (?f ` ({0..<M} \<inter> B))"
    by fastforce
  moreover have "(?f ` ({n. n \<ge> M} \<inter> B)) \<inter> (?f ` ?dom) = {}" using ind_in_set_bound[of M _ A]  by auto
  ultimately have eq1: "(?f ` ?dom) - (?f ` B) = (?f ` ?dom) - (?f ` ({0..<M} \<inter> B))" by auto
  have "{0..<M} \<inter> B \<subseteq> ?dom" using assms by auto
  then have "(?f ` ?dom) - (?f ` ({0..<M} \<inter> B)) = ?f ` (?dom - ({0..<M} \<inter> B))" 
    using bij bij_minus_subset[of "?f"] by auto
  also have "\<dots> = ?f ` ({0..<M} \<inter> ?C)" by auto
  finally have eq2: "(?f ` ?dom) - (?f ` B) = ?f ` ({0..<M} \<inter> ?C)" using eq1 by auto

  have "(?f ` ?C) = (?f ` ({0..<M} \<inter> ?C)) \<union> (?f ` ({n. n \<ge> M} \<inter> ?C))" by fastforce
  moreover have "(?f ` ({n. n \<ge> M} \<inter> ?C)) \<inter> (?f ` ?dom) = {}" using ind_in_set_bound[of M _ A]  by auto
  ultimately have eq3:"(ind_in_set A ` ?dom) \<inter> (?f ` ?C) = (ind_in_set A ` ?dom) \<inter> (?f ` ({0..<M} \<inter> ?C))" by auto

  have "{0..<M} \<inter> ?C \<subseteq> ?dom" using assms by auto
  then have "(ind_in_set A ` ?dom) \<inter> (?f ` ({0..<M} \<inter> ?C)) = (?f ` ({0..<M} \<inter> ?C))" using bij by fastforce
  then show ?thesis using eq2 eq3 by auto
qed

lemma ind_in_set_iff:
  fixes A B :: "nat set"
  assumes "x \<in> A" and "B \<subseteq> A"
  shows "ind_in_set A x \<in> (ind_in_set A ` B) = (x \<in> B)"
proof 
  have lemm: "card {i. i \<in> A \<and> i < (x::nat) } = card {i. i \<in> A \<and> i < (y::nat) } \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x = y" for A x y
    by (metis (full_types) pick_card_in_set)
  {
    assume "ind_in_set A x \<in> (ind_in_set A ` B)"
    then have "\<exists>y \<in> B. card {i \<in> A. i < x} = card {i \<in> A. i < y}" unfolding ind_in_set_def by auto
    then obtain y where y1: "y \<in> B" and ceq: "card {i \<in> A. i < x} = card {i \<in> A. i < y}" by auto
    with y1 assms have y0: "y \<in> A" by auto
    then have "x = y" using lemm[OF ceq] y0 assms by auto
    then show "x \<in> B" using y1 by auto
  }
qed (simp add: ind_in_set_def)

lemma nths_reencode_eq:
  assumes "B \<subseteq> A"
  shows "nths (nths xs A) (ind_in_set A ` B) = nths xs B"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  have seteq: "{i. i < length xs \<and> i \<in> A} = {i. i \<in> A \<and> i < length xs}" by auto

  show ?case 
  proof (cases "length xs \<in> B")
    case True
    have "nths (xs @ [x]) B = nths xs B @ nths [x] {l. l + length xs \<in> B}" using nths_append[of xs] by auto
    moreover have "nths [x] {l. l + length xs \<in> B} = [x]" using nths_singleton True by auto
    ultimately have eqT1: "nths (xs @ [x]) B = nths xs B @ [x]" by auto

    then have "length xs \<in> A" using True assms by auto
    then have "nths [x] {l. l + length xs \<in> A} = [x]" using nths_singleton by auto
    moreover have "nths (xs @ [x]) A = nths xs A @ nths [x] {l. l + length xs \<in> A}" using nths_append[of xs] by auto
    ultimately have "nths (xs @ [x]) A = nths xs A @ [x]" by auto
    then have eqT2: "nths (nths (xs @ [x]) A) (ind_in_set A ` B) = nths (nths xs A @ [x]) (ind_in_set A ` B)" by auto
    have eqT3: "nths (nths xs A @ [x]) (ind_in_set A ` B) 
      = nths xs B @ (nths [x] {l. l + length (nths xs A) \<in> (ind_in_set A ` B)})" 
      using nths_append[of "nths xs A"] snoc by auto

    have "ind_in_set A (length xs) = card {i. i < length xs \<and> i \<in> A}" using ind_in_set_def seteq by auto
    moreover have "length (nths xs A) = card {i. i < length xs \<and> i \<in> A}" using length_nths by auto
    ultimately have "length (nths xs A) = ind_in_set A (length xs)" by auto
    moreover have "ind_in_set A (length xs) \<in> ind_in_set A ` B" using True by auto
    ultimately have "length (nths xs A) \<in> ind_in_set A ` B" by auto
    then have "(nths [x] {l. l + length (nths xs A) \<in> (ind_in_set A ` B)}) = [x]" using nths_singleton by auto
    then have "nths (nths xs A @ [x]) (ind_in_set A ` B) = nths xs B @ [x]" using eqT3 by auto
    then show ?thesis using eqT1 eqT2 by auto
  next
    case False
    have "nths (xs @ [x]) B = nths xs B @ nths [x] {l. l + length xs \<in> B}" using nths_append[of xs] by auto
    moreover have "nths [x] {l. l + length xs \<in> B} = []" using nths_singleton False by auto
    ultimately have eqT1: "nths (xs @ [x]) B = nths xs B" by auto  

    have "nths (nths (xs @ [x]) A) (ind_in_set A ` B) = nths xs B"
    proof (cases "length xs \<in> A")
      case True
      then have "nths [x] {l. l + length xs \<in> A} = [x]" using nths_singleton by auto
      moreover have "nths (xs @ [x]) A = nths xs A @ nths [x] {l. l + length xs \<in> A}" using nths_append[of xs] by auto
      ultimately have "nths (xs @ [x]) A = nths xs A @ [x]" by auto
      then have "nths (nths (xs @ [x]) A) (ind_in_set A ` B) = nths (nths xs A @ [x]) (ind_in_set A ` B)" by auto
      then have eqT2: "nths (nths (xs @ [x]) A) (ind_in_set A ` B) 
        = nths xs B @ (nths [x] {l. l + length (nths xs A) \<in> (ind_in_set A ` B)})" 
        using nths_append[of "nths xs A"] snoc by auto    

      have "length (nths xs A) \<in> (ind_in_set A ` B) \<Longrightarrow> length xs \<in> B"
      proof -
        assume "length (nths xs A) \<in> (ind_in_set A ` B)"
        moreover have "length (nths xs A) = card {i. i \<in> A \<and> i < length xs}"
          using length_nths[of xs] seteq by auto
        ultimately have "card {i. i \<in> A \<and> i < length xs} \<in> (ind_in_set A ` B)" unfolding ind_in_set_def by auto
        then show "length xs \<in> B"  using ind_in_set_iff True assms unfolding ind_in_set_def by auto
      qed
      then have "length (nths xs A) \<notin> (ind_in_set A ` B)" using False by auto
      then have "nths [x] {l. l + length (nths xs A) \<in> (ind_in_set A ` B)} = []" using nths_singleton by auto
      then show "nths (nths (xs @ [x]) A) (ind_in_set A ` B) = nths xs B" using eqT2 by auto    
    next
      case False
      then have "nths [x] {l. l + length xs \<in> A} = []" using nths_singleton by auto
      moreover have "nths (xs @ [x]) A = nths xs A @ nths [x] {l. l + length xs \<in> A}" using nths_append[of xs] by auto
      ultimately have "nths (xs @ [x]) A = nths xs A" by auto
      then show ?thesis using snoc by auto
    qed
    with eqT1 show ?thesis by auto
  qed
qed

lemma nths_reencode_eq_comp:
  assumes "B \<subseteq> A"
  shows "nths (nths xs A) (- ind_in_set A ` B) = nths xs (A - B)"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  have sub20: "A - B \<subseteq> A" using assms by auto
  have seteq: "{i. i < length xs \<and> i \<in> A} = {i. i \<in> A \<and> i < length xs}" by auto
  show ?case 
  proof (cases "length xs \<in> (A - B)")
    case True
    have "nths (xs @ [x]) (A - B) = nths xs (A - B) @ nths [x] {l. l + length xs \<in> (A - B)}" using nths_append[of xs] by auto
    moreover have "nths [x] {l. l + length xs \<in> (A - B)} = [x]" using nths_singleton True by auto
    ultimately have eqT1: "nths (xs @ [x]) (A - B) = nths xs (A - B) @ [x]" by auto

    then have "length xs \<in> A" using True sub20 by auto
    then have "nths [x] {l. l + length xs \<in> A} = [x]" using nths_singleton by auto
    moreover have "nths (xs @ [x]) A = nths xs A @ nths [x] {l. l + length xs \<in> A}" using nths_append[of xs] by auto
    ultimately have "nths (xs @ [x]) A = nths xs A @ [x]" by auto
    then have "nths (nths (xs @ [x]) A) (- (ind_in_set A) ` B) = nths (nths xs A @ [x]) (- (ind_in_set A) ` B)" by auto
    then have eqT2: "nths (nths (xs @ [x]) A) (- (ind_in_set A) ` B)
      = nths xs (A - B) @ (nths [x] {l. l + length (nths xs A) \<in> (- (ind_in_set A) ` B)})" 
      using nths_append[of "nths xs A"] snoc by auto

    have "length (nths xs A) \<in> ((ind_in_set A) ` B) \<Longrightarrow> length xs \<in> B"
    proof -
      assume "length (nths xs A) \<in> ((ind_in_set A) ` B)"
      moreover have "length (nths xs A) = card {i. i \<in> A \<and> i < length xs}"
        using length_nths[of xs] seteq by auto
      ultimately have "ind_in_set A (length xs) \<in> (ind_in_set A ` B)" unfolding ind_in_set_def by auto
      then show "length xs \<in> B" using ind_in_set_iff True assms by auto
    qed
    moreover have "length xs \<notin> B" using True by auto
    ultimately have "length (nths xs A) \<in> (- (ind_in_set A) ` B)" by auto
    then have "nths [x] {l. l + length (nths xs A) \<in> (- (ind_in_set A) ` B)} = [x]"
      using nths_singleton by auto
    then have "nths (nths (xs @ [x]) A) (- (ind_in_set A) ` B) = nths xs (A - B) @ [x]" using eqT2 by auto
    then show ?thesis using eqT1 by auto
  next
    case False
    have "nths (xs @ [x]) (A - B) = nths xs (A - B) @ nths [x] {l. l + length xs \<in> (A - B)}" using nths_append[of xs] by auto
    moreover have "nths [x] {l. l + length xs \<in> (A - B)} = []" using nths_singleton False by auto
    ultimately have eqT1: "nths (xs @ [x]) (A - B) = nths xs (A - B)" by auto  

    have "nths (nths (xs @ [x]) A) (- (ind_in_set A) ` B) = nths xs (A - B)"
    proof (cases "length xs \<in> A")
      case True
      then have True1: "length xs \<in> B" using False by auto
      then have "nths [x] {l. l + length xs \<in> A} = [x]" using nths_singleton True by auto
      moreover have "nths (xs @ [x]) A = nths xs A @ nths [x] {l. l + length xs \<in> A}" using nths_append[of xs] by auto
      ultimately have "nths (xs @ [x]) A = nths xs A @ [x]" by auto
      then have "nths (nths (xs @ [x]) A) (- (ind_in_set A) ` B) = nths (nths xs A @ [x]) (- (ind_in_set A) ` B)" by auto
      then have eqT2: "nths (nths (xs @ [x]) A) (- (ind_in_set A) ` B) 
        = nths xs (A - B) @ (nths [x] {l. l + length (nths xs A) \<in> (- (ind_in_set A) ` B)})" 
        using nths_append[of "nths xs A"] snoc by auto    

      have "length (nths xs A) \<in> ((ind_in_set A) ` B)"
      proof -
        have "length (nths xs A) = card {i. i \<in> A \<and> i < length xs}"
          using length_nths[of xs] seteq by auto
        moreover have "card {i. i \<in> A \<and> i < length xs} \<in> (ind_in_set A ` B)" 
          unfolding ind_in_set_def using True ind_in_set_iff[of "length xs"] True1 by auto
        ultimately show "length (nths xs A) \<in> (ind_in_set A) ` B" by auto
      qed
      then have "nths [x] {l. l + length (nths xs A) \<in> (- (ind_in_set A) ` B)} = []" using nths_singleton by auto
      then show "nths (nths (xs @ [x]) A) (- (ind_in_set A) ` B) = nths xs (A - B)" using eqT2 by auto    
    next
      case False
      then have "nths [x] {l. l + length xs \<in> A} = []" using nths_singleton by auto
      moreover have "nths (xs @ [x]) A = nths xs A @ nths [x] {l. l + length xs \<in> A}" using nths_append[of xs] by auto
      ultimately have "nths (xs @ [x]) A = nths xs A" by auto
      then show ?thesis using snoc by auto
    qed
    with eqT1 show ?thesis by auto
  qed
qed

lemma nths_prod_list_split:
  fixes A :: "nat set" and xs :: "nat list"
  assumes "B \<subseteq> A"
  shows "prod_list (nths xs A) = (prod_list (nths xs B)) * (prod_list (nths xs (A - B)))"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by auto
next
  let ?C = "A - B"
  case (snoc x xs)
  have SA: "nths (xs @ [x]) A = nths xs A @ nths [x] {j. j + length xs \<in> A}" using nths_append[of xs] by auto
  have SB: "nths (xs @ [x]) B = nths xs B @ nths [x] {j. j + length xs \<in> B}" using nths_append[of xs] by auto
  have SC: "nths (xs @ [x]) ?C = nths xs ?C @ nths [x] {j. j + length xs \<in> ?C}" using nths_append[of xs] by auto
  show ?case 
  proof (cases "length xs \<in> A")
    case True
    then have "nths (xs @ [x]) A = nths xs A @ [x]" using SA by auto
    then have eqA: "prod_list (nths (xs @ [x]) A) = prod_list (nths xs A) * x"  by auto
    show ?thesis
    proof (cases "length xs \<in> B")
      case True
      then have "nths (xs @ [x]) B = nths xs B @ [x]" using SB by auto
      then have eqB: "prod_list (nths (xs @ [x]) B) = prod_list (nths xs B) * x"  by auto
      have "length xs \<notin> ?C" using True assms by auto
      then have "nths (xs @ [x]) ?C = nths xs ?C" using SC by auto
      then have eqC: "prod_list (nths (xs @ [x]) ?C) = prod_list (nths xs ?C)" by auto
      then show ?thesis using snoc eqA eqB eqC by auto
    next
      case False
      then have "nths (xs @ [x]) B = nths xs B" using SB by auto
      then have eqB: "prod_list (nths (xs @ [x]) B) = prod_list (nths xs B)"  by auto    
      then have "length xs \<in> ?C" using True False assms by auto
      then have "nths (xs @ [x]) ?C = nths xs ?C @ [x]" using SC by auto
      then have eqC: "prod_list (nths (xs @ [x]) ?C) = prod_list (nths xs ?C) * x" by auto
      then show ?thesis using snoc eqA eqB eqC by auto
    qed
  next
    case False
    then have ninB: "length xs \<notin> B" and ninC: "length xs \<notin> ?C" using assms by auto

    have "nths (xs @ [x]) A = nths xs A" using SA False nths_singleton by auto
    then have eqA: "prod_list (nths (xs @ [x]) A) = prod_list (nths xs A)" by auto
    have "nths (xs @ [x]) B = nths xs B" using SB ninB nths_singleton by auto
    then have eqB: "prod_list (nths (xs @ [x]) B) = prod_list (nths xs B)" by auto
    have "nths (xs @ [x]) ?C = nths xs ?C" using SC ninC nths_singleton by auto
    then have eqC: "prod_list (nths (xs @ [x]) ?C) = prod_list (nths xs ?C)" by auto
    then show ?thesis using eqA eqB eqC snoc by auto
  qed
qed

subsection \<open>Encodings\<close>

lemma digit_encode_take:
  "take n (digit_encode ds a) = digit_encode (take n ds) a"
proof (induct n arbitrary: ds a)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
  proof (cases ds)
    case Nil
    then show ?thesis by auto
  next
    case (Cons d ds')
    then show ?thesis by (auto simp add: Suc)
  qed
qed

lemma nths_minus_upt_eq_drop:
  "nths l (-{..<n}) = drop n l"
  apply (induct l rule: rev_induct)
  by (auto simp add: nths_append)

lemma digit_encode_drop:
  "drop n (digit_encode ds a) = digit_encode (drop n ds) (a div (prod_list (take n ds)))"
proof (induct n arbitrary: ds a)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case
  proof (cases ds)
    case Nil
    then show ?thesis by auto
  next
    case (Cons d ds')
    then show ?thesis by (auto simp add: Suc div_mult2_eq)
  qed
qed

text \<open>List of active variables in the partial state\<close>
locale partial_state = state_sig +
  fixes vars :: "nat set"

context partial_state
begin

text \<open>Dimensions of active variables\<close>
abbreviation avars :: "nat set" where
  "avars \<equiv> {0..<length dims}"

definition dims1 :: "nat list" where
  "dims1 = nths dims vars"

definition dims2 :: "nat list" where
  "dims2 = nths dims (-vars)"

lemma dims1_alter:
  assumes "avars \<subseteq> A"
  shows "dims1 = nths dims (A \<inter> vars)"
   using nths_intersection_eq assms unfolding dims1_def by auto

lemma dims2_alter:
  assumes "avars \<subseteq> A"
  shows "dims2 = nths dims (A-vars)"
  using nths_minus_eq assms unfolding dims2_def by auto

text \<open>Total dimension for the active variables\<close>
definition d1 :: nat where
  "d1 = prod_list dims1"

text \<open>Total dimension for the non-active variables\<close>
definition d2 :: nat where
  "d2 = prod_list dims2"

text \<open>Translating dimension in d to dimension in d1\<close>
definition encode1 :: "nat \<Rightarrow> nat" where
  "encode1 i = digit_decode dims1 (nths (digit_encode dims i) vars)"

lemma encode1_alter:
  assumes "avars \<subseteq> A"
  shows "encode1 i = digit_decode dims1 (nths (digit_encode dims i) (A \<inter> vars))"
  using length_digit_encode[of dims i] nths_intersection_eq[of "digit_encode dims i" A vars] assms unfolding encode1_def
  by (subgoal_tac "nths (digit_encode dims i) (vars) = nths (digit_encode dims i) (A \<inter> vars)", auto)

text \<open>Translating dimension in d to dimension in d2\<close>
definition encode2 :: "nat \<Rightarrow> nat" where
  "encode2 i = digit_decode dims2 (nths (digit_encode dims i) (-vars))"

lemma encode2_alter:
  assumes "avars \<subseteq> A"
  shows "encode2 i = digit_decode dims2 (nths (digit_encode dims i) (A-vars))"
  using length_digit_encode[of dims i] nths_minus_eq[of "digit_encode dims i" A] assms unfolding encode2_def
  by (subgoal_tac "nths (digit_encode dims i) (- vars) = nths (digit_encode dims i) (A - vars)", auto)

lemma encode1_lt [simp]:
  assumes "i < d"
  shows "encode1 i < d1"
  unfolding d1_def encode1_def apply (rule digit_decode_lt)
  using dims1_def assms d_def digit_encode_valid_index valid_index_nths by auto

lemma encode2_lt [simp]:
  assumes "i < d"
  shows "encode2 i < d2"
  unfolding d2_def encode2_def apply (rule digit_decode_lt)
  using dims2_def assms d_def digit_encode_valid_index valid_index_nths by auto

text \<open>Given dimensions in d1 and d2, form dimension in d\<close>
fun encode12 :: "nat \<times> nat \<Rightarrow> nat" where
  "encode12 (i, j) = digit_decode dims (weave vars (digit_encode dims1 i) (digit_encode dims2 j))"
declare encode12.simps [simp del]

lemma encode12_inv:
  assumes "k < d"
  shows "encode12 (encode1 k, encode2 k) = k"
  unfolding encode12.simps encode1_def encode2_def
  using assms d_def digit_encode_valid_index dims1_def dims2_def valid_index_nths by auto

lemma encode12_inv1:
  assumes "i < d1" "j < d2"
  shows "encode1 (encode12 (i, j)) = i"
  unfolding encode12.simps encode1_def
  using assms unfolding d1_def d2_def dims1_def dims2_def
  by (metis digit_decode_encode_lt digit_encode_decode digit_encode_valid_index valid_index_weave(1,2))

lemma encode12_inv2:
  assumes "i < d1" "j < d2"
  shows "encode2 (encode12 (i, j)) = j"
  unfolding encode12.simps encode2_def
  using assms unfolding d1_def d2_def dims1_def dims2_def
  by (metis digit_decode_encode_lt digit_encode_decode digit_encode_valid_index valid_index_weave(1,3))

lemma encode12_lt:
  assumes "i < d1" "j < d2"
  shows "encode12 (i, j) < d"
  using assms unfolding encode12.simps d_def d1_def d2_def dims1_def dims2_def
  by (simp add: digit_decode_lt digit_encode_valid_index valid_index_weave(1))

lemma sum_encode: "(\<Sum>i = 0..<d1. \<Sum>j = 0..<d2. f i j) = sum (\<lambda>k. f (encode1 k) (encode2 k)) {0..<d}"
  apply (subst sum.cartesian_product)
  apply (rule sum.reindex_bij_witness[where i="\<lambda>k. (encode1 k, encode2 k)" and j=encode12])
  by (auto simp: encode12_inv1 encode12_inv2 encode12_inv encode12_lt)

subsection \<open>Tensor product of vectors and matrices\<close>

text \<open>Given vector v1 of dimension d1, and vector v2 of dimension d2, form
  the tensor vector of dimension d1 * d2 = d\<close>
definition tensor_vec :: "'a::times vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
  "tensor_vec v1 v2 = Matrix.vec d (\<lambda>i. v1 $ encode1 i * v2 $ encode2 i)"

lemma tensor_vec_dim [simp]:
  "dim_vec (tensor_vec v1 v2) = d"
  unfolding tensor_vec_def by auto

lemma tensor_vec_carrier:
  "tensor_vec v1 v2 \<in> carrier_vec d"
  unfolding tensor_vec_def by auto

lemma tensor_vec_eval:
  assumes "i < d"
  shows "tensor_vec v1 v2 $ i = v1 $ encode1 i * v2 $ encode2 i"
  unfolding tensor_vec_def using assms by simp

lemma tensor_vec_add1:
  fixes v1 v2 v3 :: "'a::comm_ring vec"
  assumes "v1 \<in> carrier_vec d1"
    and "v2 \<in> carrier_vec d1"
    and "v3 \<in> carrier_vec d2"
  shows "tensor_vec (v1 + v2) v3 = tensor_vec v1 v3 + tensor_vec v2 v3"
  apply (rule eq_vecI, auto)
  unfolding tensor_vec_eval
  using assms(2) comm_semiring_class.distrib by force

lemma tensor_vec_add2:
  fixes v1 v2 v3 :: "'a::comm_ring vec"
  assumes "v1 \<in> carrier_vec d1"
    and "v2 \<in> carrier_vec d2"
    and "v3 \<in> carrier_vec d2"
  shows "tensor_vec v1 (v2 + v3) = tensor_vec v1 v2 + tensor_vec v1 v3"
  apply (rule eq_vecI, auto)
  unfolding tensor_vec_eval
  using assms(3) semiring_class.distrib_left by force

text \<open>Given d1-by-d1 matrix m1, and d2-by-d2 matrix m2, form d-by-d matrix\<close>
definition tensor_mat :: "'a::comm_ring_1 mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "tensor_mat m1 m2 = Matrix.mat d d (\<lambda>(i,j).
    m1 $$ (encode1 i, encode1 j) * m2 $$ (encode2 i, encode2 j))"

lemma tensor_mat_dim_row [simp]:
  "dim_row (tensor_mat m1 m2) = d"
  unfolding tensor_mat_def by auto

lemma tensor_mat_dim_col [simp]:
  "dim_col (tensor_mat m1 m2) = d"
  unfolding tensor_mat_def by auto

lemma tensor_mat_carrier:
  "tensor_mat m1 m2 \<in> carrier_mat d d"
  unfolding tensor_mat_def by auto

lemma tensor_mat_eval:
  assumes "i < d" "j < d"
  shows "tensor_mat m1 m2 $$ (i, j) = m1 $$ (encode1 i, encode1 j) * m2 $$ (encode2 i, encode2 j)"
  unfolding tensor_mat_def using assms by simp

lemma tensor_mat_zero1:
  shows "tensor_mat (0\<^sub>m d1 d1) m1 = 0\<^sub>m d d"
  apply (rule eq_matI)
  by (auto simp add: tensor_mat_eval)

lemma tensor_mat_zero2:
  shows "tensor_mat m1 (0\<^sub>m d2 d2) = 0\<^sub>m d d"
  apply (rule eq_matI)
  by (auto simp add: tensor_mat_eval)

lemma tensor_mat_add1:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d1 d1"
    and "m3 \<in> carrier_mat d2 d2"
  shows "tensor_mat (m1 + m2) m3 = tensor_mat m1 m3 + tensor_mat m2 m3"
  apply (rule eq_matI, auto)
  unfolding tensor_mat_eval
  using assms(2) comm_semiring_class.distrib by force

lemma tensor_mat_add2:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
    and "m3 \<in> carrier_mat d2 d2"
  shows "tensor_mat m1 (m2 + m3) = tensor_mat m1 m2 + tensor_mat m1 m3"
  apply (rule eq_matI, auto)
  unfolding tensor_mat_eval
  using assms(3) semiring_class.distrib_left by force

lemma tensor_mat_minus1:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d1 d1"
    and "m3 \<in> carrier_mat d2 d2"
  shows "tensor_mat (m1 - m2) m3 = tensor_mat m1 m3 - tensor_mat m2 m3"
  apply (rule eq_matI, auto)
  unfolding tensor_mat_eval
  apply (subst index_minus_mat)
  subgoal using assms by auto
  subgoal using assms by auto
  using assms(2) ring_class.left_diff_distrib by force

lemma tensor_mat_matrix_sum2:
  assumes "m1 \<in> carrier_mat d1 d1"
  shows "(\<And>k. k < n \<Longrightarrow> f k \<in> carrier_mat d2 d2)
    \<Longrightarrow> matrix_sum d (\<lambda>k. tensor_mat m1 (f k)) n = tensor_mat m1 (matrix_sum d2 f n)"
proof (induct n)
case 0
  then show ?case apply simp using tensor_mat_zero2[of m1] by auto
next
  case (Suc n)
  then have "k < n \<Longrightarrow> f k \<in> carrier_mat d2 d2" for k by auto
  then have ds: "matrix_sum d2 f n \<in> carrier_mat d2 d2" using matrix_sum_dim by auto
  have dn: "f n \<in> carrier_mat d2 d2" using Suc by auto
  have "matrix_sum d2 f (Suc n) = f n + matrix_sum d2 f n" by simp
  then have eq: "tensor_mat m1 (matrix_sum d2 f (Suc n)) 
    = tensor_mat m1 (f n) + tensor_mat m1 (matrix_sum d2 f n)"
    using tensor_mat_add2 dn ds assms by auto

  have "matrix_sum d (\<lambda>k. tensor_mat m1 (f k)) (Suc n) 
    = tensor_mat m1 (f n) + matrix_sum d (\<lambda>k. tensor_mat m1 (f k)) n" by simp
  also have "\<dots> = tensor_mat m1 (f n) + tensor_mat m1 (matrix_sum d2 f n)"
    using Suc by auto
  finally show ?case using eq by auto
qed

lemma tensor_mat_scale1:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
  shows "tensor_mat (a \<cdot>\<^sub>m m1) m2 = a \<cdot>\<^sub>m tensor_mat m1 m2"
  apply (rule eq_matI, auto)
  unfolding tensor_mat_eval
  using assms comm_semiring_class.distrib by force

lemma tensor_mat_scale2:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
  shows "tensor_mat m1 (a \<cdot>\<^sub>m m2) = a \<cdot>\<^sub>m tensor_mat m1 m2"
  apply (rule eq_matI, auto)
  unfolding tensor_mat_eval
  using assms comm_semiring_class.distrib by force

lemma tensor_mat_trace:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
  shows "trace (tensor_mat m1 m2) = trace m1 * trace m2"
  apply (auto simp add: tensor_mat_carrier trace_def tensor_mat_eval)
  apply (subst Groups_Big.sum_product)
  apply (subst sum_encode[symmetric])
  using assms by auto
  
lemma tensor_mat_id:
  "tensor_mat (1\<^sub>m d1) (1\<^sub>m d2) = 1\<^sub>m d"
proof (rule eq_matI, auto)
  show "tensor_mat (1\<^sub>m d1) (1\<^sub>m d2) $$ (i, i) = 1" if "i < d" for i
    using that by (simp add: tensor_mat_eval)
next
  show "tensor_mat (1\<^sub>m d1) (1\<^sub>m d2) $$ (i, j) = 0" if "i < d" "j < d" "i \<noteq> j" for i j
    using that apply (simp add: tensor_mat_eval)
    by (metis encode12_inv)
qed

lemma tensor_mat_mult_vec:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
    and "v1 \<in> carrier_vec d1"
    and "v2 \<in> carrier_vec d2"
  shows "tensor_vec (m1 *\<^sub>v v1) (m2 *\<^sub>v v2) = tensor_mat m1 m2 *\<^sub>v tensor_vec v1 v2"
proof (rule eq_vecI, auto)
  fix i j :: nat
  assume i: "i < d"
  let ?i1 = "encode1 i" and ?i2 = "encode2 i"
  have "tensor_vec (m1 *\<^sub>v v1) (m2 *\<^sub>v v2) $ i = (m1 *\<^sub>v v1) $ ?i1 * (m2 *\<^sub>v v2) $ ?i2"
    using i by (simp add: tensor_vec_eval)
  also have "\<dots> = (row m1 ?i1 \<bullet> v1) * (row m2 ?i2 \<bullet> v2)"
    using assms i by auto
  also have "\<dots> = (\<Sum>i = 0..<d1. m1 $$ (?i1, i) * v1 $ i) * (\<Sum>j = 0..<d2. m2 $$ (?i2, j) * v2 $ j)"
    using assms i by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>i = 0..<d1. \<Sum>j = 0..<d2. (m1 $$ (?i1, i) * v1 $ i) * (m2 $$ (?i2, j) * v2 $ j))"
    by (rule Groups_Big.sum_product)
  also have "\<dots> = (\<Sum>i = 0..<d. (m1 $$ (?i1, encode1 i) * v1 $ (encode1 i)) * (m2 $$ (?i2, encode2 i) * v2 $ (encode2 i)))"
    by (rule sum_encode)
  also have "\<dots> = row (tensor_mat m1 m2) i \<bullet> tensor_vec v1 v2"
    apply (simp add: scalar_prod_def tensor_mat_eval tensor_vec_eval i)
    by (rule sum.cong, auto)
  finally show "tensor_vec (m1 *\<^sub>v v1) (m2 *\<^sub>v v2) $ i = row (tensor_mat m1 m2) i \<bullet> tensor_vec v1 v2" by auto
qed

lemma tensor_mat_mult:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d1 d1"
    and "m3 \<in> carrier_mat d2 d2"
    and "m4 \<in> carrier_mat d2 d2"
  shows "tensor_mat (m1 * m2) (m3 * m4) = tensor_mat m1 m3 * tensor_mat m2 m4"
proof (rule eq_matI, auto)
  fix i j :: nat
  assume i: "i < d" and j: "j < d"
  let ?i1 = "encode1 i" and ?i2 = "encode2 i" and ?j1 = "encode1 j" and ?j2 = "encode2 j"
  have "tensor_mat (m1 * m2) (m3 * m4) $$ (i, j) = (m1 * m2) $$ (?i1, ?j1) * (m3 * m4) $$ (?i2, ?j2)"
    using i j by (simp add: tensor_mat_eval)
  also have "\<dots> = (row m1 ?i1 \<bullet> col m2 ?j1) * (row m3 ?i2 \<bullet> col m4 ?j2)"
    using assms i j by auto
  also have "\<dots> = (\<Sum>i = 0..<d1. m1 $$ (?i1, i) * m2 $$ (i, ?j1)) * (\<Sum>j = 0..<d2. m3 $$ (?i2, j) * m4 $$ (j, ?j2))"
    using assms i j by (simp add: scalar_prod_def)
  also have "\<dots> = (\<Sum>i = 0..<d1. \<Sum>j = 0..<d2. (m1 $$ (?i1, i) * m2 $$ (i, ?j1)) * (m3 $$ (?i2, j) * m4 $$ (j, ?j2)))"
    by (rule Groups_Big.sum_product)
  also have "\<dots> = (\<Sum>i = 0..<d. (m1 $$ (?i1, encode1 i) * m2 $$ (encode1 i, ?j1)) * (m3 $$ (?i2, encode2 i) * m4 $$ (encode2 i, ?j2)))"
    by (rule sum_encode)
  also have "\<dots> = row (tensor_mat m1 m3) i \<bullet> col (tensor_mat m2 m4) j"
    apply (simp add: scalar_prod_def tensor_mat_eval i j)
    by (rule sum.cong, auto)
  finally show "tensor_mat (m1 * m2) (m3 * m4) $$ (i, j) = row (tensor_mat m1 m3) i \<bullet> col (tensor_mat m2 m4) j" .
qed

lemma tensor_mat_adjoint:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
  shows "adjoint (tensor_mat m1 m2) = tensor_mat (adjoint m1) (adjoint m2)"
  apply (rule eq_matI, auto)
  unfolding tensor_mat_def adjoint_def
  using assms by (simp add: conjugate_dist_mul)

lemma tensor_mat_hermitian:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
    and "hermitian m1"
    and "hermitian m2"
  shows "hermitian (tensor_mat m1 m2)"
  using assms by (metis hermitian_def tensor_mat_adjoint)

lemma tensor_mat_unitary:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
    and "unitary m1"
    and "unitary m2"
  shows "unitary (tensor_mat m1 m2)"
  using assms apply (auto simp add: unitary_def tensor_mat_adjoint)
  using assms unfolding inverts_mat_def
  apply (subst tensor_mat_mult[symmetric], auto)
  by (rule tensor_mat_id)

lemma tensor_mat_positive:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
    and "positive m1"
    and "positive m2"
  shows "positive (tensor_mat m1 m2)"
proof -
  obtain M1 where M1: "m1 = M1 * adjoint M1" and dM1:"M1 \<in> carrier_mat d1 d1" using positive_only_if_decomp assms by auto
  obtain M2 where M2: "m2 = M2 * adjoint M2" and dM2:"M2 \<in> carrier_mat d2 d2" using positive_only_if_decomp assms by auto
  have "(adjoint (tensor_mat M1 M2)) = tensor_mat (adjoint M1) (adjoint M2)" using tensor_mat_adjoint dM1 dM2 by auto
  then have "tensor_mat M1 M2 * (adjoint (tensor_mat M1 M2)) = tensor_mat (M1 * adjoint M1) (M2 * adjoint M2)"
    using dM1 dM2 adjoint_dim[OF dM1] adjoint_dim[OF dM2] by (auto simp add: tensor_mat_mult)
  also have "\<dots> = tensor_mat m1 m2" using M1 M2 by auto
  finally have "tensor_mat m1 m2 = tensor_mat M1 M2 * (adjoint (tensor_mat M1 M2))"..
  then have "\<exists>M. M * adjoint M = tensor_mat m1 m2" by auto
  moreover have "tensor_mat m1 m2 \<in> carrier_mat d d" using tensor_mat_carrier by auto
  ultimately show ?thesis using positive_if_decomp[of "tensor_mat m1 m2"] by auto
qed

lemma tensor_mat_positive_le:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
    and "positive m1"
    and "positive m2"
    and "m1 \<le>\<^sub>L A"
    and "m2 \<le>\<^sub>L B"
  shows "tensor_mat m1 m2 \<le>\<^sub>L tensor_mat A B"
proof -
  have dA: "A \<in> carrier_mat d1 d1" using assms lowner_le_def by auto
  have pA: "positive A" using assms dA lowner_le_trans_positiveI[of m1] by auto
  have dB: "B \<in> carrier_mat d2 d2" using assms lowner_le_def by auto
  have pB: "positive B" using assms dB lowner_le_trans_positiveI[of m2] by auto
  have "A - m1 = A + (- m1)" using assms by (auto simp add: minus_add_uminus_mat)
  then have "positive (A + (- m1))" using assms unfolding lowner_le_def by auto
  then have p1: "positive (tensor_mat (A + (- m1)) m2)" using assms tensor_mat_positive by auto
  moreover have "tensor_mat (- m1) m2 = - tensor_mat m1 m2" using assms apply (subgoal_tac "- m1 = -1 \<cdot>\<^sub>m m1")
    by (auto simp add: tensor_mat_scale1)
  moreover have "tensor_mat (A + (- m1)) m2 = tensor_mat A m2 + (tensor_mat (- m1) m2)" using
      assms by (auto simp add: tensor_mat_add1 dA)
  ultimately have "tensor_mat (A + (- m1)) m2 = tensor_mat A m2 - (tensor_mat m1 m2)" by auto
  with p1 have le1: "tensor_mat m1 m2 \<le>\<^sub>L tensor_mat A m2" unfolding lowner_le_def by auto

  have "B - m2 = B + (- m2)" using assms by (auto simp add: minus_add_uminus_mat)
  then have "positive (B + (- m2))" using assms unfolding lowner_le_def by auto
  then have p2: "positive (tensor_mat A (B + (- m2)))" 
    using assms tensor_mat_positive positive_one dA dB pA by auto
  moreover have "tensor_mat A (-m2) = - tensor_mat A m2" 
    using assms apply (subgoal_tac "- m2 = -1 \<cdot>\<^sub>m m2")
    by (auto simp add: tensor_mat_scale2 dA)
  moreover have "tensor_mat A (B + (- m2)) = tensor_mat A B + tensor_mat A (- m2)"
    using assms by (auto simp add: tensor_mat_add2 dA dB)
  ultimately have "tensor_mat A (B + (- m2)) = tensor_mat A B - tensor_mat A m2" by auto
  with p2 have le20: "tensor_mat A m2 \<le>\<^sub>L tensor_mat A B" unfolding lowner_le_def by auto

  show ?thesis apply (subst lowner_le_trans[of _ d "tensor_mat (A) m2"])
    subgoal using tensor_mat_carrier by auto
    subgoal using tensor_mat_carrier by auto
    using le1 le20 by auto
qed

lemma tensor_mat_le_one:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
    and "positive m1"
    and "positive m2"
    and "m1 \<le>\<^sub>L 1\<^sub>m d1"
    and "m2 \<le>\<^sub>L 1\<^sub>m d2"
  shows "tensor_mat m1 m2 \<le>\<^sub>L 1\<^sub>m d"
proof -
  have "1\<^sub>m d1 - m1 = 1\<^sub>m d1 + (- m1)" using assms by (auto simp add: minus_add_uminus_mat)
  then have "positive (1\<^sub>m d1 + (- m1))" using assms unfolding lowner_le_def by auto
  then have p1: "positive (tensor_mat (1\<^sub>m d1 + (- m1)) m2)" using assms tensor_mat_positive by auto
  moreover have "tensor_mat (- m1) m2 = - tensor_mat m1 m2" using assms apply (subgoal_tac "- m1 = -1 \<cdot>\<^sub>m m1")
    by (auto simp add: tensor_mat_scale1)
  moreover have "tensor_mat (1\<^sub>m d1 + (- m1)) m2 = tensor_mat (1\<^sub>m d1) m2 + (tensor_mat (- m1) m2)" using
      assms by (auto simp add: tensor_mat_add1)
  ultimately have "tensor_mat (1\<^sub>m d1 + (- m1)) m2 = tensor_mat (1\<^sub>m d1) m2 - (tensor_mat m1 m2)" by auto
  with p1 have le1: "(tensor_mat m1 m2) \<le>\<^sub>L tensor_mat (1\<^sub>m d1) m2" unfolding lowner_le_def by auto

  have "1\<^sub>m d2 - m2 = 1\<^sub>m d2 + (- m2)" using assms by (auto simp add: minus_add_uminus_mat)
  then have "positive (1\<^sub>m d2 + (- m2))" using assms unfolding lowner_le_def by auto
  then have p2: "positive (tensor_mat (1\<^sub>m d1) (1\<^sub>m d2 + (- m2)))" using assms tensor_mat_positive positive_one by auto
  moreover have "tensor_mat (1\<^sub>m d1) (-m2) = - tensor_mat (1\<^sub>m d1) m2" using assms apply (subgoal_tac "- m2 = -1 \<cdot>\<^sub>m m2")
    by (auto simp add: tensor_mat_scale2)
  moreover have "tensor_mat (1\<^sub>m d1) (1\<^sub>m d2 + (- m2)) = tensor_mat (1\<^sub>m d1) (1\<^sub>m d2) + (tensor_mat (1\<^sub>m d1) (- m2))" using
      assms by (auto simp add: tensor_mat_add2)
  ultimately have "tensor_mat (1\<^sub>m d1) (1\<^sub>m d2 + (- m2)) = tensor_mat (1\<^sub>m d1) (1\<^sub>m d2) - (tensor_mat (1\<^sub>m d1) m2)" by auto
  with p2 have le20: "tensor_mat (1\<^sub>m d1) m2 \<le>\<^sub>L tensor_mat (1\<^sub>m d1) (1\<^sub>m d2)" unfolding lowner_le_def by auto
  then have le2: "tensor_mat (1\<^sub>m d1) m2 \<le>\<^sub>L 1\<^sub>m d" apply (subst tensor_mat_id[symmetric]) by auto
  have "tensor_mat (1\<^sub>m d1) (1\<^sub>m d2) = 1\<^sub>m d" using tensor_mat_id by auto

  show ?thesis apply (subst lowner_le_trans[of _ d "tensor_mat (1\<^sub>m d1) m2"])
    subgoal using tensor_mat_carrier by auto
    subgoal using tensor_mat_carrier by auto
    using le1 le2 by auto
qed

subsection \<open>Extension of matrices\<close>

definition mat_extension :: "'a::comm_ring_1 mat \<Rightarrow> 'a mat" where
  "mat_extension m = tensor_mat m (1\<^sub>m d2)"

lemma mat_extension_carrier:
  "mat_extension m \<in> carrier_mat d d"
  by (simp add: mat_extension_def tensor_mat_carrier)

lemma mat_extension_add:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d1 d1"
  shows "mat_extension (m1 + m2) = mat_extension m1 + mat_extension m2"
  using assms by (simp add: mat_extension_def tensor_mat_add1)

lemma mat_extension_trace:
  assumes "m \<in> carrier_mat d1 d1"
  shows "trace (mat_extension m) = d2 * trace m"
  unfolding mat_extension_def
  using assms by (simp add: tensor_mat_trace)

lemma mat_extension_id:
  "mat_extension (1\<^sub>m d1) = 1\<^sub>m d"
  unfolding mat_extension_def by (rule tensor_mat_id)

lemma mat_extension_mult:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d1 d1"
  shows "mat_extension (m1 * m2) = mat_extension m1 * mat_extension m2"
  using assms by (simp add: mat_extension_def tensor_mat_mult[symmetric])

lemma mat_extension_hermitian:
  assumes "m \<in> carrier_mat d1 d1"
    and "hermitian m"
  shows "hermitian (mat_extension m)"
  using assms by (simp add: hermitian_one mat_extension_def tensor_mat_hermitian)

lemma mat_extension_unitary:
  assumes "m \<in> carrier_mat d1 d1"
    and "unitary m"
  shows "unitary (mat_extension m)"
  using assms by (simp add: mat_extension_def tensor_mat_unitary unitary_one)

end

abbreviation "tensor_mat \<equiv> partial_state.tensor_mat"
abbreviation "mat_extension \<equiv> partial_state.mat_extension"

context state_sig
begin

text \<open>Swapping the order of matrices, as well as switching vars, should have no effect\<close>

lemma tensor_mat_comm:
  assumes "vars1 \<inter> vars2 = {}"
    and "{0..<length dims} \<subseteq> vars1 \<union> vars2"
    and "m1 \<in> carrier_mat (prod_list (nths dims vars1)) (prod_list (nths dims vars1))"
    and "m2 \<in> carrier_mat (prod_list (nths dims vars2)) (prod_list (nths dims vars2))"
  shows "tensor_mat dims vars1 m1 m2 = tensor_mat dims vars2 m2 m1"
proof -
  {
  fix i
  have "nths dims (- vars2) = nths dims vars1" using nths_split_complement_eq[symmetric] assms by auto
  then have eq2211: "partial_state.dims2 dims vars2 = partial_state.dims1 dims vars1" 
    unfolding partial_state.dims2_def partial_state.dims1_def by auto
  have "nths dims (- vars1) = nths dims vars2" using nths_split_complement_eq[symmetric, of vars2] assms by auto
  then have eq2112: "partial_state.dims2 dims vars1 = partial_state.dims1 dims vars2" 
    unfolding partial_state.dims2_def partial_state.dims1_def by auto

  have "vars1 \<union> vars2 - vars2 = vars1" using assms by auto
  then have e1:"partial_state.encode2 dims vars2 i = partial_state.encode1 dims (vars1) i"
    using assms(2) partial_state.encode2_alter[of dims "vars1 \<union> vars2" vars2]
    unfolding partial_state.encode2_def partial_state.encode1_def apply (subst eq2211[symmetric]) by auto

  have "vars1 \<union> vars2 - vars1 = vars2" using assms by auto
  then have e2:"partial_state.encode2 dims vars1 i = partial_state.encode1 dims (vars2) i"
    using assms(2) partial_state.encode2_alter[of dims "vars1 \<union> vars2" vars1]
    unfolding partial_state.encode2_def partial_state.encode1_def apply (subst eq2112[symmetric]) by auto

  note e1 e2
  }
  note e = this
  show ?thesis
  unfolding partial_state.tensor_mat_def apply (rule cong_mat, simp_all)
  unfolding partial_state.dims1_def partial_state.dims2_def
  using e by auto
qed
end

subsection \<open>Partial tensor product\<close>

text \<open>In this context, we assume two disjoint sets of variables, and define
  the tensor product of two matrices on these variables\<close>

locale partial_state2 = state_sig + 
  fixes vars1 :: "nat set"
    and vars2 :: "nat set"
  assumes disjoint: "vars1 \<inter> vars2 = {}"

begin

definition vars0 :: "nat set" where
  "vars0 = vars1 \<union> vars2"

definition dims0 :: "nat list" where
  "dims0 = nths dims vars0"

definition dims1 :: "nat list" where
  "dims1 = nths dims vars1"

definition dims2 :: "nat list" where
  "dims2 = nths dims vars2"

definition d0 :: nat where
  "d0 = prod_list dims0"

definition d1 :: nat where
  "d1 = prod_list dims1"

definition d2 :: nat where
  "d2 = prod_list dims2"

lemma dims_product:
  "d0 = d1 * d2"
  unfolding d0_def d1_def d2_def dims0_def dims1_def dims2_def vars0_def
  using disjoint nths_prod_list_split[of vars1 "vars1 \<union> vars2" dims]
  apply (subgoal_tac "vars1 \<union> vars2 - vars1 = vars2")
  by auto

text \<open>Locations of variables in vars1 relative to vars0.
  For example: if vars0 = {0,1,2,4,5,6,9} and vars1 = {1,4,6,9}, then
  vars1' should be {1,3,5,6}.\<close>

definition vars1' :: "nat set" where
  "vars1' = (ind_in_set vars0) ` vars1"

definition vars2' :: "nat set" where
  "vars2' = (ind_in_set vars0) ` vars2"

lemma vars1'I:
  "x \<in> vars1 \<Longrightarrow> card {y\<in>vars0. y < x} \<in> vars1'"
  unfolding vars1'_def ind_in_set_def by auto

lemma vars1'D:
  "i \<in> vars1' \<Longrightarrow> \<exists>x\<in>vars1. card {y\<in>vars0. y < x} = i"
  unfolding vars1'_def ind_in_set_def by auto

text \<open>Main property of vars1'\<close>

lemma ind_in_set_bij:
  "bij_betw (ind_in_set vars0) ({0..<length dims} \<inter> vars0) {0..<card ({0..<length dims} \<inter> vars0)}"
  using bij_ind_in_set_bound unfolding ind_in_set_def by auto

lemma length_dims0:
  "length dims0 = card ({0..<length dims} \<inter> vars0)"
  unfolding dims0_def using length_nths[of dims vars0] 
  apply (subgoal_tac "{i. i < length dims \<and> i \<in> vars0}= {0..<length dims} \<inter> vars0")
  by auto

lemma length_dims0_minus_vars2'_is_vars1':
  "{0..<length dims0} - vars2' = {0..<length dims0} \<inter> vars1'"
proof -
  have sub20: "vars2 \<subseteq> vars0" unfolding vars0_def by auto
  have sub1: "vars1 = vars0 - vars2" unfolding vars0_def using disjoint by auto
  have eq: "{0..<length dims0} = ind_in_set vars0 ` ({0..<length dims} \<inter> vars0)"
    using ind_in_set_bij length_dims0 bij_betw_imp_surj_on[of "ind_in_set vars0"] by auto
  show ?thesis unfolding vars2'_def vars1'_def eq using ind_in_set_minus_subset_bound[OF sub20] sub1 by auto
qed

lemma length_dims0_minus_vars1'_is_vars2':
  "{0..<length dims0} - vars1' = {0..<length dims0} \<inter> vars2'"
proof -
  have sub10: "vars1 \<subseteq> vars0" unfolding vars0_def by auto
  have sub2: "vars2 = vars0 - vars1" unfolding vars0_def using disjoint by auto
  have eq: "{0..<length dims0} = ind_in_set vars0 ` ({0..<length dims} \<inter> vars0)"
    using ind_in_set_bij length_dims0 bij_betw_imp_surj_on[of "ind_in_set vars0"] by auto
  show ?thesis unfolding vars2'_def vars1'_def eq using ind_in_set_minus_subset_bound[OF sub10] sub2 by auto
qed

lemma nths_vars1':
  "nths dims0 vars1' = dims1" 
  using nths_reencode_eq[of vars1 vars0 dims] 
    using nths_reencode_eq_comp[of vars1 vars0 dims] 
  unfolding vars0_def ind_in_set_def vars1'_def dims1_def dims0_def by auto

lemma nths_vars1'_comp:
  "nths dims0 (-vars2') = dims1" 
  using nths_reencode_eq_comp[of vars2 vars0 dims] disjoint
  unfolding vars0_def ind_in_set_def vars2'_def dims1_def dims0_def 
  apply (subgoal_tac "(vars1 \<union> vars2 - vars2) = vars1") by auto

lemma nths_vars2':
  "nths dims0 (-vars1') = dims2" 
  using nths_reencode_eq_comp[of vars1 vars0 dims] disjoint
  unfolding vars0_def ind_in_set_def vars1'_def dims2_def dims0_def 
  apply (subgoal_tac "(vars1 \<union> vars2 - vars1) = vars2") by auto

lemma nths_vars2'_comp:
  "nths dims0 (vars2') = dims2" 
  using nths_reencode_eq[of vars2 vars0 dims] 
  unfolding vars0_def ind_in_set_def vars2'_def dims2_def dims0_def 
  by auto

lemma ptensor_encode1_encode2:
  "partial_state.encode1 dims0 vars1' = partial_state.encode2 dims0 vars2'"
proof -
  have "partial_state.encode1 dims0 vars1' i 
    = digit_decode (partial_state.dims1 dims0 vars1') (nths (digit_encode dims0 i) ({0..<length dims0} \<inter> vars1'))" for i
    using partial_state.encode1_alter by auto
  moreover have "partial_state.encode2 dims0 vars2' i 
    = digit_decode (partial_state.dims2 dims0 vars2') (nths (digit_encode dims0 i) ({0..<length dims0} - vars2'))" for i
    using partial_state.encode2_alter by auto
  moreover have "partial_state.dims1 dims0 vars1' = partial_state.dims2 dims0 vars2'"
    unfolding partial_state.dims1_def partial_state.dims2_def using nths_vars1' nths_vars1'_comp by auto
  ultimately show ?thesis using length_dims0_minus_vars2'_is_vars1' by auto
qed

lemma ptensor_encode2_encode1:
  "partial_state.encode1 dims0 vars2' = partial_state.encode2 dims0 vars1'"
proof -
  have "partial_state.encode1 dims0 vars2' i 
    = digit_decode (partial_state.dims1 dims0 vars2') (nths (digit_encode dims0 i) ({0..<length dims0} \<inter> vars2'))" for i
    using partial_state.encode1_alter by auto
  moreover have "partial_state.encode2 dims0 vars1' i 
    = digit_decode (partial_state.dims2 dims0 vars1') (nths (digit_encode dims0 i) ({0..<length dims0} - vars1'))" for i
    using partial_state.encode2_alter by auto
  moreover have "partial_state.dims1 dims0 vars2' = partial_state.dims2 dims0 vars1'"
    unfolding partial_state.dims1_def partial_state.dims2_def using nths_vars2' nths_vars2'_comp by auto
  ultimately show ?thesis using length_dims0_minus_vars1'_is_vars2' by auto
qed

text \<open>Given vector v1 of dimension d1, and vector v2 of dimension d2, form
  the tensor vector of dimension d1 * d2 = d0\<close>
definition ptensor_vec :: "'a::times vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" where
  "ptensor_vec v1 v2 = partial_state.tensor_vec dims0 vars1' v1 v2"

lemma ptensor_vec_dim [simp]:
  "dim_vec (ptensor_vec v1 v2) = d0"
  by (simp add: ptensor_vec_def partial_state.tensor_vec_dim state_sig.d_def d0_def)

lemma ptensor_vec_carrier:
  "ptensor_vec v1 v2 \<in> carrier_vec d0"
  by (simp add: carrier_dim_vec)

lemma ptensor_vec_add:
  fixes v1 v2 v3 :: "'a::comm_ring vec"
  assumes "v1 \<in> carrier_vec d1"
    and "v2 \<in> carrier_vec d1"
    and "v3 \<in> carrier_vec d2"
  shows "ptensor_vec (v1 + v2) v3 = ptensor_vec v1 v3 + ptensor_vec v2 v3"
  unfolding ptensor_vec_def
  apply (rule partial_state.tensor_vec_add1)
  unfolding partial_state.d1_def partial_state.d2_def
    partial_state.dims1_def partial_state.dims2_def nths_vars1' nths_vars2'
  using assms unfolding d1_def d2_def by auto

definition ptensor_mat :: "'a::comm_ring_1 mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "ptensor_mat m1 m2 = partial_state.tensor_mat dims0 vars1' m1 m2"

lemma ptensor_mat_dim_row [simp]:
  "dim_row (ptensor_mat m1 m2) = d0"
  by (simp add: ptensor_mat_def partial_state.tensor_mat_dim_row d0_def state_sig.d_def)

lemma ptensor_mat_dim_col [simp]:
  "dim_col (ptensor_mat m1 m2) = d0"
  by (simp add: ptensor_mat_def partial_state.tensor_mat_dim_col d0_def state_sig.d_def)

lemma ptensor_mat_carrier:
  "ptensor_mat m1 m2 \<in> carrier_mat d0 d0"
  by (simp add: carrier_matI)

lemma ptensor_mat_add:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d1 d1"
    and "m3 \<in> carrier_mat d2 d2"
  shows "ptensor_mat (m1 + m2) m3 = ptensor_mat m1 m3 + ptensor_mat m2 m3"
  unfolding ptensor_mat_def
  apply (rule partial_state.tensor_mat_add1)
  unfolding partial_state.d1_def partial_state.d2_def
    partial_state.dims1_def partial_state.dims2_def nths_vars1'
    nths_vars2'
  using assms unfolding d1_def d2_def by auto

lemma ptensor_mat_trace:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d2 d2"
  shows "trace (ptensor_mat m1 m2) = trace m1 * trace m2"
  unfolding ptensor_mat_def
  apply (rule partial_state.tensor_mat_trace)
  unfolding partial_state.d1_def partial_state.d2_def
    partial_state.dims1_def partial_state.dims2_def nths_vars1' nths_vars2'
  using assms unfolding d1_def d2_def by auto

lemma ptensor_mat_id:
  "ptensor_mat (1\<^sub>m d1) (1\<^sub>m d2) = 1\<^sub>m d0"
  unfolding ptensor_mat_def
  by (metis d0_def d1_def d2_def nths_vars1' nths_vars2'
      partial_state.d1_def partial_state.d2_def partial_state.dims1_def
      partial_state.dims2_def partial_state.tensor_mat_id state_sig.d_def)

lemma ptensor_mat_mult:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d1 d1"
    and "m3 \<in> carrier_mat d2 d2"
    and "m4 \<in> carrier_mat d2 d2"
  shows "ptensor_mat (m1 * m2) (m3 * m4) = ptensor_mat m1 m3 * ptensor_mat m2 m4"
proof -
  interpret st: partial_state dims0 vars1'.
  have "st.d1 = d1" unfolding st.d1_def st.dims1_def d1_def nths_vars1' by auto
  moreover have "st.d2 = d2" unfolding st.d2_def st.dims2_def d2_def nths_vars2' by auto 
  ultimately show ?thesis unfolding ptensor_mat_def
    using st.tensor_mat_mult assms by auto
qed

lemma ptensor_mat_mult_vec:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "v1 \<in> carrier_vec d1"
    and "m2 \<in> carrier_mat d2 d2"
    and "v2 \<in> carrier_vec d2"
  shows "ptensor_vec (m1 *\<^sub>v v1) (m2 *\<^sub>v v2) = ptensor_mat m1 m2 *\<^sub>v ptensor_vec v1 v2"
proof -
  interpret st: partial_state dims0 vars1'.
  have "st.d1 = d1" unfolding st.d1_def st.dims1_def d1_def nths_vars1' by auto
  moreover have "st.d2 = d2" unfolding st.d2_def st.dims2_def d2_def nths_vars2' by auto 
  ultimately show ?thesis unfolding ptensor_mat_def ptensor_vec_def
    using st.tensor_mat_mult_vec assms by auto
qed

subsection \<open>Partial extensions\<close>

definition pmat_extension :: "'a::comm_ring_1 mat \<Rightarrow> 'a mat" where
  "pmat_extension m = ptensor_mat m (1\<^sub>m d2)"

lemma pmat_extension_carrier:
  "pmat_extension m \<in> carrier_mat d0 d0"
  by (simp add: pmat_extension_def ptensor_mat_carrier)

lemma pmat_extension_add:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d1 d1"
  shows "pmat_extension (m1 + m2) = pmat_extension m1 + pmat_extension m2"
  using assms by (simp add: pmat_extension_def ptensor_mat_add)

lemma pmat_extension_trace:
  assumes "m \<in> carrier_mat d1 d1"
  shows "trace (pmat_extension m) = d2 * trace m"
  using assms by (simp add: pmat_extension_def ptensor_mat_trace)

lemma pmat_extension_id:
  "pmat_extension (1\<^sub>m d1) = 1\<^sub>m d0"
  by (simp add: pmat_extension_def ptensor_mat_id)

lemma pmat_extension_mult:
  assumes "m1 \<in> carrier_mat d1 d1"
    and "m2 \<in> carrier_mat d1 d1"
  shows "pmat_extension (m1 * m2) = pmat_extension m1 * pmat_extension m2"
  using assms by (simp add: pmat_extension_def ptensor_mat_mult[symmetric])

end

context state_sig
begin

abbreviation "ptensor_vec \<equiv> partial_state2.ptensor_vec"
abbreviation "ptensor_mat \<equiv> partial_state2.ptensor_mat"
abbreviation "pmat_extension \<equiv> partial_state2.pmat_extension"

text \<open>Key property: commutativity of tensor product\<close>

lemma ptensor_mat_comm:
  fixes m1 m2 :: "complex mat"
  assumes "vars1 \<inter> vars2 = {}"
  shows "ptensor_mat dims vars1 vars2 m1 m2 = ptensor_mat dims vars2 vars1 m2 m1"  
proof -
  interpret st1: partial_state2 dims vars1 vars2
    apply unfold_locales using assms by auto
  interpret st2: partial_state2 dims vars2 vars1
    apply unfold_locales using assms by auto

  have eq1: "partial_state.encode1 st1.dims0 st1.vars1' = partial_state.encode2 st2.dims0 st2.vars1'"
    apply (subst st1.ptensor_encode1_encode2) 
    unfolding st1.dims0_def st1.vars0_def st1.vars2'_def st2.dims0_def st2.vars0_def st2.vars1'_def
    by (subgoal_tac "vars1 \<union> vars2 = vars2 \<union> vars1", auto)
  have eq2: "partial_state.encode2 st1.dims0 st1.vars1' = partial_state.encode1 st2.dims0 st2.vars1'"
    apply (subst st1.ptensor_encode2_encode1[symmetric])
    unfolding st1.dims0_def st1.vars0_def st1.vars2'_def st2.dims0_def st2.vars0_def st2.vars1'_def
    by (subgoal_tac "vars1 \<union> vars2 = vars2 \<union> vars1", auto)

  show ?thesis unfolding st1.ptensor_mat_def st2.ptensor_mat_def partial_state.tensor_mat_def
    apply (rule cong_mat, auto)
    subgoal unfolding st1.dims0_def st1.vars0_def st2.dims0_def st2.vars0_def by (subgoal_tac "vars1 \<union> vars2 = vars2 \<union> vars1", auto)
    subgoal unfolding st1.dims0_def st1.vars0_def st2.dims0_def st2.vars0_def by (subgoal_tac "vars1 \<union> vars2 = vars2 \<union> vars1", auto)
    using eq1 eq2 by auto
qed

text \<open>Key property: associativity of tensor product\<close>

lemma ind_in_set_mono:
  fixes a b :: nat and A :: "nat set"
  assumes "a \<in> A" "b \<in> A" "a < b"
  shows "ind_in_set A a < ind_in_set A b"
  unfolding ind_in_set_def
  apply (rule psubset_card_mono)
  subgoal by auto
proof -
  have "x \<in> {i \<in> A. i < b}" if "x \<in> {i \<in> A. i < a}" for x
    using assms that by auto
  moreover have "a \<in> {i \<in> A. i < b}" using assms by auto
  moreover have "b \<notin> {i \<in> A. i < b}" by auto
  ultimately show "{i \<in> A. i < a} \<subset> {i \<in> A. i < b}" by blast
qed

lemma ind_in_set_inj:
  fixes a b :: nat and A :: "nat set"
  assumes "a \<in> A" "b \<in> A" "ind_in_set A a = ind_in_set A b"
  shows "a = b"
proof -
  have "ind_in_set A a < ind_in_set A b" if "a < b"
    by (rule ind_in_set_mono[OF assms(1) assms(2) that])
  moreover have "ind_in_set A b < ind_in_set A a" if "b < a"
    by (rule ind_in_set_mono[OF assms(2) assms(1) that])
  ultimately show ?thesis using assms(3) by arith
qed

lemma ind_in_set_mono2:
  fixes a b :: nat and A :: "nat set"
  assumes "a \<in> A" "b \<in> A" "ind_in_set A a < ind_in_set A b"
  shows "a < b"
  using ind_in_set_mono ind_in_set_inj
  by (metis assms not_less_iff_gr_or_eq)

lemma ind_in_set_bij_betw:
  fixes A B :: "nat set"
  assumes "B \<subseteq> A" "c \<in> B"
  shows "bij_betw (ind_in_set A) {i \<in> B. i < c} {i \<in> ind_in_set A ` B. i < ind_in_set A c}"
  unfolding bij_betw_def apply auto
proof -
  show "inj_on (ind_in_set A) {i \<in> B. i < c}"
    unfolding inj_on_def apply auto
    using assms(1) ind_in_set_inj by blast
  show "ind_in_set A x < ind_in_set A c" if "x \<in> B" "x < c" for x
    by (meson assms that ind_in_set_mono subsetCE)
  show "ind_in_set A x \<in> ind_in_set A ` {i \<in> B. i < c}" if "ind_in_set A x < ind_in_set A c" "x \<in> B" for x
    using that ind_in_set_mono2 assms by blast
qed    

lemma ind_in_set_assoc:
  fixes A B C :: "nat set"
  assumes "C \<subseteq> B" "B \<subseteq> A"
  shows "ind_in_set (ind_in_set A ` B) ` (ind_in_set A ` C) = ind_in_set B ` C"
proof -
  have "x \<in> ind_in_set (ind_in_set A ` B) ` (ind_in_set A ` C)" if x: "x \<in> ind_in_set B ` C" for x
  proof -
    obtain c where c: "c \<in> C" and x_eq: "x = card {i \<in> B. i < c}"
      using x by (auto simp add: ind_in_set_def)
    have "card {i \<in> B. i < c} = card {i \<in> ind_in_set A ` B. i < ind_in_set A c}"
      apply (rule bij_betw_same_card)
      using c assms by (auto intro: ind_in_set_bij_betw)
    then have "ind_in_set (ind_in_set A ` B) (ind_in_set A c) = x"
      apply (subst ind_in_set_def) using x_eq by auto
    then show ?thesis
      using \<open>c \<in> C\<close> by blast
  qed
  moreover have "x \<in> ind_in_set B ` C" if x: "x \<in> ind_in_set (ind_in_set A ` B) ` (ind_in_set A ` C)" for x
  proof -
    obtain c where c: "c \<in> C" and x_eq: "x = card {i \<in> ind_in_set A ` B. i < ind_in_set A c}"
      using x by (auto simp add: ind_in_set_def)
    have "card {i \<in> B. i < c} = card {i \<in> ind_in_set A ` B. i < ind_in_set A c}"
      apply (rule bij_betw_same_card)
      using c assms by (auto intro: ind_in_set_bij_betw)
    then have "ind_in_set B c = x"
      apply (subst ind_in_set_def) using x_eq by auto
    then show ?thesis
      using \<open>c \<in> C\<close> by blast
  qed
  ultimately show ?thesis by auto
qed
    
lemma nths_reencode_eq3:
  fixes A B C :: "nat set"
  assumes "C \<subseteq> B" "B \<subseteq> A"
  shows "nths (nths xs (ind_in_set A ` B)) (ind_in_set B ` C) = nths xs (ind_in_set A ` C)"
  apply (subst ind_in_set_assoc[OF assms, symmetric])
  apply (rule nths_reencode_eq)
  using assms by blast

lemma nths_assoc_three_A:
  fixes A B C :: "nat set"
  assumes "A \<inter> B = {}"
    and "(A \<union> B) \<inter> C = {}"
  shows "nths (nths xs (ind_in_set (A \<union> B \<union> C) ` (A \<union> B))) (ind_in_set (A \<union> B) ` A)
       = nths xs (ind_in_set (A \<union> B \<union> C) ` A)"
  apply (rule nths_reencode_eq3) by auto

lemma nths_assoc_three_B:
  fixes A B C :: "nat set"
  assumes "A \<inter> B = {}"
    and "(A \<union> B) \<inter> C = {}"
  shows "nths (nths xs (ind_in_set (A \<union> B \<union> C) ` (A \<union> B))) (ind_in_set (A \<union> B) ` B)
       = nths (nths xs (ind_in_set (A \<union> B \<union> C) ` (B \<union> C))) (ind_in_set (B \<union> C) ` B)"
proof -
  have "nths (nths xs (ind_in_set (A \<union> B \<union> C) ` (A \<union> B))) (ind_in_set (A \<union> B) ` B) = nths xs (ind_in_set (A \<union> B \<union> C) ` B)"
    using nths_assoc_three_A[of B A C xs] assms by (simp add: inf_commute sup_commute)
  moreover have "nths (nths xs (ind_in_set (A \<union> B \<union> C) ` (B \<union> C))) (ind_in_set (B \<union> C) ` B) = nths xs (ind_in_set (A \<union> B \<union> C) ` B)" 
    using nths_assoc_three_A[of B C A xs] assms by (smt Un_empty inf_commute inf_sup_distrib2 sup_assoc sup_commute)
  ultimately show ?thesis by auto
qed

lemma nths_assoc_three_C:
  fixes A B C :: "nat set"
  assumes "A \<inter> B = {}"
    and "(A \<union> B) \<inter> C = {}"
  shows "nths (nths xs (ind_in_set (A \<union> B \<union> C) ` (B \<union> C))) (ind_in_set (B \<union> C) ` C)
    = nths xs (ind_in_set (A \<union> B \<union> C) ` C) "
  using nths_assoc_three_A[of C B A xs] assms
  by (smt Un_empty inf_commute inf_sup_distrib2 sup_assoc sup_commute)

lemma valid_index_ind_in_set:
  assumes "is \<lhd> nths dims A" "B \<subseteq> A"
  shows "nths is (ind_in_set A ` B) \<lhd> nths dims B"
  apply (subst nths_reencode_eq[OF assms(2), symmetric])
  apply (rule valid_index_nths)
  by (rule assms(1))

lemma ind_in_set_id:
  fixes A :: "nat set"
  assumes "finite A"
  shows "ind_in_set A ` A = {0..< card A}"
  unfolding ind_in_set_def apply auto
  subgoal using assms lt_set_card_lt by auto
proof -
  fix x assume x: "x < card A"
  have *: "card {i \<in> A. i < pick A x} = x"
    apply (rule card_pick_le) by (rule x)
  show "x \<in> (\<lambda>x. card {i \<in> A. i < x}) ` A"
    apply (subst *[symmetric])
    apply (rule imageI)
    apply (rule pick_in_set_le) by (rule x)
qed

lemma nths_complement_ind_in_set:
  fixes A B :: "nat set"
  assumes "A \<inter> B = {}"
    "card (A \<union> B) = length xs"
  shows "nths xs (- ind_in_set (A \<union> B) ` A) = nths xs (ind_in_set (A \<union> B) ` B)"
  apply (rule nths_split_complement_eq[symmetric])
  subgoal apply auto using assms(1) ind_in_set_inj
    by (metis disjoint_iff_not_equal subsetCE sup_ge1 sup_ge2)
proof -
  have *: "ind_in_set (A \<union> B) ` B \<union> ind_in_set (A \<union> B) ` A = ind_in_set (A \<union> B) ` (A \<union> B)"
    by auto
  show "{0..<length xs} \<subseteq> ind_in_set (A \<union> B) ` B \<union> ind_in_set (A \<union> B) ` A"
    apply (auto simp add: * assms(2))
    using ind_in_set_id
    by (metis assms(2) atLeastLessThan_iff card_infinite not_le_imp_less not_less_zero)
qed

lemma ind_in_set_inj':
  fixes A B :: "nat set"
  assumes "B \<subseteq> A"
  shows "inj_on (ind_in_set A) B"
proof (rule inj_onI)
  fix x y assume x: "x \<in> B" and y: "y \<in> B" and eq: "ind_in_set A x = ind_in_set A y"
  have x': "x \<in> A" using x assms by auto
  have y': "y \<in> A" using y assms by auto
  show "x = y" by (rule ind_in_set_inj[OF x' y' eq])
qed

lemma ind_in_set_less:
  fixes x :: nat and A :: "nat set"
  assumes "finite A" "x \<in> A"
  shows "ind_in_set A x < card A"
  unfolding ind_in_set_def
  apply (rule psubset_card_mono) using assms by auto

lemma ptensor_mat_assoc:
  assumes "vars1 \<inter> vars2 = {}"
    and "(vars1 \<union> vars2) \<inter> vars3 = {}"
    and "vars1 \<union> vars2 \<union> vars3 \<subseteq> {0..< length dims}"
  shows "ptensor_mat dims (vars1 \<union> vars2) vars3 (ptensor_mat dims vars1 vars2 m1 m2) m3 =
         ptensor_mat dims vars1 (vars2 \<union> vars3) m1 (ptensor_mat dims vars2 vars3 m2 m3)"
proof -
  interpret a: partial_state2 dims vars1 vars2
    by (unfold_locales, rule assms(1))
  interpret b: partial_state2 dims "vars1 \<union> vars2" vars3
    by (unfold_locales, rule assms(2))
  interpret c: partial_state2 dims vars2 vars3
    apply unfold_locales using assms(2) by auto
  interpret d: partial_state2 dims vars1 "vars2 \<union> vars3"
    apply unfold_locales using assms by auto

  have uassoc: "vars1 \<union> (vars2 \<union> vars3) = vars1 \<union> vars2 \<union> vars3"
    by auto

  have **: "{i. i < length dims \<and> (i \<in> vars1 \<or> i \<in> vars2 \<or> i \<in> vars3)} = vars1 \<union> vars2 \<union> vars3"
    using assms(3) by auto

  have finite_union: "finite (vars1 \<union> vars2 \<union> vars3)"
    using assms(3)
    using subset_eq_atLeast0_lessThan_finite by blast

  have m1eq: "digit_encode a.dims0 (digit_decode b.dims1 (nths (digit_encode b.dims0 i) b.vars1')) 
    = nths (digit_encode b.dims0 i) b.vars1'" if "i < state_sig.d b.dims0" for i
    unfolding a.dims0_def a.vars0_def b.dims1_def b.dims0_def b.vars0_def b.vars1'_def
    apply (subst digit_encode_decode)
    apply (rule valid_index_ind_in_set)
    apply (rule digit_encode_valid_index)
    using that unfolding state_sig.d_def b.dims0_def b.vars0_def by auto
  have m1index: "partial_state.encode1 a.dims0 a.vars1' (partial_state.encode1 b.dims0 b.vars1' i) 
    = partial_state.encode1 d.dims0 d.vars1' i" if "i < state_sig.d b.dims0" for i
    unfolding partial_state.encode1_def partial_state.dims1_def a.nths_vars1' d.nths_vars1' b.nths_vars1'
    apply (rule arg_cong[where f="digit_decode d.dims1"])
    apply (subst m1eq[OF that])
    unfolding a.vars0_def a.vars1'_def b.dims0_def b.vars0_def b.vars1'_def d.dims0_def d.vars0_def d.vars1'_def
    using nths_assoc_three_A[OF assms(1-2)] using uassoc by auto

  have m2eq1: "digit_encode a.dims0 (digit_decode (nths b.dims0 b.vars1') (nths (digit_encode b.dims0 i) b.vars1'))
    = nths (digit_encode b.dims0 i) b.vars1'"
    if "i < state_sig.d b.dims0" for i
    unfolding a.dims0_def a.vars0_def b.nths_vars1' b.dims1_def
    apply (subst digit_encode_decode)
    unfolding b.vars1'_def
     apply (rule valid_index_ind_in_set)
    unfolding b.dims0_def
      apply (rule digit_encode_valid_index)
    using that unfolding state_sig.d_def b.dims0_def b.vars0_def by auto

  have m2eq2: "digit_encode c.dims0 (digit_decode (nths d.dims0 (- d.vars1')) (nths (digit_encode d.dims0 i) (- d.vars1')))
    = nths (digit_encode d.dims0 i) (- d.vars1')"
    if "i < state_sig.d b.dims0" for i
    unfolding c.dims0_def c.vars0_def d.nths_vars2' d.dims2_def
    apply (subst digit_encode_decode)
    unfolding d.vars1'_def d.vars0_def
     apply (subst nths_complement_ind_in_set)
    subgoal using assms by auto
    subgoal apply (auto simp only: length_digit_encode d.dims0_def d.vars0_def length_nths)
      by (auto simp add: ** uassoc)
     apply (rule valid_index_ind_in_set)
    unfolding d.dims0_def d.vars0_def
      apply (rule digit_encode_valid_index)
    using that unfolding state_sig.d_def b.dims0_def b.vars0_def using uassoc by auto

  have m2index: "partial_state.encode2 a.dims0 a.vars1' (partial_state.encode1 b.dims0 b.vars1' i) =
    partial_state.encode1 c.dims0 c.vars1' (partial_state.encode2 d.dims0 d.vars1' i)"
    if "i < state_sig.d b.dims0" for i
    unfolding partial_state.encode2_def partial_state.encode1_def
      partial_state.dims2_def a.nths_vars2' partial_state.dims1_def c.nths_vars1'
      a.dims2_def c.dims1_def
    apply (rule arg_cong[where f="digit_decode (nths dims vars2)"])
    apply (subst m2eq1[OF that])
    apply (subst m2eq2[OF that])
    unfolding b.dims0_def b.vars0_def b.vars1'_def a.vars1'_def a.vars0_def
      d.dims0_def d.vars0_def d.vars1'_def c.vars1'_def c.vars0_def
    apply (subst nths_complement_ind_in_set)
    subgoal using assms by auto
    subgoal apply (auto simp only: length_nths length_digit_encode)
      apply (rule bij_betw_same_card[where f="ind_in_set (vars1 \<union> vars2 \<union> vars3)"])
      unfolding bij_betw_def apply (rule conjI)
      subgoal apply (rule ind_in_set_inj') by auto
      apply auto using finite_union by (auto simp add: ** intro: ind_in_set_less)
    apply (subst nths_complement_ind_in_set)
    subgoal using assms by auto
    subgoal apply (auto simp only: length_digit_encode length_nths)
      by (auto simp add: ** uassoc)
    using nths_assoc_three_B[OF assms(1-2)] uassoc by auto

  have m3eq: "digit_encode c.dims0 (digit_decode d.dims2 (nths (digit_encode d.dims0 i) (- d.vars1')))
    = nths (digit_encode d.dims0 i) (- d.vars1')" if "i < state_sig.d b.dims0" for i
    unfolding c.dims0_def c.vars0_def d.dims2_def d.dims0_def d.vars1'_def d.vars0_def
    apply (subst digit_encode_decode)
     apply (subst nths_complement_ind_in_set)
     subgoal using assms by auto
     subgoal apply (auto simp only: length_digit_encode length_nths)
      by (auto simp add: ** uassoc)
    apply (rule valid_index_ind_in_set)
       apply (rule digit_encode_valid_index)
     using that unfolding state_sig.d_def b.dims0_def b.vars0_def using uassoc by auto

  have m3index: "partial_state.encode2 c.dims0 c.vars1' (partial_state.encode2 d.dims0 d.vars1' i) =
    partial_state.encode2 b.dims0 b.vars1' i"
    if "i < state_sig.d b.dims0" for i
    unfolding partial_state.encode2_def partial_state.dims2_def c.nths_vars2' d.nths_vars2' b.nths_vars2'
    apply (rule arg_cong[where f="digit_decode c.dims2"])
    apply (subst m3eq[OF that])
    unfolding d.dims0_def d.vars0_def d.vars1'_def c.vars1'_def b.dims0_def b.vars1'_def b.vars0_def c.vars0_def
    apply (subst nths_complement_ind_in_set)
    subgoal using assms by auto
    subgoal apply (auto simp only: length_digit_encode length_nths)
      by (auto simp add: ** uassoc)
    apply (subst nths_complement_ind_in_set)
    subgoal using assms by auto
    subgoal apply (auto simp only: length_nths length_digit_encode)
      apply (rule bij_betw_same_card[where f="ind_in_set (vars1 \<union> vars2 \<union> vars3)"])
      unfolding bij_betw_def apply (rule conjI)
      subgoal apply (rule ind_in_set_inj') by auto
      apply (auto simp add: uassoc) using finite_union
      by (auto simp add: ** intro: ind_in_set_less)
    apply (subst nths_complement_ind_in_set)
    subgoal using assms by auto
    subgoal apply (auto simp only: length_nths length_digit_encode)
      by (auto simp add: ** uassoc)
    using nths_assoc_three_C[OF assms(1-2)] uassoc by auto

  show ?thesis
    unfolding a.ptensor_mat_def b.ptensor_mat_def c.ptensor_mat_def d.ptensor_mat_def partial_state.tensor_mat_def
    apply (rule cong_mat)
    subgoal unfolding b.dims0_def d.dims0_def b.vars0_def d.vars0_def 
      apply (subgoal_tac "vars1 \<union> vars2 \<union> vars3 = vars1 \<union> (vars2 \<union> vars3)") by auto
    subgoal unfolding b.dims0_def d.dims0_def b.vars0_def d.vars0_def 
      apply (subgoal_tac "vars1 \<union> vars2 \<union> vars3 = vars1 \<union> (vars2 \<union> vars3)") by auto
    subgoal for i j
    proof -
      assume lti: "i < state_sig.d b.dims0" and ltj: "j < state_sig.d b.dims0"
      have lti': "i < state_sig.d d.dims0" using \<open>state_sig.d b.dims0 = state_sig.d d.dims0\<close> lti by auto
      have ltj': "j < state_sig.d d.dims0" using \<open>state_sig.d b.dims0 = state_sig.d d.dims0\<close> ltj by auto
      have eq1: "partial_state.d2 d.dims0 d.vars1' = state_sig.d c.dims0"
        unfolding partial_state.d2_def partial_state.dims2_def d.nths_vars2'
          d.dims2_def state_sig.d_def c.dims0_def c.vars0_def by auto
      have eq2: "partial_state.d1 b.dims0 b.vars1' = state_sig.d a.dims0"
        unfolding partial_state.d1_def partial_state.dims1_def b.nths_vars1'
          b.dims1_def state_sig.d_def a.dims0_def a.vars0_def by auto
      have lt1: "partial_state.encode2 d.dims0 d.vars1' i < state_sig.d c.dims0"
        using partial_state.encode2_lt[OF lti', where vars=d.vars1'] eq1 by auto
      have lt2: "partial_state.encode2 d.dims0 d.vars1' j < state_sig.d c.dims0"
        using partial_state.encode2_lt[OF ltj', where vars=d.vars1'] eq1 by auto
      have lt3: "partial_state.encode1 b.dims0 b.vars1' i < state_sig.d a.dims0"
        using partial_state.encode1_lt[OF lti, where vars=b.vars1'] eq2 by auto
      have lt4: "partial_state.encode1 b.dims0 b.vars1' j < state_sig.d a.dims0"
        using partial_state.encode1_lt[OF ltj, where vars=b.vars1'] eq2 by auto
      show ?thesis
        apply (auto simp add: lt1 lt2 lt3 lt4)
        apply (simp only: m1index[OF lti] m1index[OF ltj] m2index[OF lti] m2index[OF ltj] m3index[OF lti] m3index[OF ltj])
        by auto
    qed
    done
qed

text \<open>Some simple consequences of associativity\<close>

lemma pmat_extension_assoc:
  assumes "vars1 \<inter> vars2 = {}"
    and "(vars1 \<union> vars2) \<inter> vars3 = {}"
    and "vars1 \<union> vars2 \<union> vars3 \<subseteq> {0..< length dims}"
  shows "pmat_extension dims vars1 (vars2 \<union> vars3) m =
         pmat_extension dims (vars1 \<union> vars2) vars3 (pmat_extension dims vars1 vars2 m)"
proof -
  interpret a: partial_state2 dims vars1 vars2
    by (unfold_locales, rule assms(1))
  interpret b: partial_state2 dims "vars1 \<union> vars2" vars3
    by (unfold_locales, rule assms(2))
  interpret c: partial_state2 dims vars2 vars3
    apply unfold_locales using assms(2) by auto
  interpret d: partial_state2 dims vars1 "vars2 \<union> vars3"
    apply unfold_locales using assms by auto
  have "a.d2 = c.d1"
    by (simp add: c.d1_def a.d2_def c.dims1_def a.dims2_def)
  have "c.d0 = d.d2"
    by (simp add: c.d0_def d.d2_def c.dims0_def d.dims2_def c.vars0_def)
  show ?thesis
    unfolding a.pmat_extension_def b.pmat_extension_def d.pmat_extension_def
    apply (simp add: ptensor_mat_assoc[OF assms])
    apply (simp add: \<open>a.d2 = c.d1\<close> c.ptensor_mat_id)
    by (simp add: \<open>c.d0 = d.d2\<close>)
qed

end

subsection \<open>Commands on subset of variables\<close>

context state_sig
begin

definition Utrans_P :: "nat set \<Rightarrow> complex mat \<Rightarrow> com" where
  "Utrans_P vars U = Utrans (mat_extension dims vars U)"

lemma well_com_Utrans_P:
  assumes "U \<in> carrier_mat (prod_list (nths dims vars)) (prod_list (nths dims vars))"
    and "unitary U"
  shows "well_com (Utrans_P vars U)"
proof -
  have 1: "mat_extension dims vars U \<in> carrier_mat d d"
    by (rule partial_state.mat_extension_carrier)
  have 2: "unitary (mat_extension dims vars U)"
    apply (rule partial_state.mat_extension_unitary)
    unfolding partial_state.d1_def partial_state.dims1_def using assms by auto
  show "well_com (Utrans_P vars U)"
    using 1 2 Utrans_P_def by auto
qed

definition Measure_P :: "nat set \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> complex mat) \<Rightarrow> com list \<Rightarrow> com" where
  "Measure_P vars n Ps Cs = Measure n (\<lambda>n. mat_extension dims vars (Ps n)) Cs"

definition While_P :: "nat set \<Rightarrow> complex mat \<Rightarrow> complex mat \<Rightarrow> com \<Rightarrow> com" where
  "While_P vars M0 M1 C = While (\<lambda>n.
    if n = 0 then mat_extension dims vars M0
    else if n = 1 then mat_extension dims vars M1
    else undefined) C"

end

end
