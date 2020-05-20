(* 
  File:     Non_Regular_Languages.thy
  Author:   Manuel Eberl <eberlm@in.tum.de>
  
  This file provides some tools for showing the non-regularity of a language, either 
  via an infinite set of equivalence classes or via the Pumping Lemma.
*)
section \<open>Tools for showing non-regularity of a language\<close>
theory Non_Regular_Languages
  imports Myhill
begin

subsection \<open>Auxiliary material\<close>

lemma bij_betw_image_quotient:
  "bij_betw (\<lambda>y. f -` {y}) (f ` A) (A // {(a,b). f a = f b})"
  by (force simp: bij_betw_def inj_on_def image_image quotient_def)
   
lemma regular_Derivs_finite:
  fixes r :: "'a :: finite rexp"
  shows "finite (range (\<lambda>w. Derivs w (lang r)))"
proof -
  have "?thesis \<longleftrightarrow> finite (UNIV // \<approx>lang r)"
    unfolding str_eq_conv_Derivs by (rule bij_betw_finite bij_betw_image_quotient)+
  also have "\<dots>" by (subst Myhill_Nerode [symmetric]) auto
  finally show ?thesis .
qed
  
lemma Nil_in_Derivs_iff: "[] \<in> Derivs w A \<longleftrightarrow> w \<in> A"
  by (auto simp: Derivs_def)

(* TODO: Move to distribution? *)
text \<open>
  The following operation repeats a list $n$ times (usually written as $w ^ n$).
\<close>
primrec repeat :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "repeat 0 xs = []"
| "repeat (Suc n) xs = xs @ repeat n xs"
  
lemma repeat_Cons_left: "repeat (Suc n) xs = xs @ repeat n xs" by simp
    
lemma repeat_Cons_right: "repeat (Suc n) xs = repeat n xs @ xs"
  by (induction n) simp_all
    
lemma repeat_Cons_append_commute [simp]: "repeat n xs @ xs = xs @ repeat n xs"
  by (subst repeat_Cons_right [symmetric]) simp
    
lemma repeat_Cons_add [simp]: "repeat (m + n) xs = repeat m xs @ repeat n xs"
  by (induction m) simp_all
    
lemma repeat_Nil [simp]: "repeat n [] = []"
  by (induction n) simp_all
    
lemma repeat_conv_replicate: "repeat n xs = concat (replicate n xs)"
  by (induction n) simp_all

    
(* TODO: Move to distribution? *)
lemma nth_prefixes [simp]: "n \<le> length xs \<Longrightarrow> prefixes xs ! n = take n xs"
  by (induction xs arbitrary: n) (auto simp: nth_Cons split: nat.splits)
    
lemma nth_suffixes [simp]: "n \<le> length xs \<Longrightarrow> suffixes xs ! n = drop (length xs - n) xs"
  by (subst suffixes_conv_prefixes) (simp_all add: rev_take)

lemma length_take_prefixes:
  assumes "xs \<in> set (take n (prefixes ys))"
  shows   "length xs < n"
proof (cases "n \<le> Suc (length ys)")
  case True
  with assms obtain i where "i < n" "xs = take i ys"
    by (subst (asm) nth_image [symmetric]) auto
  thus ?thesis by simp
next
  case False
  with assms have "prefix xs ys" by simp
  hence "length xs \<le> length ys" by (rule prefix_length_le)
  also from False have "\<dots> < n" by simp
  finally show ?thesis .
qed


subsection \<open>Non-regularity by giving an infinite set of equivalence classes\<close>
  
text \<open>
  Non-regularity can be shown by giving an infinite set of non-equivalent words (w.r.t. the 
  Myhill--Nerode relation).
\<close>
lemma not_regular_langI:
  assumes "infinite B" "\<And>x y. x \<in> B \<Longrightarrow> y \<in> B \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>w. \<not>(x @ w \<in> A \<longleftrightarrow> y @ w \<in> A)"
  shows   "\<not>regular_lang (A :: 'a :: finite list set)"
proof -
  have "(\<lambda>w. Derivs w A) ` B \<subseteq> range (\<lambda>w. Derivs w A)" by blast
  moreover from assms(2) have "inj_on (\<lambda>w. Derivs w A) B"
    by (auto simp: inj_on_def Derivs_def)
  with assms(1) have "infinite ((\<lambda>w. Derivs w A) ` B)"
    by (blast dest: finite_imageD)
  ultimately have "infinite (range (\<lambda>w. Derivs w A))" by (rule infinite_super)
  with regular_Derivs_finite show ?thesis by blast
qed

lemma not_regular_langI':
  assumes "infinite B" "\<And>x y. x \<in> B \<Longrightarrow> y \<in> B \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<exists>w. \<not>(f x @ w \<in> A \<longleftrightarrow> f y @ w \<in> A)"
  shows   "\<not>regular_lang (A :: 'a :: finite list set)"
proof (rule not_regular_langI)
  from assms(2) have "inj_on f B" by (force simp: inj_on_def)
  with \<open>infinite B\<close> show "infinite (f ` B)" by (simp add: finite_image_iff)
qed (insert assms, auto)

  
subsection \<open>The Pumping Lemma\<close>

text \<open>
  The Pumping lemma can be shown very easily from the Myhill--Nerode theorem: if we have 
  a word whose length is more than the (finite) number of equivalence classes, then it must 
  have two different prefixes in the same class and the difference between these two 
  prefixes can then be ``pumped''.
\<close>
lemma pumping_lemma_aux:
  fixes A :: "'a list set"
  defines "\<delta> \<equiv> \<lambda>w. Derivs w A"
  defines "n \<equiv> card (range \<delta>)"
  assumes "z \<in> A" "finite (range \<delta>)" "length z \<ge> n"
  shows "\<exists>u v w. z = u @ v @ w \<and> length (u @ v) \<le> n \<and> v \<noteq> [] \<and> (\<forall>i. u @ repeat i v @ w \<in> A)"
proof -
  define P where "P = set (take (Suc n) (prefixes z))"
  from \<open>length z \<ge> n\<close> have [simp]: "card P = Suc n"
    unfolding P_def by (subst distinct_card) (auto intro!: distinct_take)
  have length_le: "length y \<le> n" if "y \<in> P" for y
    using length_take_prefixes[OF that [unfolded P_def]] by simp
      
  have "card (\<delta> ` P) \<le> card (range \<delta>)" by (intro card_mono assms) auto
  also from assms have "\<dots> < card P" by simp
  finally have "\<not>inj_on \<delta> P" by (rule pigeonhole)
  then obtain a b where ab: "a \<in> P" "b \<in> P" "a \<noteq> b" "Derivs a A = Derivs b A"
    by (auto simp: inj_on_def \<delta>_def)
  from ab have prefix_ab: "prefix a z" "prefix b z" by (auto simp: P_def dest: in_set_takeD)
  from ab have length_ab: "length a \<le> n" "length b \<le> n"
    by (simp_all add: length_le)
      
  have *: ?thesis 
    if uz': "prefix u z'" "prefix z' z" "length z' \<le> n" 
            "u \<noteq> z'" "Derivs z' A = Derivs u A" for u z'
  proof -
    from \<open>prefix u z'\<close> and \<open>u \<noteq> z'\<close> 
      obtain v where v [simp]: "z' = u @ v" "v \<noteq> []" 
      by (auto simp: prefix_def)
    from \<open>prefix z' z\<close> obtain w where [simp]: "z = u @ v @ w" 
      by (auto simp: prefix_def)
      
    hence [simp]: "Derivs (repeat i v) (Derivs u A) = Derivs u A" for i
      by (induction i) (use uz' in simp_all)
    have "Derivs z A = Derivs (u @ repeat i v @ w) A" for i
      using uz' by simp
    with \<open>z \<in> A\<close> and uz' have "\<forall>i. u @ repeat i v @ w \<in> A"
      by (simp add: Nil_in_Derivs_iff [of _ A, symmetric])
    moreover have "z = u @ v @ w" by simp
    moreover from \<open>length z' \<le> n\<close> have "length (u @ v) \<le> n" by simp
    ultimately show ?thesis using \<open>v \<noteq> []\<close> by blast
  qed
  
  from prefix_ab have "prefix a b \<or> prefix b a" by (rule prefix_same_cases)
  with *[of a b] and *[of b a] and ab and prefix_ab and length_ab show ?thesis by blast
qed

theorem pumping_lemma:
  fixes r :: "'a :: finite rexp"
  obtains n where 
    "\<And>z. z \<in> lang r \<Longrightarrow> length z \<ge> n \<Longrightarrow> 
            \<exists>u v w. z = u @ v @ w \<and> length (u @ v) \<le> n \<and> v \<noteq> [] \<and> (\<forall>i. u @ repeat i v @ w \<in> lang r)"
proof -
  let ?n = "card (range (\<lambda>w. Derivs w (lang r)))"
  have "\<exists>u v w. z = u @ v @ w \<and> length (u @ v) \<le> ?n \<and> v \<noteq> [] \<and> (\<forall>i. u @ repeat i v @ w \<in> lang r)"
    if "z \<in> lang r" and "length z \<ge> ?n" for z
    by (intro pumping_lemma_aux[of z] that regular_Derivs_finite)
  thus ?thesis by (rule that)
qed
  
corollary pumping_lemma_not_regular_lang:
  fixes A :: "'a :: finite list set"
  assumes "\<And>n. length (z n) \<ge> n" and "\<And>n. z n \<in> A"
  assumes "\<And>n u v w. z n = u @ v @ w \<Longrightarrow> length (u @ v) \<le> n \<Longrightarrow> v \<noteq> [] \<Longrightarrow> 
             u @ repeat (i n u v w) v @ w \<notin> A"
  shows   "\<not>regular_lang A"
proof
  assume "regular_lang A"
  then obtain r where r: "lang r = A" by blast
  from pumping_lemma[of r] guess n .
  from this[of "z n"] and assms[of n] obtain u v w 
    where "z n = u @ v @ w" and "length (u @ v) \<le> n" and "v \<noteq> []" and 
          "\<And>i. u @ repeat i v @ w \<in> lang r" by (auto simp: r)
  with assms(3)[of n u v w] show False by (auto simp: r)
qed


subsection \<open>Examples\<close>

text \<open>
  The language of all words containing the same number of $a$s and $b$s is not regular.
\<close>
lemma "\<not>regular_lang {w. length (filter id w) = length (filter Not w)}" (is "\<not>regular_lang ?A")
proof (rule not_regular_langI')
  show "infinite (UNIV :: nat set)" by simp
next
  fix m n :: nat assume "m \<noteq> n"
  hence "replicate m True @ replicate m False \<in> ?A" and
        "replicate n True @ replicate m False \<notin> ?A" by simp_all
  thus "\<exists>w. \<not>(replicate m True @ w \<in> ?A \<longleftrightarrow> replicate n True @ w \<in> ?A)" by blast
qed

text \<open>
  The language $\{a^i b^i\ |\ i \in \mathbb{N}\}$ is not regular.
\<close>
lemma eq_replicate_iff:
  "xs = replicate n x \<longleftrightarrow> set xs \<subseteq> {x} \<and> length xs = n"
  using replicate_length_same[of xs x] by (subst eq_commute) auto
    
lemma replicate_eq_appendE:
  assumes "xs @ ys = replicate n x"
  obtains i j where "n = i + j" "xs = replicate i x" "ys = replicate j x"
proof -
  have "n = length (replicate n x)" by simp
  also note assms [symmetric]
  finally have "n = length xs + length ys" by simp
  moreover have "xs = replicate (length xs) x" and "ys = replicate (length ys) x"
    using assms by (auto simp: eq_replicate_iff)
  ultimately show ?thesis using that[of "length xs" "length ys"] by auto
qed
  
lemma "\<not>regular_lang (range (\<lambda>i. replicate i True @ replicate i False))" (is "\<not>regular_lang ?A")
proof (rule pumping_lemma_not_regular_lang)
  fix n :: nat
  show "length (replicate n True @ replicate n False) \<ge> n" by simp
  show "replicate n True @ replicate n False \<in> ?A" by simp
next
  fix n :: nat and u v w :: "bool list"
  assume decomp: "replicate n True @ replicate n False = u @ v @ w"
     and length_le: "length (u @ v) \<le> n" and v_ne: "v \<noteq> []"
  define w1 w2 where "w1 = take (n - length (u@v)) w" and "w2 = drop (n - length (u@v)) w"
  have w_decomp: "w = w1 @ w2" by (simp add: w1_def w2_def)
  
  have "replicate n True = take n (replicate n True @ replicate n False)" by simp
  also note decomp
  also have "take n (u @ v @ w) = u @ v @ w1" using length_le by (simp add: w1_def)
  finally have "u @ v @ w1 = replicate n True" by simp
  then obtain i j k 
    where uvw1: "n = i + j + k" "u = replicate i True" "v = replicate j True" "w1 = replicate k True"
    by (elim replicate_eq_appendE) auto
  
  have "replicate n False = drop n (replicate n True @ replicate n False)" by simp
  also note decomp
  finally have [simp]: "w2 = replicate n False" using length_le by (simp add: w2_def)
      
  have "u @ repeat (Suc (Suc 0)) v @ w = replicate (n + j) True @ replicate n False"
    by (simp add: uvw1 w_decomp replicate_add [symmetric])
  also have "\<dots> \<notin> ?A"
  proof safe
    fix m assume *: "replicate (n + j) True @ replicate n False = 
                       replicate m True @ replicate m False" (is "?lhs = ?rhs")
    have "n = length (filter Not ?lhs)" by simp
    also note *
    also have "length (filter Not ?rhs) = m" by simp
    finally have [simp]: "m = n" by simp
    from * have "v = []" by (simp add: uvw1)
    with \<open>v \<noteq> []\<close> show False by contradiction
  qed
  finally show "u @ repeat (Suc (Suc 0)) v @ w \<notin> ?A" .
qed
    
end
