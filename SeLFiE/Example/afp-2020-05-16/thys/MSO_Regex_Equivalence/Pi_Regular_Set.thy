(*  Author: Tobias Nipkow, Alex Krauss, Dmitriy Traytel  *)

section "Regular Sets"

(*<*)
theory Pi_Regular_Set
imports Main
begin
(*>*)

type_synonym 'a lang = "'a list set"

definition conc :: "'a lang \<Rightarrow> 'a lang \<Rightarrow> 'a lang" (infixr "@@" 75) where
"A @@ B = {xs@ys | xs ys. xs:A & ys:B}"

lemma [code]:
  "A @@ B = (%(xs, ys). xs @ ys) ` (A \<times> B)"
  unfolding conc_def by auto

overloading word_pow == "compow :: nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
begin
  primrec word_pow :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "word_pow 0 w = []" |
  "word_pow (Suc n) w = w @ word_pow n w"
end

overloading lang_pow == "compow :: nat \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
begin
  primrec lang_pow :: "nat \<Rightarrow> 'a lang \<Rightarrow> 'a lang" where
  "lang_pow 0 A = {[]}" |
  "lang_pow (Suc n) A = A @@ (lang_pow n A)"
end

lemma word_pow_alt: "compow n w = concat (replicate n w)"
  by (induct n) auto

definition star :: "'a lang \<Rightarrow> 'a lang" where
"star A = (\<Union>n. A ^^ n)"


subsection\<open>Concatenation of Languages\<close>

lemma concI[simp,intro]: "u : A \<Longrightarrow> v : B \<Longrightarrow> u@v : A @@ B"
  by (auto simp add: conc_def)

lemma concE[elim]: 
assumes "w \<in> A @@ B"
obtains u v where "u \<in> A" "v \<in> B" "w = u@v"
  using assms by (auto simp: conc_def)

lemma conc_mono: "A \<subseteq> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow> A @@ B \<subseteq> C @@ D"
  by (auto simp: conc_def) 

lemma conc_empty[simp]: shows "{} @@ A = {}" and "A @@ {} = {}"
  by auto

lemma conc_epsilon[simp]: shows "{[]} @@ A = A" and "A @@ {[]} = A"
  by (simp_all add:conc_def)

lemma conc_assoc: "(A @@ B) @@ C = A @@ (B @@ C)"
  by (auto elim!: concE) (simp only: append_assoc[symmetric] concI)

lemma conc_Un_distrib:
shows "A @@ (B \<union> C) = A @@ B \<union> A @@ C"
and   "(A \<union> B) @@ C = A @@ C \<union> B @@ C"
  by auto

lemma conc_UNION_distrib:
shows "A @@ \<Union>(M ` I) = \<Union>((%i. A @@ M i) ` I)"
and   "\<Union>(M ` I) @@ A = \<Union>((%i. M i @@ A) ` I)"
  by auto

lemma hom_image_conc: "\<lbrakk>\<And>xs ys. f (xs @ ys) = f xs @ f ys\<rbrakk> \<Longrightarrow> f ` (A @@ B) = f ` A @@ f ` B"
  unfolding conc_def by (auto simp: image_iff) metis

lemma map_image_conc[simp]: "map f ` (A @@ B) = map f ` A @@ map f ` B"
  by (simp add: hom_image_conc)

lemma conc_subset_lists: "A \<subseteq> lists S \<Longrightarrow> B \<subseteq> lists S \<Longrightarrow> A @@ B \<subseteq> lists S"
  by(fastforce simp: conc_def in_lists_conv_set)


subsection\<open>Iteration of Languages\<close>

lemma lang_pow_add: "A ^^ (n + m) = A ^^ n @@ A ^^ m"
  by (induct n) (auto simp: conc_assoc)

lemma lang_pow_simps: "(A ^^ Suc n) = (A ^^ n @@ A)"
  using lang_pow_add[of n "Suc 0" A] by auto

lemma lang_pow_empty: "{} ^^ n = (if n = 0 then {[]} else {})"
  by (induct n) auto

lemma lang_pow_empty_Suc[simp]: "({}::'a lang) ^^ Suc n = {}"
  by (simp add: lang_pow_empty)

lemma conc_pow_comm:
  shows "A @@ (A ^^ n) = (A ^^ n) @@ A"
  by (induct n) (simp_all add: conc_assoc[symmetric])

lemma length_lang_pow_ub:
  "ALL w : A. length w \<le> k \<Longrightarrow> w : A^^n \<Longrightarrow> length w \<le> k*n"
  by(induct n arbitrary: w) (fastforce simp: conc_def)+

lemma length_lang_pow_lb:
  "ALL w : A. length w \<ge> k \<Longrightarrow> w : A^^n \<Longrightarrow> length w \<ge> k*n"
  by(induct n arbitrary: w) (fastforce simp: conc_def)+

lemma lang_pow_subset_lists: "A \<subseteq> lists S \<Longrightarrow> A ^^ n \<subseteq> lists S"
  by (induct n) (auto simp: conc_subset_lists)

lemma star_subset_lists: "A \<subseteq> lists S \<Longrightarrow> star A \<subseteq> lists S"
  unfolding star_def by(blast dest: lang_pow_subset_lists)

lemma star_if_lang_pow[simp]: "w : A ^^ n \<Longrightarrow> w : star A"
  by (auto simp: star_def)

lemma Nil_in_star[iff]: "[] : star A"
proof (rule star_if_lang_pow)
  show "[] : A ^^ 0" by simp
qed

lemma star_if_lang[simp]: assumes "w : A" shows "w : star A"
proof (rule star_if_lang_pow)
  show "w : A ^^ 1" using \<open>w : A\<close> by simp
qed

lemma append_in_starI[simp]:
assumes "u : star A" and "v : star A" shows "u@v : star A"
proof -
  from \<open>u : star A\<close> obtain m where "u : A ^^ m" by (auto simp: star_def)
  moreover
  from \<open>v : star A\<close> obtain n where "v : A ^^ n" by (auto simp: star_def)
  ultimately have "u@v : A ^^ (m+n)" by (simp add: lang_pow_add)
  thus ?thesis by simp
qed

lemma conc_star_star: "star A @@ star A = star A"
  by (auto simp: conc_def)

lemma conc_star_comm:
  shows "A @@ star A = star A @@ A"
  unfolding star_def conc_pow_comm conc_UNION_distrib
  by simp

lemma star_induct[consumes 1, case_names Nil append, induct set: star]:
assumes "w : star A"
  and "P []"
  and step: "!!u v. u : A \<Longrightarrow> v : star A \<Longrightarrow> P v \<Longrightarrow> P (u@v)"
shows "P w"
proof -
  { fix n have "w : A ^^ n \<Longrightarrow> P w"
    by (induct n arbitrary: w) (auto intro: \<open>P []\<close> step star_if_lang_pow) }
  with \<open>w : star A\<close> show "P w" by (auto simp: star_def)
qed

lemma star_empty[simp]: "star {} = {[]}"
  by (auto elim: star_induct)

lemma star_epsilon[simp]: "star {[]} = {[]}"
  by (auto elim: star_induct)

lemma star_idemp[simp]: "star (star A) = star A"
  by (auto elim: star_induct)

lemma star_unfold_left: "star A = A @@ star A \<union> {[]}" (is "?L = ?R")
proof
  show "?L \<subseteq> ?R" by (rule, erule star_induct) auto
qed auto

lemma concat_in_star: "set ws \<subseteq> A \<Longrightarrow> concat ws : star A"
  by (induct ws) simp_all

lemma in_star_iff_concat:
  "w : star A = (EX ws. set ws \<subseteq> A & w = concat ws & [] \<notin> set ws)"
  (is "_ = (EX ws. ?R w ws)")
proof
  assume "w : star A" thus "EX ws. ?R w ws"
  proof induct
    case Nil have "?R [] []" by simp
    thus ?case ..
  next
    case (append u v)
    moreover
    then obtain ws where "set ws \<subseteq> A \<and> v = concat ws \<and> [] \<notin> set ws" by blast
    ultimately have "?R (u@v) (if u = [] then ws else u#ws)" by auto
    thus ?case ..
  qed
next
  assume "EX us. ?R w us" thus "w : star A"
  by (auto simp: concat_in_star)
qed

lemma star_conv_concat: "star A = {concat ws|ws. set ws \<subseteq> A & [] \<notin> set ws}"
  by (fastforce simp: in_star_iff_concat)

lemma star_insert_eps[simp]: "star (insert [] A) = star(A)"
proof-
  { fix us
    have "set us \<subseteq> insert [] A \<Longrightarrow> EX vs. concat us = concat vs \<and> set vs \<subseteq> A"
      (is "?P \<Longrightarrow> EX vs. ?Q vs")
    proof
      let ?vs = "filter (%u. u \<noteq> []) us"
      show "?P \<Longrightarrow> ?Q ?vs" by (induct us) auto
    qed
  } thus ?thesis by (auto simp: star_conv_concat)
qed

lemma star_decom: 
  assumes a: "x \<in> star A" "x \<noteq> []"
  shows "\<exists>a b. x = a @ b \<and> a \<noteq> [] \<and> a \<in> A \<and> b \<in> star A"
  using a by (induct rule: star_induct) (blast)+

lemma Ball_starI: "\<forall>a \<in> set as. [a] \<in> A \<Longrightarrow> as \<in> star A"
  by (induct as rule: rev_induct) auto

lemma map_image_star[simp]: "map f ` star A = star (map f ` A)"
  by (auto elim: star_induct) (auto elim: star_induct simp del: map_append simp: map_append[symmetric] intro!: imageI)

subsection \<open>Left-Quotients of Languages\<close>

definition lQuot :: "'a \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
where "lQuot x A = { xs. x#xs \<in> A }"

definition lQuots :: "'a list \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
where "lQuots xs A = { ys. xs @ ys \<in> A }"

abbreviation 
  lQuotss :: "'a list \<Rightarrow> 'a lang set \<Rightarrow> 'a lang"
where
  "lQuotss s As \<equiv> \<Union> (lQuots s ` As)"


lemma lQuot_empty[simp]:   "lQuot a {} = {}"
  and lQuot_epsilon[simp]: "lQuot a {[]} = {}"
  and lQuot_char[simp]:    "lQuot a {[b]} = (if a = b then {[]} else {})"
  and lQuot_chars[simp]:   "lQuot a {[b] | b. P b} = (if P a then {[]} else {})"
  and lQuot_union[simp]:   "lQuot a (A \<union> B) = lQuot a A \<union> lQuot a B"
  and lQuot_inter[simp]:   "lQuot a (A \<inter> B) = lQuot a A \<inter> lQuot a B"
  and lQuot_compl[simp]:   "lQuot a (-A) = - lQuot a A"
  by (auto simp: lQuot_def)

lemma lQuot_conc_subset: "lQuot a A @@ B \<subseteq> lQuot a (A @@ B)" (is "?L \<subseteq> ?R")
proof 
  fix w assume "w \<in> ?L"
  then obtain u v where "w = u @ v" "a # u \<in> A" "v \<in> B"
    by (auto simp: lQuot_def)
  then have "a # w \<in> A @@ B"
    by (auto intro: concI[of "a # u", simplified])
  thus "w \<in> ?R" by (auto simp: lQuot_def)
qed

lemma lQuot_conc [simp]: "lQuot c (A @@ B) = (lQuot c A) @@ B \<union> (if [] \<in> A then lQuot c B else {})"
  unfolding lQuot_def conc_def
  by (auto simp add: Cons_eq_append_conv)

lemma lQuot_star [simp]: "lQuot c (star A) = (lQuot c A) @@ star A"
proof -
  have incl: "[] \<in> A \<Longrightarrow> lQuot c (star A) \<subseteq> (lQuot c A) @@ star A"
    unfolding lQuot_def conc_def 
    apply(auto simp add: Cons_eq_append_conv)
    apply(drule star_decom)
    apply(auto simp add: Cons_eq_append_conv)
    done

  have "lQuot c (star A) = lQuot c (A @@ star A \<union> {[]})"
    by (simp only: star_unfold_left[symmetric])
  also have "... = lQuot c (A @@ star A)"
    by (simp only: lQuot_union) (simp)
  also have "... =  (lQuot c A) @@ (star A) \<union> (if [] \<in> A then lQuot c (star A) else {})"
    by simp
   also have "... =  (lQuot c A) @@ star A"
    using incl by auto
  finally show "lQuot c (star A) = (lQuot c A) @@ star A" . 
qed

lemma lQuot_diff[simp]: "lQuot c (A - B) = lQuot c A - lQuot c B"
  by(auto simp add: lQuot_def)

lemma lQuot_lists[simp]: "c : S \<Longrightarrow> lQuot c (lists S) = lists S"
  by(auto simp add: lQuot_def)

lemma lQuots_simps [simp]:
  shows "lQuots [] A = A"
  and   "lQuots (c # s) A = lQuots s (lQuot c A)"
  and   "lQuots (s1 @ s2) A = lQuots s2 (lQuots s1 A)"
  unfolding lQuots_def lQuot_def by auto

lemma lQuots_append[iff]: "v \<in> lQuots w A \<longleftrightarrow> w @ v \<in> A"
  by (induct w arbitrary: v A) (auto simp add: lQuot_def)

subsection \<open>Right-Quotients of Languages\<close>

definition rQuot :: "'a \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
where "rQuot x A = { xs. xs @ [x] \<in> A }"

definition rQuots :: "'a list \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
where "rQuots xs A = { ys. ys @ rev xs \<in> A }"

abbreviation 
  rQuotss :: "'a list \<Rightarrow> 'a lang set \<Rightarrow> 'a lang"
where
  "rQuotss s As \<equiv> \<Union> (rQuots s ` As)"

lemma rQuot_rev_lQuot: "rQuot x A = rev ` lQuot x (rev ` A)"
  unfolding rQuot_def lQuot_def by (auto simp: rev_swap[symmetric])

lemma rQuots_rev_lQuots: "rQuots x A = rev ` lQuots x (rev ` A)"
  unfolding rQuots_def lQuots_def by (auto simp: rev_swap[symmetric])

lemma rQuot_empty[simp]:   "rQuot a {} = {}"
  and rQuot_epsilon[simp]: "rQuot a {[]} = {}"
  and rQuot_char[simp]:    "rQuot a {[b]} = (if a = b then {[]} else {})"
  and rQuot_union[simp]:   "rQuot a (A \<union> B) = rQuot a A \<union> rQuot a B"
  and rQuot_inter[simp]:   "rQuot a (A \<inter> B) = rQuot a A \<inter> rQuot a B"
  and rQuot_compl[simp]:   "rQuot a (-A) = - rQuot a A"
  by (auto simp: rQuot_def)

lemma lQuot_rQuot: "lQuot a (rQuot b A) = rQuot b (lQuot a A)"
  unfolding lQuot_def rQuot_def by auto

lemma rQuot_lQuot: "rQuot a (lQuot b A) = lQuot b (rQuot a A)"
  unfolding lQuot_def rQuot_def by auto

lemma rev_simp_invert: "(xs @ [x] = rev zs) = (zs = x # rev xs)"
  by (induct zs) auto

lemma rev_append_invert: "(xs @ ys = rev zs) = (zs = rev ys @ rev xs)"
  by (induct xs arbitrary: ys rule: rev_induct) auto

lemma image_rev_lists[simp]: "rev ` lists S = lists S"
proof (intro set_eqI)
  fix xs
  show "xs \<in> rev ` lists S \<longleftrightarrow> xs \<in> lists S"
  proof (induct xs rule: rev_induct)
    case (snoc x xs)
    thus ?case by (auto intro!: image_eqI[of _ rev] simp: rev_simp_invert)
  qed simp
qed

lemma image_rev_conc[simp]: "rev ` (A @@ B) = rev ` B @@ rev ` A"
  by auto (auto simp: rev_append[symmetric] simp del: rev_append)

lemma image_rev_star[simp]: "rev ` star A = star (rev ` A)"
  by (auto elim: star_induct) (auto elim: star_induct simp: rev_append[symmetric] simp del: rev_append)

lemma rQuot_conc [simp]: "rQuot c (A @@ B) = A @@ (rQuot c B) \<union> (if [] \<in> B then rQuot c A else {})"
  unfolding rQuot_rev_lQuot by (auto simp: image_image image_Un)

lemma rQuot_star [simp]: "rQuot c (star A) = star A @@ (rQuot c A)"
  unfolding rQuot_rev_lQuot by (auto simp: image_image)

lemma rQuot_diff[simp]: "rQuot c (A - B) = rQuot c A - rQuot c B"
  by(auto simp add: rQuot_def)

lemma rQuot_lists[simp]: "c : S \<Longrightarrow> rQuot c (lists S) = lists S"
  by(auto simp add: rQuot_def)

lemma rQuots_simps [simp]:
  shows "rQuots [] A = A"
  and   "rQuots (c # s) A = rQuots s (rQuot c A)"
  and   "rQuots (s1 @ s2) A = rQuots s2 (rQuots s1 A)"
  unfolding rQuots_def rQuot_def by auto

lemma rQuots_append[iff]: "v \<in> rQuots w A \<longleftrightarrow> v @ rev w \<in> A"
  by (induct w arbitrary: v A) (auto simp add: rQuot_def)

subsection \<open>Two-Sided-Quotients of Languages\<close>

definition biQuot :: "'a \<Rightarrow> 'a \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
where "biQuot x y A = { xs. x # xs @ [y] \<in> A }"

definition biQuots :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a lang \<Rightarrow> 'a lang"
where "biQuots xs ys A = { zs. xs @ zs @ rev ys \<in> A }"

abbreviation 
  biQuotss :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a lang set \<Rightarrow> 'a lang"
where
  "biQuotss xs ys As \<equiv> \<Union> (biQuots xs ys ` As)"

lemma biQuot_rQuot_lQuot: "biQuot x y A = rQuot y (lQuot x A)"
  unfolding biQuot_def rQuot_def lQuot_def by auto

lemma biQuot_lQuot_rQuot: "biQuot x y A = lQuot x (rQuot y A)"
  unfolding biQuot_def rQuot_def lQuot_def by auto

lemma biQuots_rQuots_lQuots: "biQuots x y A = rQuots y (lQuots x A)"
  unfolding biQuots_def rQuots_def lQuots_def by auto

lemma biQuots_lQuots_rQuots: "biQuots x y A = lQuots x (rQuots y A)"
  unfolding biQuots_def rQuots_def lQuots_def by auto

lemma biQuot_empty[simp]:   "biQuot a b {} = {}"
  and biQuot_epsilon[simp]: "biQuot a b {[]} = {}"
  and biQuot_char[simp]:    "biQuot a b {[c]} = {}"
  and biQuot_union[simp]:   "biQuot a b (A \<union> B) = biQuot a b A \<union> biQuot a b B"
  and biQuot_inter[simp]:   "biQuot a b (A \<inter> B) = biQuot a b A \<inter> biQuot a b B"
  and biQuot_compl[simp]:   "biQuot a b (-A) = - biQuot a b A"
  by (auto simp: biQuot_def)

lemma biQuot_conc [simp]: "biQuot a b (A @@ B) =
  lQuot a A @@ rQuot b B \<union>
  (if [] \<in> A \<and> [] \<in> B then biQuot a b A \<union> biQuot a b B
  else if [] \<in> A then biQuot a b B
  else if [] \<in> B then biQuot a b A
  else {})"
  unfolding biQuot_rQuot_lQuot by auto

lemma biQuot_star [simp]: "biQuot a b (star A) = biQuot a b A \<union> lQuot a A @@ star A @@ rQuot b A"
  unfolding biQuot_rQuot_lQuot by auto

lemma biQuot_diff[simp]: "biQuot a b (A - B) = biQuot a b A - biQuot a b B"
  by(auto simp add: biQuot_def)

lemma biQuot_lists[simp]: "a : S \<Longrightarrow> b : S \<Longrightarrow> biQuot a b (lists S) = lists S"
  by(auto simp add: biQuot_def)

lemma biQuots_simps [simp]:
  shows "biQuots [] [] A = A"
  and   "biQuots (a#as) (b#bs) A = biQuots as bs (biQuot a b A)"
  and   "\<lbrakk>length s1 = length t1; length s2 = length t2\<rbrakk> \<Longrightarrow>
    biQuots (s1 @ s2) (t1 @ t2) A = biQuots s2 t2 (biQuots s1 t1 A)"
  unfolding biQuots_def biQuot_def by auto

lemma biQuots_append[iff]: "v \<in> biQuots u w A \<longleftrightarrow> u @ v @ rev w \<in> A"
  unfolding biQuots_def by auto

subsection \<open>Arden's Lemma\<close>

lemma arden_helper:
  assumes eq: "X = A @@ X \<union> B"
  shows "X = (A ^^ Suc n) @@ X \<union> (\<Union>m\<le>n. (A ^^ m) @@ B)"
proof (induct n)
  case 0 
  show "X = (A ^^ Suc 0) @@ X \<union> (\<Union>m\<le>0. (A ^^ m) @@ B)"
    using eq by simp
next
  case (Suc n)
  have ih: "X = (A ^^ Suc n) @@ X \<union> (\<Union>m\<le>n. (A ^^ m) @@ B)" by fact
  also have "\<dots> = (A ^^ Suc n) @@ (A @@ X \<union> B) \<union> (\<Union>m\<le>n. (A ^^ m) @@ B)" using eq by simp
  also have "\<dots> = (A ^^ Suc (Suc n)) @@ X \<union> ((A ^^ Suc n) @@ B) \<union> (\<Union>m\<le>n. (A ^^ m) @@ B)"
    by (simp add: conc_Un_distrib conc_assoc[symmetric] conc_pow_comm)
  also have "\<dots> = (A ^^ Suc (Suc n)) @@ X \<union> (\<Union>m\<le>Suc n. (A ^^ m) @@ B)"
    by (auto simp add: atMost_Suc)
  finally show "X = (A ^^ Suc (Suc n)) @@ X \<union> (\<Union>m\<le>Suc n. (A ^^ m) @@ B)" .
qed

lemma Arden:
  assumes "[] \<notin> A" 
  shows "X = A @@ X \<union> B \<longleftrightarrow> X = star A @@ B"
proof
  assume eq: "X = A @@ X \<union> B"
  { fix w assume "w : X"
    let ?n = "size w"
    from \<open>[] \<notin> A\<close> have "ALL u : A. length u \<ge> 1"
      by (metis Suc_eq_plus1 add_leD2 le_0_eq length_0_conv not_less_eq_eq)
    hence "ALL u : A^^(?n+1). length u \<ge> ?n+1"
      by (metis length_lang_pow_lb nat_mult_1)
    hence "ALL u : A^^(?n+1)@@X. length u \<ge> ?n+1"
      by(auto simp only: conc_def length_append)
    hence "w \<notin> A^^(?n+1)@@X" by auto
    hence "w : star A @@ B" using \<open>w : X\<close> using arden_helper[OF eq, where n="?n"]
      by (auto simp add: star_def conc_UNION_distrib)
  } moreover
  { fix w assume "w : star A @@ B"
    hence "EX n. w : A^^n @@ B" by(auto simp: conc_def star_def)
    hence "w : X" using arden_helper[OF eq] by blast
  } ultimately show "X = star A @@ B" by blast 
next
  assume eq: "X = star A @@ B"
  have "star A = A @@ star A \<union> {[]}"
    by (rule star_unfold_left)
  then have "star A @@ B = (A @@ star A \<union> {[]}) @@ B"
    by metis
  also have "\<dots> = (A @@ star A) @@ B \<union> B"
    unfolding conc_Un_distrib by simp
  also have "\<dots> = A @@ (star A @@ B) \<union> B" 
    by (simp only: conc_assoc)
  finally show "X = A @@ X \<union> B" 
    using eq by blast 
qed


lemma reversed_arden_helper:
  assumes eq: "X = X @@ A \<union> B"
  shows "X = X @@ (A ^^ Suc n) \<union> (\<Union>m\<le>n. B @@ (A ^^ m))"
proof (induct n)
  case 0 
  show "X = X @@ (A ^^ Suc 0) \<union> (\<Union>m\<le>0. B @@ (A ^^ m))"
    using eq by simp
next
  case (Suc n)
  have ih: "X = X @@ (A ^^ Suc n) \<union> (\<Union>m\<le>n. B @@ (A ^^ m))" by fact
  also have "\<dots> = (X @@ A \<union> B) @@ (A ^^ Suc n) \<union> (\<Union>m\<le>n. B @@ (A ^^ m))" using eq by simp
  also have "\<dots> = X @@ (A ^^ Suc (Suc n)) \<union> (B @@ (A ^^ Suc n)) \<union> (\<Union>m\<le>n. B @@ (A ^^ m))"
    by (simp add: conc_Un_distrib conc_assoc)
  also have "\<dots> = X @@ (A ^^ Suc (Suc n)) \<union> (\<Union>m\<le>Suc n. B @@ (A ^^ m))"
    by (auto simp add: atMost_Suc)
  finally show "X = X @@ (A ^^ Suc (Suc n)) \<union> (\<Union>m\<le>Suc n. B @@ (A ^^ m))" .
qed

theorem reversed_Arden:
  assumes nemp: "[] \<notin> A"
  shows "X = X @@ A \<union> B \<longleftrightarrow> X = B @@ star A"
proof
 assume eq: "X = X @@ A \<union> B"
  { fix w assume "w : X"
    let ?n = "size w"
    from \<open>[] \<notin> A\<close> have "ALL u : A. length u \<ge> 1"
      by (metis Suc_eq_plus1 add_leD2 le_0_eq length_0_conv not_less_eq_eq)
    hence "ALL u : A^^(?n+1). length u \<ge> ?n+1"
      by (metis length_lang_pow_lb nat_mult_1)
    hence "ALL u : X @@ A^^(?n+1). length u \<ge> ?n+1"
      by(auto simp only: conc_def length_append)
    hence "w \<notin> X @@ A^^(?n+1)" by auto
    hence "w : B @@ star A" using \<open>w : X\<close> using reversed_arden_helper[OF eq, where n="?n"]
      by (auto simp add: star_def conc_UNION_distrib)
  } moreover
  { fix w assume "w : B @@ star A"
    hence "EX n. w : B @@ A^^n" by (auto simp: conc_def star_def)
    hence "w : X" using reversed_arden_helper[OF eq] by blast
  } ultimately show "X = B @@ star A" by blast 
next 
  assume eq: "X = B @@ star A"
  have "star A = {[]} \<union> star A @@ A" 
    unfolding conc_star_comm[symmetric]
    by(metis Un_commute star_unfold_left)
  then have "B @@ star A = B @@ ({[]} \<union> star A @@ A)"
    by metis
  also have "\<dots> = B \<union> B @@ (star A @@ A)"
    unfolding conc_Un_distrib by simp
  also have "\<dots> = B \<union> (B @@ star A) @@ A" 
    by (simp only: conc_assoc)
  finally show "X = X @@ A \<union> B" 
    using eq by blast 
qed

subsection \<open>Lists of Fixed Length\<close>

abbreviation listsN where "listsN n S \<equiv> {xs. xs \<in> lists S \<and> length xs = n}"

lemma tl_listsN: "A \<subseteq> listsN (n + 1) S \<Longrightarrow> tl ` A \<subseteq> listsN n S"
proof (intro image_subsetI)
  fix xs assume "A \<subseteq> listsN (n + 1) S" "xs \<in> A"
  thus "tl xs \<in> listsN n S" by (induct xs) auto
qed

lemma map_tl_listsN: "A \<subseteq> lists (listsN (n + 1) S) \<Longrightarrow> map tl ` A \<subseteq> lists (listsN n S)"
proof (intro image_subsetI)
  fix xss assume "A \<subseteq> lists (listsN (n + 1) S)" "xss \<in> A"
  hence "set xss \<subseteq> listsN (n + 1) S" by auto
  hence "\<forall>xs \<in> set xss. tl xs \<in> listsN n S" using tl_listsN[of "set xss" S n] by auto
  thus "map tl xss \<in> lists (listsN n S)" by (induct xss) auto
qed

(*<*)
end
(*>*)
