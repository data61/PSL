section {* Stream Fusion *}

theory StreamFusion
imports Stream
begin

subsection {* Type constructors for state types *}

domain Switch = S1 | S2

domain 'a Maybe = Nothing | Just 'a

hide_const (open) Left Right

domain ('a, 'b) Either = Left 'a | Right 'b

domain ('a, 'b) Both  (infixl ":!:" 25) = Both 'a 'b (infixl ":!:" 75)

domain 'a L = L (lazy 'a)


subsection {* Map function *}

fixrec
  mapStep :: "('a \<rightarrow> 'b) \<rightarrow> ('s \<rightarrow> ('a, 's) Step) \<rightarrow> 's \<rightarrow> ('b, 's) Step"
where
  "mapStep\<cdot>f\<cdot>h\<cdot>\<bottom> = \<bottom>"
| "s \<noteq> \<bottom> \<Longrightarrow> mapStep\<cdot>f\<cdot>h\<cdot>s = (case h\<cdot>s of
    Done \<Rightarrow> Done
  | Skip\<cdot>s' \<Rightarrow> Skip\<cdot>s'
  | Yield\<cdot>x\<cdot>s' \<Rightarrow> Yield\<cdot>(f\<cdot>x)\<cdot>s')"

fixrec
  mapS :: "('a \<rightarrow> 'b) \<rightarrow> ('a, 's) Stream \<rightarrow> ('b, 's) Stream"
where
  "s \<noteq> \<bottom> \<Longrightarrow> mapS\<cdot>f\<cdot>(Stream\<cdot>h\<cdot>s) = Stream\<cdot>(mapStep\<cdot>f\<cdot>h)\<cdot>s"

lemma unfold_mapStep:
  fixes f :: "'a \<rightarrow> 'b" and h :: "'s \<rightarrow> ('a, 's) Step"
  assumes "s \<noteq> \<bottom>"
  shows "unfold\<cdot>(mapStep\<cdot>f\<cdot>h)\<cdot>s = mapL\<cdot>f\<cdot>(unfold\<cdot>h\<cdot>s)"
proof (rule below_antisym)
  show "unfold\<cdot>(mapStep\<cdot>f\<cdot>h)\<cdot>s \<sqsubseteq> mapL\<cdot>f\<cdot>(unfold\<cdot>h\<cdot>s)"
  using `s \<noteq> \<bottom>`
  apply (induct arbitrary: s rule: unfold_ind [where h="mapStep\<cdot>f\<cdot>h"])
  apply (simp, simp)
  apply (case_tac "h\<cdot>s", simp_all add: unfold)
  done
next
  show "mapL\<cdot>f\<cdot>(unfold\<cdot>h\<cdot>s) \<sqsubseteq> unfold\<cdot>(mapStep\<cdot>f\<cdot>h)\<cdot>s"
  using `s \<noteq> \<bottom>`
  apply (induct arbitrary: s rule: unfold_ind [where h="h"])
  apply (simp, simp)
  apply (case_tac "h\<cdot>s", simp_all add: unfold)
  done
qed

lemma unstream_mapS:
  fixes f :: "'a \<rightarrow> 'b" and a :: "('a, 's) Stream"
  shows "a \<noteq> \<bottom> \<Longrightarrow> unstream\<cdot>(mapS\<cdot>f\<cdot>a) = mapL\<cdot>f\<cdot>(unstream\<cdot>a)"
by (induct a, simp, simp add: unfold_mapStep)

lemma mapS_defined: "a \<noteq> \<bottom> \<Longrightarrow> mapS\<cdot>f\<cdot>a \<noteq> \<bottom>"
by (induct a, simp_all)

lemma mapS_cong:
  fixes f :: "'a \<rightarrow> 'b"
  fixes a :: "('a, 's) Stream"
  fixes b :: "('a, 't) Stream"
  shows "f = g \<Longrightarrow> a \<approx> b \<Longrightarrow> mapS\<cdot>f\<cdot>a \<approx> mapS\<cdot>g\<cdot>b"
unfolding bisimilar_def
by (simp add: unstream_mapS mapS_defined)

lemma mapL_eq: "mapL\<cdot>f\<cdot>xs = unstream\<cdot>(mapS\<cdot>f\<cdot>(stream\<cdot>xs))"
by (simp add: unstream_mapS)


subsection {* Filter function *}

fixrec
  filterStep :: "('a \<rightarrow> tr) \<rightarrow> ('s \<rightarrow> ('a, 's) Step) \<rightarrow> 's \<rightarrow> ('a, 's) Step"
where
  "filterStep\<cdot>p\<cdot>h\<cdot>\<bottom> = \<bottom>"
| "s \<noteq> \<bottom> \<Longrightarrow> filterStep\<cdot>p\<cdot>h\<cdot>s = (case h\<cdot>s of
    Done \<Rightarrow> Done
  | Skip\<cdot>s' \<Rightarrow> Skip\<cdot>s'
  | Yield\<cdot>x\<cdot>s' \<Rightarrow> (If p\<cdot>x then Yield\<cdot>x\<cdot>s' else Skip\<cdot>s'))"

fixrec
  filterS :: "('a \<rightarrow> tr) \<rightarrow> ('a, 's) Stream \<rightarrow> ('a, 's) Stream"
where
  "s \<noteq> \<bottom> \<Longrightarrow> filterS\<cdot>p\<cdot>(Stream\<cdot>h\<cdot>s) = Stream\<cdot>(filterStep\<cdot>p\<cdot>h)\<cdot>s"

lemma unfold_filterStep:
  fixes p :: "'a \<rightarrow> tr" and h :: "'s \<rightarrow> ('a, 's) Step"
  assumes "s \<noteq> \<bottom>"
  shows "unfold\<cdot>(filterStep\<cdot>p\<cdot>h)\<cdot>s = filterL\<cdot>p\<cdot>(unfold\<cdot>h\<cdot>s)"
proof (rule below_antisym)
  show "unfold\<cdot>(filterStep\<cdot>p\<cdot>h)\<cdot>s \<sqsubseteq> filterL\<cdot>p\<cdot>(unfold\<cdot>h\<cdot>s)"
  using `s \<noteq> \<bottom>`
  apply (induct arbitrary: s rule: unfold_ind [where h="filterStep\<cdot>p\<cdot>h"])
  apply (simp, simp)
  apply (case_tac "h\<cdot>s", simp_all add: unfold)
  apply (case_tac "p\<cdot>a" rule: trE, simp_all)
  done
next
  show "filterL\<cdot>p\<cdot>(unfold\<cdot>h\<cdot>s) \<sqsubseteq> unfold\<cdot>(filterStep\<cdot>p\<cdot>h)\<cdot>s"
  using `s \<noteq> \<bottom>`
  apply (induct arbitrary: s rule: unfold_ind [where h="h"])
  apply (simp, simp)
  apply (case_tac "h\<cdot>s", simp_all add: unfold)
  apply (case_tac "p\<cdot>a" rule: trE, simp_all add: unfold)
  done
qed

lemma unstream_filterS:
  "a \<noteq> \<bottom> \<Longrightarrow> unstream\<cdot>(filterS\<cdot>p\<cdot>a) = filterL\<cdot>p\<cdot>(unstream\<cdot>a)"
by (induct a, simp, simp add: unfold_filterStep)

lemma filterS_defined: "a \<noteq> \<bottom> \<Longrightarrow> filterS\<cdot>p\<cdot>a \<noteq> \<bottom>"
by (induct a, simp_all)

lemma filterS_cong:
  fixes p :: "'a \<rightarrow> tr"
  fixes a :: "('a, 's) Stream"
  fixes b :: "('a, 't) Stream"
  shows "p = q \<Longrightarrow> a \<approx> b \<Longrightarrow> filterS\<cdot>p\<cdot>a \<approx> filterS\<cdot>q\<cdot>b"
unfolding bisimilar_def
by (simp add: unstream_filterS filterS_defined)

lemma filterL_eq: "filterL\<cdot>p\<cdot>xs = unstream\<cdot>(filterS\<cdot>p\<cdot>(stream\<cdot>xs))"
by (simp add: unstream_filterS)


subsection {* Foldr function *}

fixrec
  foldrS :: "('a \<rightarrow> 'b \<rightarrow> 'b) \<rightarrow> 'b \<rightarrow> ('a, 's) Stream \<rightarrow> 'b"
where
  foldrS_Stream:
  "s \<noteq> \<bottom> \<Longrightarrow> foldrS\<cdot>f\<cdot>z\<cdot>(Stream\<cdot>h\<cdot>s) =
    (case h\<cdot>s of Done \<Rightarrow> z
               | Skip\<cdot>s' \<Rightarrow> foldrS\<cdot>f\<cdot>z\<cdot>(Stream\<cdot>h\<cdot>s')
               | Yield\<cdot>x\<cdot>s' \<Rightarrow> f\<cdot>x\<cdot>(foldrS\<cdot>f\<cdot>z\<cdot>(Stream\<cdot>h\<cdot>s')))"

lemma unfold_foldrS:
  assumes "s \<noteq> \<bottom>" shows "foldrS\<cdot>f\<cdot>z\<cdot>(Stream\<cdot>h\<cdot>s) = foldrL\<cdot>f\<cdot>z\<cdot>(unfold\<cdot>h\<cdot>s)"
proof (rule below_antisym)
  show "foldrS\<cdot>f\<cdot>z\<cdot>(Stream\<cdot>h\<cdot>s) \<sqsubseteq> foldrL\<cdot>f\<cdot>z\<cdot>(unfold\<cdot>h\<cdot>s)"
  using `s \<noteq> \<bottom>`
  apply (induct arbitrary: s rule: foldrS.induct)
  apply (simp, simp, simp)
  apply (case_tac "h\<cdot>s", simp_all add: monofun_cfun unfold)
  done
next
  show "foldrL\<cdot>f\<cdot>z\<cdot>(unfold\<cdot>h\<cdot>s) \<sqsubseteq> foldrS\<cdot>f\<cdot>z\<cdot>(Stream\<cdot>h\<cdot>s)"
  using `s \<noteq> \<bottom>`
  apply (induct arbitrary: s rule: unfold_ind)
  apply (simp, simp)
  apply (case_tac "h\<cdot>s", simp_all add: monofun_cfun unfold)
  done
qed

lemma unstream_foldrS:
  "a \<noteq> \<bottom> \<Longrightarrow> foldrS\<cdot>f\<cdot>z\<cdot>a = foldrL\<cdot>f\<cdot>z\<cdot>(unstream\<cdot>a)"
by (induct a, simp, simp del: foldrS_Stream add: unfold_foldrS)

lemma foldrS_cong:
  fixes a :: "('a, 's) Stream"
  fixes b :: "('a, 't) Stream"
  shows "f = g \<Longrightarrow> z = w \<Longrightarrow> a \<approx> b \<Longrightarrow> foldrS\<cdot>f\<cdot>z\<cdot>a = foldrS\<cdot>g\<cdot>w\<cdot>b"
by (simp add: bisimilar_def unstream_foldrS)

lemma foldrL_eq:
  "foldrL\<cdot>f\<cdot>z\<cdot>xs = foldrS\<cdot>f\<cdot>z\<cdot>(stream\<cdot>xs)"
by (simp add: unstream_foldrS)


subsection {* EnumFromTo function *}

type_synonym int' = "int\<^sub>\<bottom>"

fixrec
  enumFromToStep :: "int' \<rightarrow> (int')\<^sub>\<bottom> \<rightarrow> (int', (int')\<^sub>\<bottom>) Step"
where
  "enumFromToStep\<cdot>(up\<cdot>y)\<cdot>(up\<cdot>(up\<cdot>x)) =
    (if x \<le> y then Yield\<cdot>(up\<cdot>x)\<cdot>(up\<cdot>(up\<cdot>(x+1))) else Done)"

lemma enumFromToStep_strict [simp]:
  "enumFromToStep\<cdot>\<bottom>\<cdot>x'' = \<bottom>"
  "enumFromToStep\<cdot>(up\<cdot>y)\<cdot>\<bottom> = \<bottom>"
  "enumFromToStep\<cdot>(up\<cdot>y)\<cdot>(up\<cdot>\<bottom>) = \<bottom>"
by fixrec_simp+

lemma enumFromToStep_simps' [simp]:
  "x \<le> y \<Longrightarrow> enumFromToStep\<cdot>(up\<cdot>y)\<cdot>(up\<cdot>(up\<cdot>x)) =
    Yield\<cdot>(up\<cdot>x)\<cdot>(up\<cdot>(up\<cdot>(x+1)))"
  "\<not> x \<le> y \<Longrightarrow> enumFromToStep\<cdot>(up\<cdot>y)\<cdot>(up\<cdot>(up\<cdot>x)) = Done"
  by simp_all

declare enumFromToStep.simps [simp del]

fixrec
  enumFromToS :: "int' \<rightarrow> int' \<rightarrow> (int', (int')\<^sub>\<bottom>) Stream"
where
  "enumFromToS\<cdot>x\<cdot>y = Stream\<cdot>(enumFromToStep\<cdot>y)\<cdot>(up\<cdot>x)"

declare enumFromToS.simps [simp del]

lemma unfold_enumFromToStep:
  "unfold\<cdot>(enumFromToStep\<cdot>(up\<cdot>y))\<cdot>(up\<cdot>n) = enumFromToL\<cdot>n\<cdot>(up\<cdot>y)"
proof (rule below_antisym)
  show "unfold\<cdot>(enumFromToStep\<cdot>(up\<cdot>y))\<cdot>(up\<cdot>n) \<sqsubseteq> enumFromToL\<cdot>n\<cdot>(up\<cdot>y)"
    apply (induct arbitrary: n rule: unfold_ind [where h="enumFromToStep\<cdot>(up\<cdot>y)"])
    apply (simp, simp)
    apply (case_tac n, simp, simp)
    apply (case_tac "x \<le> y", simp_all)
    done
next
  show "enumFromToL\<cdot>n\<cdot>(up\<cdot>y) \<sqsubseteq> unfold\<cdot>(enumFromToStep\<cdot>(up\<cdot>y))\<cdot>(up\<cdot>n)"
    apply (induct arbitrary: n rule: enumFromToL.induct)
    apply (simp, simp)
    apply (rename_tac e n)
    apply (case_tac n, simp)
    apply (case_tac "x \<le> y", simp_all add: unfold)
    done
qed

lemma unstream_enumFromToS:
  "unstream\<cdot>(enumFromToS\<cdot>x\<cdot>y) = enumFromToL\<cdot>x\<cdot>y"
apply (simp add: enumFromToS.simps)
apply (induct y, simp add: unfold)
apply (induct x, simp add: unfold)
apply (simp add: unfold_enumFromToStep)
done

lemma enumFromToS_defined: "enumFromToS\<cdot>x\<cdot>y \<noteq> \<bottom>"
  by (simp add: enumFromToS.simps)

lemma enumFromToS_cong:
  "x = x' \<Longrightarrow> y = y' \<Longrightarrow> enumFromToS\<cdot>x\<cdot>y \<approx> enumFromToS\<cdot>x'\<cdot>y'"
unfolding bisimilar_def by (simp add: enumFromToS_defined)

lemma enumFromToL_eq: "enumFromToL\<cdot>x\<cdot>y = unstream\<cdot>(enumFromToS\<cdot>x\<cdot>y)"
by (simp add: unstream_enumFromToS)


subsection {* Append function *}

fixrec
  appendStep ::
    "('s \<rightarrow> ('a, 's) Step) \<rightarrow>
     ('t \<rightarrow> ('a, 't) Step) \<rightarrow>
     't \<rightarrow> ('s, 't) Either \<rightarrow> ('a, ('s, 't) Either) Step"
where
  "sa \<noteq> \<bottom> \<Longrightarrow> appendStep\<cdot>ha\<cdot>hb\<cdot>sb0\<cdot>(Left\<cdot>sa) =
    (case ha\<cdot>sa of
      Done \<Rightarrow> Skip\<cdot>(Right\<cdot>sb0)
    | Skip\<cdot>sa' \<Rightarrow> Skip\<cdot>(Left\<cdot>sa')
    | Yield\<cdot>x\<cdot>sa' \<Rightarrow> Yield\<cdot>x\<cdot>(Left\<cdot>sa'))"
| "sb \<noteq> \<bottom> \<Longrightarrow> appendStep\<cdot>ha\<cdot>hb\<cdot>sb0\<cdot>(Right\<cdot>sb) =
    (case hb\<cdot>sb of
      Done \<Rightarrow> Done
    | Skip\<cdot>sb' \<Rightarrow> Skip\<cdot>(Right\<cdot>sb')
    | Yield\<cdot>x\<cdot>sb' \<Rightarrow> Yield\<cdot>x\<cdot>(Right\<cdot>sb'))"

lemma appendStep_strict [simp]: "appendStep\<cdot>ha\<cdot>hb\<cdot>sb0\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec
  appendS ::
    "('a, 's) Stream \<rightarrow> ('a, 't) Stream \<rightarrow> ('a, ('s, 't) Either) Stream"
where
  "sa0 \<noteq> \<bottom> \<Longrightarrow> sb0 \<noteq> \<bottom> \<Longrightarrow>
    appendS\<cdot>(Stream\<cdot>ha\<cdot>sa0)\<cdot>(Stream\<cdot>hb\<cdot>sb0) =
      Stream\<cdot>(appendStep\<cdot>ha\<cdot>hb\<cdot>sb0)\<cdot>(Left\<cdot>sa0)"

lemma unfold_appendStep:
  fixes ha :: "'s \<rightarrow> ('a, 's) Step"
  fixes hb :: "'t \<rightarrow> ('a, 't) Step"
  assumes sb0 [simp]: "sb0 \<noteq> \<bottom>"
  shows
  "(\<forall>sa. sa \<noteq> \<bottom> \<longrightarrow> unfold\<cdot>(appendStep\<cdot>ha\<cdot>hb\<cdot>sb0)\<cdot>(Left\<cdot>sa) =
         appendL\<cdot>(unfold\<cdot>ha\<cdot>sa)\<cdot>(unfold\<cdot>hb\<cdot>sb0)) \<and>
   (\<forall>sb. sb \<noteq> \<bottom> \<longrightarrow> unfold\<cdot>(appendStep\<cdot>ha\<cdot>hb\<cdot>sb0)\<cdot>(Right\<cdot>sb) =
         unfold\<cdot>hb\<cdot>sb)"
proof -
  note unfold [simp]
  let ?h = "appendStep\<cdot>ha\<cdot>hb\<cdot>sb0"

  have 1:
  "(\<forall>sa. sa \<noteq> \<bottom> \<longrightarrow>
         unfold\<cdot>?h\<cdot>(Left\<cdot>sa) \<sqsubseteq>
         appendL\<cdot>(unfold\<cdot>ha\<cdot>sa)\<cdot>(unfold\<cdot>hb\<cdot>sb0))
   \<and>
   (\<forall>sb. sb \<noteq> \<bottom> \<longrightarrow> unfold\<cdot>?h\<cdot>(Right\<cdot>sb) \<sqsubseteq> unfold\<cdot>hb\<cdot>sb)"
    apply (rule unfold_ind [where h="?h"])
      apply simp
     apply simp
    apply (intro conjI allI impI)
     apply (case_tac "ha\<cdot>sa", simp, simp, simp, simp)
    apply (case_tac "hb\<cdot>sb", simp, simp, simp, simp)
    done

  let ?P = "\<lambda>ua ub. \<forall>sa. sa \<noteq> \<bottom> \<longrightarrow>
        appendL\<cdot>(ua\<cdot>sa)\<cdot>(ub\<cdot>sb0) \<sqsubseteq> unfold\<cdot>?h\<cdot>(Left\<cdot>sa)"

  let ?Q = "\<lambda>ub. \<forall>sb. sb \<noteq> \<bottom> \<longrightarrow> ub\<cdot>sb \<sqsubseteq> unfold\<cdot>?h\<cdot>(Right\<cdot>sb)"

  have P_base: "\<And>ub. ?P \<bottom> ub"
    by simp

  have Q_base: "?Q \<bottom>"
    by simp

  have P_step: "\<And>ua ub. ?P ua ub \<Longrightarrow> ?Q ub \<Longrightarrow> ?P (unfoldF\<cdot>ha\<cdot>ua) ub"
    apply (intro allI impI)
    apply (case_tac "ha\<cdot>sa", simp, simp, simp, simp)
    done

  have Q_step: "\<And>ua ub. ?Q ub \<Longrightarrow> ?Q (unfoldF\<cdot>hb\<cdot>ub)"
    apply (intro allI impI)
    apply (case_tac "hb\<cdot>sb", simp, simp, simp, simp)
    done

  have Q: "?Q (unfold\<cdot>hb)"
    apply (rule unfold_ind [where h="hb"], simp)
     apply (rule Q_base)
    apply (erule Q_step)
    done

  have P: "?P (unfold\<cdot>ha) (unfold\<cdot>hb)"
    apply (rule unfold_ind [where h="ha"], simp)
     apply (rule P_base)
    apply (erule P_step)
    apply (rule Q)
    done

  have 2: "?P (unfold\<cdot>ha) (unfold\<cdot>hb) \<and> ?Q (unfold\<cdot>hb)"
    using P Q by (rule conjI)

  from 1 2 show ?thesis
    by (simp add: po_eq_conv [where 'a="'a LList"])
qed

lemma appendS_defined: "xs \<noteq> \<bottom> \<Longrightarrow> ys \<noteq> \<bottom> \<Longrightarrow> appendS\<cdot>xs\<cdot>ys \<noteq> \<bottom>"
by (cases xs, simp, cases ys, simp, simp)

lemma unstream_appendS:
  "a \<noteq> \<bottom> \<Longrightarrow> b \<noteq> \<bottom> \<Longrightarrow>
    unstream\<cdot>(appendS\<cdot>a\<cdot>b) = appendL\<cdot>(unstream\<cdot>a)\<cdot>(unstream\<cdot>b)"
apply (cases a, simp, cases b, simp)
apply (simp add: unfold_appendStep)
done

lemma appendS_cong:
  fixes f :: "'a \<rightarrow> 'b"
  fixes a :: "('a, 's) Stream"
  fixes b :: "('a, 't) Stream"
  shows "a \<approx> a' \<Longrightarrow> b \<approx> b' \<Longrightarrow> appendS\<cdot>a\<cdot>b \<approx> appendS\<cdot>a'\<cdot>b'"
unfolding bisimilar_def
by (simp add: unstream_appendS appendS_defined)

lemma appendL_eq: "appendL\<cdot>xs\<cdot>ys = unstream\<cdot>(appendS\<cdot>(stream\<cdot>xs)\<cdot>(stream\<cdot>ys))"
by (simp add: unstream_appendS)


subsection {* ZipWith function *}

fixrec
  zipWithStep ::
    "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow>
     ('s \<rightarrow> ('a, 's) Step) \<rightarrow>
     ('t \<rightarrow> ('b, 't) Step) \<rightarrow>
      's :!: 't :!: 'a L Maybe \<rightarrow> ('c, 's :!: 't :!: 'a L Maybe) Step"
where
  "sa \<noteq> \<bottom> \<Longrightarrow> sb \<noteq> \<bottom> \<Longrightarrow>
   zipWithStep\<cdot>f\<cdot>ha\<cdot>hb\<cdot>(sa :!: sb :!: Nothing) =
   (case ha\<cdot>sa of
     Done \<Rightarrow> Done
   | Skip\<cdot>sa' \<Rightarrow> Skip\<cdot>(sa' :!: sb :!: Nothing)
   | Yield\<cdot>a\<cdot>sa' \<Rightarrow> Skip\<cdot>(sa' :!: sb :!: Just\<cdot>(L\<cdot>a)))"
| "sa \<noteq> \<bottom> \<Longrightarrow> sb \<noteq> \<bottom> \<Longrightarrow>
   zipWithStep\<cdot>f\<cdot>ha\<cdot>hb\<cdot>(sa :!: sb :!: Just\<cdot>(L\<cdot>a)) =
   (case hb\<cdot>sb of
     Done \<Rightarrow> Done
   | Skip\<cdot>sb' \<Rightarrow> Skip\<cdot>(sa :!: sb' :!: Just\<cdot>(L\<cdot>a))
   | Yield\<cdot>b\<cdot>sb' \<Rightarrow> Yield\<cdot>(f\<cdot>a\<cdot>b)\<cdot>(sa :!: sb' :!: Nothing))"

lemma zipWithStep_strict [simp]: "zipWithStep\<cdot>f\<cdot>ha\<cdot>hb\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec
  zipWithS :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow>
      ('a, 's) Stream \<rightarrow> ('b, 't) Stream \<rightarrow> ('c, 's :!: 't :!: 'a L Maybe) Stream"
where
  "sa0 \<noteq> \<bottom> \<Longrightarrow> sb0 \<noteq> \<bottom> \<Longrightarrow> zipWithS\<cdot>f\<cdot>(Stream\<cdot>ha\<cdot>sa0)\<cdot>(Stream\<cdot>hb\<cdot>sb0) =
    Stream\<cdot>(zipWithStep\<cdot>f\<cdot>ha\<cdot>hb)\<cdot>(sa0 :!: sb0 :!: Nothing)"

lemma zipWithS_fix_ind_lemma:
  fixes P Q :: "nat \<Rightarrow> nat \<Rightarrow> bool"
  assumes P_0: "\<And>j. P 0 j" and P_Suc: "\<And>i j. P i j \<Longrightarrow> Q i j \<Longrightarrow> P (Suc i) j"
  assumes Q_0: "\<And>i. Q i 0" and Q_Suc: "\<And>i j. P i j \<Longrightarrow> Q i j \<Longrightarrow> Q i (Suc j)"
  shows "P i j \<and> Q i j"
apply (induct n \<equiv> "i + j" arbitrary: i j)
apply (simp add: P_0 Q_0)
apply (rule conjI)
apply (case_tac i, simp add: P_0, simp add: P_Suc)
apply (case_tac j, simp add: Q_0, simp add: Q_Suc)
done

lemma zipWithS_fix_ind:
  assumes x: "x = fix\<cdot>f" and y: "y = fix\<cdot>g"
  assumes adm_P: "adm (\<lambda>x. P (fst x) (snd x))"
  assumes adm_Q: "adm (\<lambda>x. Q (fst x) (snd x))"
  assumes P_0: "\<And>b. P \<bottom> b" and P_Suc: "\<And>a b. P a b \<Longrightarrow> Q a b \<Longrightarrow> P (f\<cdot>a) b"
  assumes Q_0: "\<And>a. Q a \<bottom>" and Q_Suc: "\<And>a b. P a b \<Longrightarrow> Q a b \<Longrightarrow> Q a (g\<cdot>b)"
  shows "P x y \<and> Q x y"
proof -
  have 1: "\<And>i j. P (iterate i\<cdot>f\<cdot>\<bottom>) (iterate j\<cdot>g\<cdot>\<bottom>) \<and> Q (iterate i\<cdot>f\<cdot>\<bottom>) (iterate j\<cdot>g\<cdot>\<bottom>)"
    apply (rule_tac i=i and j=j in zipWithS_fix_ind_lemma)
    apply (simp add: P_0)
    apply (simp add: P_Suc)
    apply (simp add: Q_0)
    apply (simp add: Q_Suc)
    done
  have "case_prod P (\<Squnion>i. (iterate i\<cdot>f\<cdot>\<bottom>, iterate i\<cdot>g\<cdot>\<bottom>))"
    apply (rule admD)
    apply (simp add: split_def adm_P)
    apply simp
    apply (simp add: 1)
    done
  then have P: "P x y"
    unfolding x y fix_def2
    by (simp add: lub_prod)
  have "case_prod Q (\<Squnion>i. (iterate i\<cdot>f\<cdot>\<bottom>, iterate i\<cdot>g\<cdot>\<bottom>))"
    apply (rule admD)
    apply (simp add: split_def adm_Q)
    apply simp
    apply (simp add: 1)
    done
  then have Q: "Q x y"
    unfolding x y fix_def2
    by (simp add: lub_prod)
  from P Q show ?thesis by simp
qed

lemma unfold_zipWithStep:
  fixes f :: "'a \<rightarrow> 'b \<rightarrow> 'c"
  fixes ha :: "'s \<rightarrow> ('a, 's) Step"
  fixes hb :: "'t \<rightarrow> ('b, 't) Step"
  defines h_def: "h \<equiv> zipWithStep\<cdot>f\<cdot>ha\<cdot>hb"
  shows
  "(\<forall>sa sb. sa \<noteq> \<bottom> \<longrightarrow> sb \<noteq> \<bottom> \<longrightarrow>
    unfold\<cdot>h\<cdot>(sa :!: sb :!: Nothing) =
      zipWithL\<cdot>f\<cdot>(unfold\<cdot>ha\<cdot>sa)\<cdot>(unfold\<cdot>hb\<cdot>sb)) \<and>
   (\<forall>sa sb a. sa \<noteq> \<bottom> \<longrightarrow> sb \<noteq> \<bottom> \<longrightarrow>
    unfold\<cdot>h\<cdot>(sa :!: sb :!: Just\<cdot>(L\<cdot>a)) =
      zipWithL\<cdot>f\<cdot>(LCons\<cdot>a\<cdot>(unfold\<cdot>ha\<cdot>sa))\<cdot>(unfold\<cdot>hb\<cdot>sb))"
proof -
  note unfold [simp]
  have h_simps [simp]:
    "\<And>sa sb. sa \<noteq> \<bottom> \<Longrightarrow> sb \<noteq> \<bottom> \<Longrightarrow> h\<cdot>(sa :!: sb :!: Nothing) =
      (case ha\<cdot>sa of
        Done \<Rightarrow> Done
      | Skip\<cdot>sa' \<Rightarrow> Skip\<cdot>(sa' :!: sb :!: Nothing)
      | Yield\<cdot>a\<cdot>sa' \<Rightarrow> Skip\<cdot>(sa' :!: sb :!: Just\<cdot>(L\<cdot>a)))"
    "\<And>sa sb a. sa \<noteq> \<bottom> \<Longrightarrow> sb \<noteq> \<bottom> \<Longrightarrow> h\<cdot>(sa :!: sb :!: Just\<cdot>(L\<cdot>a)) =
      (case hb\<cdot>sb of
        Done \<Rightarrow> Done
      | Skip\<cdot>sb' \<Rightarrow> Skip\<cdot>(sa :!: sb' :!: Just\<cdot>(L\<cdot>a))
      | Yield\<cdot>b\<cdot>sb' \<Rightarrow> Yield\<cdot>(f\<cdot>a\<cdot>b)\<cdot>(sa :!: sb' :!: Nothing))"
    "h\<cdot>\<bottom> = \<bottom>"
    unfolding h_def by simp_all

  have 1:
  "(\<forall>sa sb. sa \<noteq> \<bottom> \<longrightarrow> sb \<noteq> \<bottom> \<longrightarrow>
    unfold\<cdot>h\<cdot>(sa :!: sb :!: Nothing) \<sqsubseteq>
      zipWithL\<cdot>f\<cdot>(unfold\<cdot>ha\<cdot>sa)\<cdot>(unfold\<cdot>hb\<cdot>sb))
   \<and>
   (\<forall>sa sb a. sa \<noteq> \<bottom> \<longrightarrow> sb \<noteq> \<bottom> \<longrightarrow>
    unfold\<cdot>h\<cdot>(sa :!: sb :!: Just\<cdot>(L\<cdot>a)) \<sqsubseteq>
      zipWithL\<cdot>f\<cdot>(LCons\<cdot>a\<cdot>(unfold\<cdot>ha\<cdot>sa))\<cdot>(unfold\<cdot>hb\<cdot>sb))"
    apply (rule unfold_ind [where h="h"], simp)
     apply simp
    apply (intro conjI allI impI)
     apply (case_tac "ha\<cdot>sa", simp, simp, simp, simp)
    apply (case_tac "hb\<cdot>sb", simp, simp, simp, simp)
    done

  let ?P = "\<lambda>ua ub. \<forall>sa sb. sa \<noteq> \<bottom> \<longrightarrow> sb \<noteq> \<bottom> \<longrightarrow>
        zipWithL\<cdot>f\<cdot>(ua\<cdot>sa)\<cdot>(ub\<cdot>sb) \<sqsubseteq> unfold\<cdot>h\<cdot>(sa :!: sb :!: Nothing)"

  let ?Q = "\<lambda>ua ub. \<forall>sa sb a. sa \<noteq> \<bottom> \<longrightarrow> sb \<noteq> \<bottom> \<longrightarrow>
        zipWithL\<cdot>f\<cdot>(LCons\<cdot>a\<cdot>(ua\<cdot>sa))\<cdot>(ub\<cdot>sb) \<sqsubseteq>
          unfold\<cdot>h\<cdot>(sa :!: sb :!: Just\<cdot>(L\<cdot>a))"

  have P_base: "\<And>ub. ?P \<bottom> ub"
    by simp

  have Q_base: "\<And>ua. ?Q ua \<bottom>"
    by simp

  have P_step: "\<And>ua ub. ?P ua ub \<Longrightarrow> ?Q ua ub \<Longrightarrow> ?P (unfoldF\<cdot>ha\<cdot>ua) ub"
    by (clarsimp, case_tac "ha\<cdot>sa", simp_all)

  have Q_step: "\<And>ua ub. ?P ua ub \<Longrightarrow> ?Q ua ub \<Longrightarrow> ?Q ua (unfoldF\<cdot>hb\<cdot>ub)"
    by (clarsimp, case_tac "hb\<cdot>sb", simp_all)

  have 2: "?P (unfold\<cdot>ha) (unfold\<cdot>hb) \<and> ?Q (unfold\<cdot>ha) (unfold\<cdot>hb)"
    apply (rule zipWithS_fix_ind [OF unfold_eq_fix [of ha] unfold_eq_fix [of hb]])
    apply (simp, simp) (* admissibility *)
    apply (rule P_base)
    apply (erule (1) P_step)
    apply (rule Q_base)
    apply (erule (1) Q_step)
    done

  from 1 2 show ?thesis
    by (simp_all add: po_eq_conv [where 'a="'c LList"])
qed

lemma zipWithS_defined: "a \<noteq> \<bottom> \<Longrightarrow> b \<noteq> \<bottom> \<Longrightarrow> zipWithS\<cdot>f\<cdot>a\<cdot>b \<noteq> \<bottom>"
by (cases a, simp, cases b, simp, simp)

lemma unstream_zipWithS:
  "a \<noteq> \<bottom> \<Longrightarrow> b \<noteq> \<bottom> \<Longrightarrow>
    unstream\<cdot>(zipWithS\<cdot>f\<cdot>a\<cdot>b) = zipWithL\<cdot>f\<cdot>(unstream\<cdot>a)\<cdot>(unstream\<cdot>b)"
apply (cases a, simp, cases b, simp)
apply (simp add: unfold_zipWithStep)
done

lemma zipWithS_cong:
  "f = f' \<Longrightarrow> a \<approx> a' \<Longrightarrow> b \<approx> b' \<Longrightarrow>
    zipWithS\<cdot>f\<cdot>a\<cdot>b \<approx> zipWithS\<cdot>f\<cdot>a'\<cdot>b'"
unfolding bisimilar_def
by (simp add: unstream_zipWithS zipWithS_defined)

lemma zipWithL_eq:
  "zipWithL\<cdot>f\<cdot>xs\<cdot>ys = unstream\<cdot>(zipWithS\<cdot>f\<cdot>(stream\<cdot>xs)\<cdot>(stream\<cdot>ys))"
by (simp add: unstream_zipWithS)


subsection {* ConcatMap function *}

fixrec
  concatMapStep ::
    "('a \<rightarrow> ('b, 't) Stream) \<rightarrow>
     ('s \<rightarrow> ('a, 's) Step) \<rightarrow>
     's :!: ('b, 't) Stream Maybe \<rightarrow>
     ('b, 's :!: ('b, 't) Stream Maybe) Step"
where
  "sa \<noteq> \<bottom> \<Longrightarrow> concatMapStep\<cdot>f\<cdot>ha\<cdot>(sa :!: Nothing) =
    (case ha\<cdot>sa of
      Done \<Rightarrow> Done
    | Skip\<cdot>sa' \<Rightarrow> Skip\<cdot>(sa' :!: Nothing)
    | Yield\<cdot>a\<cdot>sa' \<Rightarrow> Skip\<cdot>(sa' :!: Just\<cdot>(f\<cdot>a)))"
| "sa \<noteq> \<bottom> \<Longrightarrow> sb \<noteq> \<bottom> \<Longrightarrow>
    concatMapStep\<cdot>f\<cdot>ha\<cdot>(sa :!: Just\<cdot>(Stream\<cdot>hb\<cdot>sb)) =
    (case hb\<cdot>sb of
      Done \<Rightarrow> Skip\<cdot>(sa :!: Nothing)
    | Skip\<cdot>sb' \<Rightarrow> Skip\<cdot>(sa :!: Just\<cdot>(Stream\<cdot>hb\<cdot>sb'))
    | Yield\<cdot>b\<cdot>sb' \<Rightarrow> Yield\<cdot>b\<cdot>(sa :!: Just\<cdot>(Stream\<cdot>hb\<cdot>sb')))"

lemma concatMapStep_strict [simp]: "concatMapStep\<cdot>f\<cdot>ha\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

fixrec
  concatMapS ::
    "('a \<rightarrow> ('b, 't) Stream) \<rightarrow> ('a, 's) Stream \<rightarrow>
     ('b, 's :!: ('b, 't) Stream Maybe) Stream"
where
  "s \<noteq> \<bottom> \<Longrightarrow> concatMapS\<cdot>f\<cdot>(Stream\<cdot>h\<cdot>s) = Stream\<cdot>(concatMapStep\<cdot>f\<cdot>h)\<cdot>(s :!: Nothing)"

lemma concatMapS_strict [simp]: "concatMapS\<cdot>f\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma unfold_concatMapStep:
  fixes ha :: "'s \<rightarrow> ('a, 's) Step"
  fixes f :: "'a \<rightarrow> ('b, 't) Stream"
  defines h_def: "h \<equiv> concatMapStep\<cdot>f\<cdot>ha"
  defines f'_def: "f' \<equiv> unstream oo f"
  shows
  "(\<forall>sa. sa \<noteq> \<bottom> \<longrightarrow>
      unfold\<cdot>h\<cdot>(sa :!: Nothing) = concatMapL\<cdot>f'\<cdot>(unfold\<cdot>ha\<cdot>sa)) \<and>
   (\<forall>sa hb sb. sa \<noteq> \<bottom> \<longrightarrow> sb \<noteq> \<bottom> \<longrightarrow>
      unfold\<cdot>h\<cdot>(sa :!: Just\<cdot>(Stream\<cdot>hb\<cdot>sb)) =
        appendL\<cdot>(unfold\<cdot>hb\<cdot>sb)\<cdot>(concatMapL\<cdot>f'\<cdot>(unfold\<cdot>ha\<cdot>sa)))"
proof -
  note unfold [simp]
  have h_simps [simp]:
    "\<And>sa. sa \<noteq> \<bottom> \<Longrightarrow> h\<cdot>(sa :!: Nothing) =
      (case ha\<cdot>sa of Done \<Rightarrow> Done
      | Skip\<cdot>sa' \<Rightarrow> Skip\<cdot>(sa' :!: Nothing)
      | Yield\<cdot>a\<cdot>sa' \<Rightarrow> Skip\<cdot>(sa' :!: Just\<cdot>(f\<cdot>a)))"
    "\<And>sa hb sb. sa \<noteq> \<bottom> \<Longrightarrow> sb \<noteq> \<bottom> \<Longrightarrow> h\<cdot>(sa :!: Just\<cdot>(Stream\<cdot>hb\<cdot>sb)) =
      (case hb\<cdot>sb of Done \<Rightarrow> Skip\<cdot>(sa :!: Nothing)
      | Skip\<cdot>sb' \<Rightarrow> Skip\<cdot>(sa :!: Just\<cdot>(Stream\<cdot>hb\<cdot>sb'))
      | Yield\<cdot>b\<cdot>sb' \<Rightarrow> Yield\<cdot>b\<cdot>(sa :!: Just\<cdot>(Stream\<cdot>hb\<cdot>sb')))"
    "h\<cdot>\<bottom> = \<bottom>"
    unfolding h_def by simp_all

  have f'_beta [simp]: "\<And>a. f'\<cdot>a = unstream\<cdot>(f\<cdot>a)"
    unfolding f'_def by simp

  have 1:
  "(\<forall>sa. sa \<noteq> \<bottom> \<longrightarrow>
      unfold\<cdot>h\<cdot>(sa :!: Nothing) \<sqsubseteq> concatMapL\<cdot>f'\<cdot>(unfold\<cdot>ha\<cdot>sa))
   \<and>
   (\<forall>sa hb sb. sa \<noteq> \<bottom> \<longrightarrow> sb \<noteq> \<bottom> \<longrightarrow>
      unfold\<cdot>h\<cdot>(sa :!: Just\<cdot>(Stream\<cdot>hb\<cdot>sb)) \<sqsubseteq>
        appendL\<cdot>(unfold\<cdot>hb\<cdot>sb)\<cdot>(concatMapL\<cdot>f'\<cdot>(unfold\<cdot>ha\<cdot>sa)))"
    apply (rule unfold_ind [where h="h"], simp)
     apply simp
    apply (intro conjI allI impI)
     apply (case_tac "ha\<cdot>sa", simp, simp, simp)
     apply (rename_tac a sa')
     apply (case_tac "f\<cdot>a", simp, simp)
    apply (case_tac "hb\<cdot>sb", simp, simp, simp, simp)
    done

  let ?P = "\<lambda>ua. \<forall>sa. sa \<noteq> \<bottom> \<longrightarrow>
        concatMapL\<cdot>f'\<cdot>(ua\<cdot>sa) \<sqsubseteq> unfold\<cdot>h\<cdot>(sa :!: Nothing)"

  let ?Q = "\<lambda>hb ua ub. \<forall>sa sb. sa \<noteq> \<bottom> \<longrightarrow> sb \<noteq> \<bottom> \<longrightarrow>
        appendL\<cdot>(ub\<cdot>sb)\<cdot>(concatMapL\<cdot>f'\<cdot>(ua\<cdot>sa)) \<sqsubseteq>
            unfold\<cdot>h\<cdot>(sa :!: Just\<cdot>(Stream\<cdot>hb\<cdot>sb))"

  have P_base: "?P \<bottom>"
    by simp

  have P_step: "\<And>ua. ?P ua \<Longrightarrow> \<forall>hb. ?Q hb ua (unfold\<cdot>hb) \<Longrightarrow> ?P (unfoldF\<cdot>ha\<cdot>ua)"
    apply (intro allI impI)
    apply (case_tac "ha\<cdot>sa", simp, simp, simp)
    apply (rename_tac a sa')
    apply (case_tac "f\<cdot>a", simp, simp)
    done

  have Q_base: "\<And>ua hb. ?Q hb ua \<bottom>"
    by simp

  have Q_step: "\<And>hb ua ub. ?P ua \<Longrightarrow> ?Q hb ua ub \<Longrightarrow> ?Q hb ua (unfoldF\<cdot>hb\<cdot>ub)"
    apply (intro allI impI)
    apply (case_tac "hb\<cdot>sb", simp, simp, simp, simp)
    done

  have 2: "?P (unfold\<cdot>ha) \<and> (\<forall>hb. ?Q hb (unfold\<cdot>ha) (unfold\<cdot>hb))"
    apply (rule unfold_ind [where h="ha"], simp)
     apply (rule conjI)
      apply (rule P_base)
     apply (rule allI, rule_tac h=hb in unfold_ind, simp)
      apply (rule Q_base)
     apply (erule Q_step [OF P_base])
    apply (erule conjE)
    apply (rule conjI)
     apply (erule (1) P_step)
    apply (rule allI, rule_tac h=hb in unfold_ind, simp)
     apply (rule Q_base)
    apply (erule (2) Q_step [OF P_step])
    done

  from 1 2 show ?thesis
    by (simp_all add: po_eq_conv [where 'a="'b LList"])
qed

lemma unstream_concatMapS:
  "unstream\<cdot>(concatMapS\<cdot>f\<cdot>a) = concatMapL\<cdot>(unstream oo f)\<cdot>(unstream\<cdot>a)"
by (cases a, simp, simp add: unfold_concatMapStep)

lemma concatMapS_defined: "a \<noteq> \<bottom> \<Longrightarrow> concatMapS\<cdot>f\<cdot>a \<noteq> \<bottom>"
by (induct a, simp_all)

lemma concatMapS_cong:
  fixes f :: "'a \<Rightarrow> ('b, 's) Stream"
  fixes g :: "'a \<Rightarrow> ('b, 't) Stream"
  fixes a :: "('a, 'u) Stream"
  fixes b :: "('a, 'v) Stream"
  shows "(\<And>x. f x \<approx> g x) \<Longrightarrow> a \<approx> b \<Longrightarrow> cont f \<Longrightarrow> cont g \<Longrightarrow>
    concatMapS\<cdot>(\<Lambda> x. f x)\<cdot>a \<approx> concatMapS\<cdot>(\<Lambda> x. g x)\<cdot>b"
unfolding bisimilar_def
by (simp add: unstream_concatMapS oo_def concatMapS_defined)

lemma concatMapL_eq:
  "concatMapL\<cdot>f\<cdot>xs = unstream\<cdot>(concatMapS\<cdot>(stream oo f)\<cdot>(stream\<cdot>xs))"
by (simp add: unstream_concatMapS oo_def eta_cfun)


subsection {* Examples *}

lemmas stream_eqs =
  mapL_eq
  filterL_eq
  foldrL_eq
  enumFromToL_eq
  appendL_eq
  zipWithL_eq
  concatMapL_eq

lemmas stream_congs =
  unstream_cong
  stream_cong
  stream_unstream_cong
  mapS_cong
  filterS_cong
  foldrS_cong
  enumFromToS_cong
  appendS_cong
  zipWithS_cong
  concatMapS_cong

lemma
  "mapL\<cdot>f oo filterL\<cdot>p oo mapL\<cdot>g =
   unstream oo mapS\<cdot>f oo filterS\<cdot>p oo mapS\<cdot>g oo stream"
apply (rule cfun_eqI, simp)
apply (unfold stream_eqs)
apply (intro stream_congs refl)
done

lemma
  "foldrL\<cdot>f\<cdot>z\<cdot>(mapL\<cdot>g\<cdot>(filterL\<cdot>p\<cdot>(enumFromToL\<cdot>x\<cdot>y))) =
    foldrS\<cdot>f\<cdot>z\<cdot>(mapS\<cdot>g\<cdot>(filterS\<cdot>p\<cdot>(enumFromToS\<cdot>x\<cdot>y)))"
apply (unfold stream_eqs)
apply (intro stream_congs refl)
done

lemma oo_LAM [simp]: "cont g \<Longrightarrow> f oo (\<Lambda> x. g x) = (\<Lambda> x. f\<cdot>(g x))"
  unfolding oo_def by simp

lemma
  "concatMapL\<cdot>(\<Lambda> k.
    mapL\<cdot>(\<Lambda> m. f\<cdot>k\<cdot>m)\<cdot>(enumFromToL\<cdot>one\<cdot>k))\<cdot>(enumFromToL\<cdot>one\<cdot>n) =
   unstream\<cdot>(concatMapS\<cdot>(\<Lambda> k.
    mapS\<cdot>(\<Lambda> m. f\<cdot>k\<cdot>m)\<cdot>(enumFromToS\<cdot>one\<cdot>k))\<cdot>(enumFromToS\<cdot>one\<cdot>n))"
unfolding stream_eqs
apply simp
apply (simp add: stream_congs)
done

end
