theory "List-Interleavings"
imports Main
begin

inductive interleave' :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" 
  where [simp]: "interleave' [] [] []"
  | "interleave' xs ys zs \<Longrightarrow>interleave' (x#xs) ys (x#zs)"
  | "interleave' xs ys zs \<Longrightarrow>interleave' xs (x#ys) (x#zs)"

definition interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" (infixr "\<otimes>" 64)
  where "xs \<otimes> ys = Collect (interleave' xs ys)"
lemma elim_interleave'[pred_set_conv]: "interleave' xs ys zs \<longleftrightarrow> zs \<in> xs \<otimes> ys" unfolding interleave_def by simp

lemmas interleave_intros[intro?] = interleave'.intros[to_set]
lemmas interleave_intros(1)[simp]
lemmas interleave_induct[consumes 1, induct set: interleave, case_names Nil left right] = interleave'.induct[to_set]
lemmas interleave_cases[consumes 1, cases set: interleave] = interleave'.cases[to_set]
lemmas interleave_simps = interleave'.simps[to_set]


inductive_cases interleave_ConsE[elim]: "(x#xs) \<in> ys \<otimes> zs"
inductive_cases interleave_ConsConsE[elim]: "xs \<in> y#ys \<otimes> z#zs"
inductive_cases interleave_ConsE2[elim]: "xs \<in> x#ys \<otimes> zs"
inductive_cases interleave_ConsE3[elim]: "xs \<in> ys \<otimes> x#zs"

lemma interleave_comm: "xs \<in> ys \<otimes> zs \<Longrightarrow> xs \<in> zs \<otimes> ys"
  by (induction rule: interleave_induct) (auto intro: interleave_intros)

lemma interleave_Nil1[simp]: "[] \<otimes> xs = {xs}"
  by (induction xs) (auto intro: interleave_intros elim: interleave_cases)

lemma interleave_Nil2[simp]: "xs \<otimes> [] = {xs}"
  by (induction xs) (auto intro: interleave_intros elim: interleave_cases)

lemma interleave_nil_simp[simp]: "[] \<in> xs \<otimes> ys \<longleftrightarrow> xs = [] \<and> ys = []"
  by (auto elim: interleave_cases)

lemma append_interleave: "xs @ ys \<in> xs \<otimes> ys"
  by (induction xs) (auto intro: interleave_intros)

lemma interleave_assoc1: "a \<in> xs \<otimes> ys \<Longrightarrow> b \<in> a \<otimes> zs \<Longrightarrow> \<exists> c. c \<in> ys \<otimes> zs \<and>  b \<in> xs  \<otimes> c"
  by (induction b arbitrary: a  xs ys zs)
     (simp, fastforce del: interleave_ConsE elim!: interleave_ConsE  intro: interleave_intros)

lemma interleave_assoc2: "a \<in> ys \<otimes> zs \<Longrightarrow> b \<in> xs \<otimes> a \<Longrightarrow> \<exists> c. c \<in> xs \<otimes> ys \<and>  b \<in> c \<otimes> zs"
  by (induction b arbitrary: a  xs ys zs )
     (simp, fastforce del: interleave_ConsE elim!: interleave_ConsE  intro: interleave_intros)

lemma interleave_set: "zs \<in> xs \<otimes> ys \<Longrightarrow> set zs = set xs \<union> set ys"
  by(induction rule:interleave_induct) auto

lemma interleave_tl: "xs \<in> ys \<otimes> zs \<Longrightarrow> tl xs \<in> tl ys \<otimes> zs \<or> tl xs \<in> ys \<otimes> (tl zs)"
  by(induction rule:interleave_induct) auto

lemma interleave_butlast: "xs \<in> ys \<otimes> zs \<Longrightarrow> butlast xs \<in> butlast ys \<otimes> zs \<or> butlast xs \<in> ys \<otimes> (butlast zs)"
  by (induction rule:interleave_induct) (auto intro: interleave_intros)

lemma interleave_take: "zs \<in> xs \<otimes> ys \<Longrightarrow> \<exists> n\<^sub>1 n\<^sub>2. n = n\<^sub>1 + n\<^sub>2 \<and>  take n zs \<in> take n\<^sub>1 xs \<otimes> take n\<^sub>2 ys"
  apply(induction arbitrary: n rule:interleave_induct)
  apply auto
  apply arith
  apply (case_tac n, simp)
  apply (drule_tac x = nat in meta_spec)
  apply auto
  apply (rule_tac x = "Suc n\<^sub>1" in exI)
  apply (rule_tac x = "n\<^sub>2" in exI)
  apply (auto intro: interleave_intros)[1]

  apply (case_tac n, simp)
  apply (drule_tac x = nat in meta_spec)
  apply auto
  apply (rule_tac x = "n\<^sub>1" in exI)
  apply (rule_tac x = "Suc n\<^sub>2" in exI)
  apply (auto intro: interleave_intros)[1]
  done

lemma filter_interleave: "xs \<in> ys \<otimes> zs \<Longrightarrow> filter P xs \<in> filter P ys \<otimes> filter P zs"
  by (induction rule: interleave_induct)  (auto intro: interleave_intros)

lemma interleave_filtered: "xs \<in> interleave (filter P xs)  (filter (\<lambda>x'. \<not> P x') xs)"
  by (induction xs) (auto intro: interleave_intros)


function foo where 
  "foo [] [] = undefined"
| "foo xs [] = undefined"
| "foo [] ys = undefined"
| "foo (x#xs) (y#ys) = undefined (foo xs (y#ys)) (foo (x#xs) ys)"
by pat_completeness auto
termination by lexicographic_order
lemmas list_induct2'' = foo.induct[case_names NilNil ConsNil NilCons ConsCons]

lemma interleave_filter:
  assumes "xs \<in> filter P ys \<otimes> filter P zs"
  obtains xs' where "xs' \<in> ys \<otimes> zs" and "xs = filter P xs'"
using assms
apply atomize_elim
proof(induction ys zs arbitrary: xs rule: list_induct2'')
case NilNil
  thus ?case by simp
next
case (ConsNil ys xs)
  thus ?case by auto
next
case (NilCons zs xs)
  thus ?case by auto
next
case (ConsCons y ys z zs xs)
  show ?case
  proof(cases "P y")
  case False
    with ConsCons.prems(1)
    have "xs \<in> filter P ys \<otimes> filter P (z#zs)" by simp
    from ConsCons.IH(1)[OF this]
    obtain xs' where "xs' \<in> ys \<otimes> (z # zs)" "xs = filter P xs'" by auto
    hence "y#xs' \<in> y#ys \<otimes> z#zs" and "xs = filter P (y#xs')"
      using False by (auto intro: interleave_intros)
    thus ?thesis by blast
  next
 case True
    show ?thesis
    proof(cases "P z")
    case False
      with ConsCons.prems(1)
      have "xs \<in> filter P (y#ys) \<otimes> filter P zs" by simp
      from ConsCons.IH(2)[OF this]
      obtain xs' where "xs' \<in> y#ys \<otimes> zs" "xs = filter P xs'" by auto
      hence "z#xs' \<in> y#ys \<otimes> z#zs" and "xs = filter P (z#xs')"
        using False by (auto intro: interleave_intros)
      thus ?thesis by blast
    next
    case True
      from ConsCons.prems(1) \<open>P y\<close> \<open>P z\<close>
      have "xs \<in> y # filter P ys  \<otimes> z # filter P zs"  by simp
      thus ?thesis 
      proof(rule interleave_ConsConsE)
        fix xs'
        assume "xs = y # xs'" and "xs' \<in> interleave (filter P ys) (z # filter P zs)"
        hence "xs' \<in> filter P ys  \<otimes> filter P (z#zs)" using \<open>P z\<close> by simp
        from ConsCons.IH(1)[OF this]
        obtain xs'' where "xs'' \<in> ys \<otimes> (z # zs)" and "xs' = filter P xs''" by auto
        hence "y#xs'' \<in> y#ys  \<otimes> z#zs" and "y#xs' = filter P (y#xs'')"
          using \<open>P y\<close> by (auto intro: interleave_intros)
        thus ?thesis using \<open>xs = _\<close> by blast
      next
        fix xs'
        assume "xs = z # xs'" and "xs' \<in> y # filter P ys  \<otimes> filter P zs"
        hence "xs' \<in> filter P (y#ys) \<otimes> filter P zs" using \<open>P y\<close> by simp
        from ConsCons.IH(2)[OF this]
        obtain xs'' where "xs'' \<in> y#ys \<otimes> zs" and "xs' = filter P xs''" by auto
        hence "z#xs'' \<in> y#ys \<otimes> z#zs" and "z#xs' = filter P (z#xs'')"
          using \<open>P z\<close> by (auto intro: interleave_intros)
        thus ?thesis using \<open>xs = _\<close> by blast
      qed
    qed
  qed
qed


end
