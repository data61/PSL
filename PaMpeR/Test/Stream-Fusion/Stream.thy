section {* Stream Iterators *}

theory Stream
imports LazyList
begin

subsection {* Type definitions for streams *}

text {* Note that everything is strict in the state type. *}

domain ('a,'s) Step = Done | Skip 's | Yield (lazy 'a) 's

type_synonym ('a, 's) Stepper = "'s \<rightarrow> ('a, 's) Step"

domain ('a,'s) Stream = Stream (lazy "('a, 's) Stepper") 's


subsection {* Converting from streams to lists *}

fixrec
  unfold :: "('a, 's) Stepper -> ('s -> 'a LList)"
where
  "unfold\<cdot>h\<cdot>\<bottom> = \<bottom>"
| "s \<noteq> \<bottom> \<Longrightarrow>
    unfold\<cdot>h\<cdot>s =
      (case h\<cdot>s of
        Done \<Rightarrow> LNil
      | Skip\<cdot>s' \<Rightarrow> unfold\<cdot>h\<cdot>s'
      | Yield\<cdot>x\<cdot>s' \<Rightarrow> LCons\<cdot>x\<cdot>(unfold\<cdot>h\<cdot>s'))"

fixrec
  unfoldF :: "('a, 's) Stepper \<rightarrow> ('s \<rightarrow> 'a LList) \<rightarrow> ('s \<rightarrow> 'a LList)"
where
  "unfoldF\<cdot>h\<cdot>u\<cdot>\<bottom> = \<bottom>"
| "s \<noteq> \<bottom> \<Longrightarrow>
    unfoldF\<cdot>h\<cdot>u\<cdot>s =
      (case h\<cdot>s of
        Done \<Rightarrow> LNil
      | Skip\<cdot>s' \<Rightarrow> u\<cdot>s'
      | Yield\<cdot>x\<cdot>s' \<Rightarrow> LCons\<cdot>x\<cdot>(u\<cdot>s'))"

lemma unfold_eq_fix: "unfold\<cdot>h = fix\<cdot>(unfoldF\<cdot>h)"
proof (rule below_antisym)
  show "unfold\<cdot>h \<sqsubseteq> fix\<cdot>(unfoldF\<cdot>h)"
    apply (rule unfold.induct, simp, simp)
    apply (subst fix_eq)
    apply (rule cfun_belowI, rename_tac s)
    apply (case_tac "s = \<bottom>", simp, simp)
    apply (intro monofun_cfun monofun_LAM below_refl, simp_all)
    done
  show "fix\<cdot>(unfoldF\<cdot>h) \<sqsubseteq> unfold\<cdot>h"
    apply (rule fix_ind, simp, simp)
    apply (subst unfold.unfold)
    apply (rule cfun_belowI, rename_tac s)
    apply (case_tac "s = \<bottom>", simp, simp)
    apply (intro monofun_cfun monofun_LAM below_refl, simp_all)
    done
qed

lemma unfold_ind:
    fixes P :: "('s \<rightarrow> 'a LList) \<Rightarrow> bool"
    assumes "adm P" and "P \<bottom>" and "\<And>u. P u \<Longrightarrow> P (unfoldF\<cdot>h\<cdot>u)"
    shows "P (unfold\<cdot>h)"
unfolding unfold_eq_fix by (rule fix_ind [of P, OF assms])

fixrec
  unfold2 :: "('s \<rightarrow> 'a LList) \<rightarrow> ('a, 's) Step \<rightarrow> 'a LList"
where
  "unfold2\<cdot>u\<cdot>Done = LNil"
| "s \<noteq> \<bottom> \<Longrightarrow> unfold2\<cdot>u\<cdot>(Skip\<cdot>s) = u\<cdot>s"
| "s \<noteq> \<bottom> \<Longrightarrow> unfold2\<cdot>u\<cdot>(Yield\<cdot>x\<cdot>s) = LCons\<cdot>x\<cdot>(u\<cdot>s)"

lemma unfold2_strict [simp]: "unfold2\<cdot>u\<cdot>\<bottom> = \<bottom>"
by fixrec_simp

lemma unfold: "s \<noteq> \<bottom> \<Longrightarrow> unfold\<cdot>h\<cdot>s = unfold2\<cdot>(unfold\<cdot>h)\<cdot>(h\<cdot>s)"
by (case_tac "h\<cdot>s", simp_all)

lemma unfoldF: "s \<noteq> \<bottom> \<Longrightarrow> unfoldF\<cdot>h\<cdot>u\<cdot>s = unfold2\<cdot>u\<cdot>(h\<cdot>s)"
by (case_tac "h\<cdot>s", simp_all)

declare unfold.simps(2) [simp del]
declare unfoldF.simps(2) [simp del]
declare unfoldF [simp]

fixrec
  unstream :: "('a, 's) Stream \<rightarrow> 'a LList"
where
  "s \<noteq> \<bottom> \<Longrightarrow> unstream\<cdot>(Stream\<cdot>h\<cdot>s) = unfold\<cdot>h\<cdot>s"

lemma unstream_strict [simp]: "unstream\<cdot>\<bottom> = \<bottom>"
by fixrec_simp


subsection {* Converting from lists to streams *}

fixrec
  streamStep :: "('a LList)\<^sub>\<bottom> \<rightarrow> ('a, ('a LList)\<^sub>\<bottom>) Step"
where
  "streamStep\<cdot>(up\<cdot>LNil) = Done"
| "streamStep\<cdot>(up\<cdot>(LCons\<cdot>x\<cdot>xs)) = Yield\<cdot>x\<cdot>(up\<cdot>xs)"

lemma streamStep_strict [simp]: "streamStep\<cdot>(up\<cdot>\<bottom>) = \<bottom>"
by fixrec_simp

fixrec
  stream :: "'a LList \<rightarrow> ('a, ('a LList)\<^sub>\<bottom>) Stream"
where
  "stream\<cdot>xs = Stream\<cdot>streamStep\<cdot>(up\<cdot>xs)"

lemma stream_defined [simp]: "stream\<cdot>xs \<noteq> \<bottom>"
  by simp

lemma unstream_stream [simp]:
  fixes xs :: "'a LList"
  shows "unstream\<cdot>(stream\<cdot>xs) = xs"
by (induct xs, simp_all add: unfold)

declare stream.simps [simp del]


subsection {* Bisimilarity relation on streams *}

definition
  bisimilar :: "('a, 's) Stream \<Rightarrow> ('a, 't) Stream \<Rightarrow> bool" (infix "\<approx>" 50)
where
  "a \<approx> b \<longleftrightarrow> unstream\<cdot>a = unstream\<cdot>b \<and> a \<noteq> \<bottom> \<and> b \<noteq> \<bottom>"

lemma unstream_cong:
  "a \<approx> b \<Longrightarrow> unstream\<cdot>a = unstream\<cdot>b"
    unfolding bisimilar_def by simp

lemma stream_cong:
  "xs = ys \<Longrightarrow> stream\<cdot>xs \<approx> stream\<cdot>ys"
    unfolding bisimilar_def by simp

lemma stream_unstream_cong:
  "a \<approx> b \<Longrightarrow> stream\<cdot>(unstream\<cdot>a) \<approx> b"
    unfolding bisimilar_def by simp

end
