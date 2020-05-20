chapter \<open>An Application: Finite Automata\<close>

theory Finite_Automata imports Ordinal
begin

text \<open>The point of this example is that the HF sets are closed under disjoint sums and Cartesian products,
 allowing the theory of finite state machines to be developed without issues of polymorphism
 or any tricky encodings of states.\<close>

record 'a fsm = states :: hf
                init :: hf
                final :: hf
                "next" :: "hf \<Rightarrow> 'a \<Rightarrow> hf \<Rightarrow> bool"

inductive reaches :: "['a fsm, hf, 'a list, hf] \<Rightarrow> bool"
where
    Nil:  "st \<^bold>\<in> states fsm \<Longrightarrow> reaches fsm st [] st"
  | Cons: "\<lbrakk>next fsm st x st''; reaches fsm st'' xs st'; st \<^bold>\<in> states fsm\<rbrakk> \<Longrightarrow> reaches fsm st (x#xs) st'"

declare reaches.intros [intro]
inductive_simps reaches_Nil [simp]:  "reaches fsm st [] st'"
inductive_simps reaches_Cons [simp]: "reaches fsm st (x#xs) st'"

lemma reaches_imp_states: "reaches fsm st xs st' \<Longrightarrow> st \<^bold>\<in> states fsm \<and> st' \<^bold>\<in> states fsm"
  by (induct xs arbitrary: st st', auto)

lemma reaches_append_iff:
     "reaches fsm st (xs@ys) st' \<longleftrightarrow> (\<exists>st''. reaches fsm st xs st'' \<and> reaches fsm st'' ys st')"
  by (induct xs arbitrary: ys st st') (auto simp: reaches_imp_states)

definition accepts :: "'a fsm \<Rightarrow> 'a list \<Rightarrow> bool"  where
  "accepts fsm xs \<equiv> \<exists>st st'. reaches fsm st xs st' \<and> st \<^bold>\<in> init fsm \<and> st' \<^bold>\<in> final fsm"

definition regular :: "'a list set \<Rightarrow> bool" where
  "regular S \<equiv> \<exists>fsm. S = {xs. accepts fsm xs}"

definition Null where
  "Null = \<lparr>states = 0, init = 0, final = 0, next = \<lambda>st x st'. False\<rparr>"

theorem regular_empty:  "regular {}"
  by (auto simp: regular_def accepts_def) (metis hempty_iff simps(2))

abbreviation NullStr where
  "NullStr \<equiv> \<lparr>states = 1, init = 1, final = 1, next = \<lambda>st x st'. False\<rparr>"

theorem regular_emptystr:  "regular {[]}"
  apply (auto simp: regular_def accepts_def)
  apply (rule exI [where x = NullStr], auto)
  apply (case_tac x, auto)
  done

abbreviation SingStr where
  "SingStr a \<equiv> \<lparr>states = \<lbrace>0, 1\<rbrace>, init = \<lbrace>0\<rbrace>, final = \<lbrace>1\<rbrace>, next = \<lambda>st x st'. st=0 \<and> x=a \<and> st'=1\<rparr>"

theorem regular_singstr: "regular {[a]}"
  apply (auto simp: regular_def accepts_def)
  apply (rule exI [where x = "SingStr a"], auto)
  apply (case_tac x, auto)
  apply (case_tac list, auto)
  done

definition Reverse where
  "Reverse fsm = \<lparr>states = states fsm, init = final fsm, final = init fsm,
                  next = \<lambda>st x st'. next fsm st' x st\<rparr>"

lemma Reverse_Reverse_ident [simp]: "Reverse (Reverse fsm) = fsm"
  by (simp add: Reverse_def)

lemma reaches_Reverse_iff [simp]:
     "reaches (Reverse fsm) st (rev xs) st' \<longleftrightarrow> reaches fsm st' xs st"
  by (induct xs arbitrary: st st') (auto simp add: Reverse_def reaches_append_iff reaches_imp_states)

lemma reaches_Reverse_iff2 [simp]:
     "reaches (Reverse fsm) st' xs st \<longleftrightarrow> reaches fsm st (rev xs) st'"
  by (metis reaches_Reverse_iff rev_rev_ident)

lemma [simp]: "init (Reverse fsm) = final fsm"
  by (simp add: Reverse_def)

lemma [simp]: "final (Reverse fsm) = init fsm"
  by (simp add: Reverse_def)

theorem regular_rev: "regular S \<Longrightarrow> regular (rev ` S)"
  apply (auto simp: regular_def accepts_def)
  apply (rule_tac x="Reverse fsm" in exI, force+)
  done

definition Times where
  "Times fsm1 fsm2 = \<lparr>states = states fsm1 * states fsm2,
                      init = init fsm1 * init fsm2,
                      final = final fsm1 * final fsm2,
                      next = \<lambda>st x st'. (\<exists>st1 st2 st1' st2'. st = \<langle>st1,st2\<rangle> \<and> st' = \<langle>st1',st2'\<rangle> \<and>
                                      next fsm1 st1 x st1' \<and> next fsm2 st2 x st2')\<rparr>"

lemma states_Times [simp]: "states (Times fsm1 fsm2) = states fsm1 * states fsm2"
  by (simp add: Times_def)

lemma init_Times [simp]: "init (Times fsm1 fsm2) = init fsm1 * init fsm2"
  by (simp add: Times_def)

lemma final_Times [simp]: "final (Times fsm1 fsm2) = final fsm1 * final fsm2"
  by (simp add: Times_def)

lemma next_Times: "next (Times fsm1 fsm2) \<langle>st1,st2\<rangle> x st' \<longleftrightarrow>
    (\<exists>st1' st2'. st' = \<langle>st1',st2'\<rangle> \<and> next fsm1 st1 x st1' \<and> next fsm2 st2 x st2')"
  by (simp add: Times_def)

lemma reaches_Times_iff [simp]:
     "reaches (Times fsm1 fsm2) \<langle>st1,st2\<rangle> xs \<langle>st1',st2'\<rangle> \<longleftrightarrow>
      reaches fsm1 st1 xs st1' \<and> reaches fsm2 st2 xs st2'"
apply (induct xs arbitrary: st1 st2 st1' st2', force)
apply (force simp add: next_Times Times_def reaches.Cons)
done

lemma accepts_Times_iff [simp]:
     "accepts (Times fsm1 fsm2) xs \<longleftrightarrow>
      accepts fsm1 xs \<and> accepts fsm2 xs"
  by (force simp add: accepts_def)

theorem regular_Int:
  assumes S: "regular S" and T: "regular T" shows "regular (S \<inter> T)"
proof -
  obtain fsmS fsmT where "S = {xs. accepts fsmS xs}" "T = {xs. accepts fsmT xs}" using S T
    by (auto simp: regular_def)
  hence "S \<inter> T = {xs. accepts (Times fsmS fsmT) xs}"
    by (auto simp: accepts_Times_iff [of fsmS fsmT])
  thus ?thesis
    by (metis regular_def)
qed

definition Plus where
  "Plus fsm1 fsm2 = \<lparr>states = states fsm1 + states fsm2,
                      init = init fsm1 + init fsm2,
                      final = final fsm1 + final fsm2,
                      next = \<lambda>st x st'. (\<exists>st1 st1'. st = Inl st1 \<and> st' = Inl st1' \<and> next fsm1 st1 x st1') \<or>
                                       (\<exists>st2 st2'. st = Inr st2 \<and> st' = Inr st2' \<and> next fsm2 st2 x st2')\<rparr>"

lemma states_Plus [simp]: "states (Plus fsm1 fsm2) = states fsm1 + states fsm2"
  by (simp add: Plus_def)

lemma init_Plus [simp]: "init (Plus fsm1 fsm2) = init fsm1 + init fsm2"
  by (simp add: Plus_def)

lemma final_Plus [simp]: "final (Plus fsm1 fsm2) = final fsm1 + final fsm2"
  by (simp add: Plus_def)

lemma next_Plus1: "next (Plus fsm1 fsm2) (Inl st1) x st' \<longleftrightarrow> (\<exists>st1'. st' = Inl st1' \<and> next fsm1 st1 x st1')"
  by (simp add: Plus_def)

lemma next_Plus2: "next (Plus fsm1 fsm2) (Inr st2) x st' \<longleftrightarrow> (\<exists>st2'. st' = Inr st2' \<and> next fsm2 st2 x st2')"
  by (simp add: Plus_def)

lemma reaches_Plus_iff1 [simp]:
     "reaches (Plus fsm1 fsm2) (Inl st1) xs st' \<longleftrightarrow>
      (\<exists>st1'. st' = Inl st1' \<and> reaches fsm1 st1 xs st1')"
apply (induct xs arbitrary: st1, force)
apply (force simp add: next_Plus1 reaches.Cons)
done

lemma reaches_Plus_iff2 [simp]:
     "reaches (Plus fsm1 fsm2) (Inr st2) xs st' \<longleftrightarrow>
      (\<exists>st2'. st' = Inr st2' \<and> reaches fsm2 st2 xs st2')"
apply (induct xs arbitrary: st2, force)
apply (force simp add: next_Plus2 reaches.Cons)
done

lemma reaches_Plus_iff [simp]:
     "reaches (Plus fsm1 fsm2) st xs st' \<longleftrightarrow>
      (\<exists>st1 st1'. st = Inl st1 \<and> st' = Inl st1' \<and> reaches fsm1 st1 xs st1') \<or>
      (\<exists>st2 st2'. st = Inr st2 \<and> st' = Inr st2' \<and> reaches fsm2 st2 xs st2')"
apply (induct xs arbitrary: st st', auto)
apply (force simp add: next_Plus1 next_Plus2 Plus_def reaches.Cons)
apply (auto simp: Plus_def)
done

lemma accepts_Plus_iff [simp]:
     "accepts (Plus fsm1 fsm2) xs \<longleftrightarrow> accepts fsm1 xs \<or> accepts fsm2 xs"
  by (auto simp: accepts_def) (metis sum_iff)

lemma regular_Un:
  assumes S: "regular S" and T: "regular T" shows "regular (S \<union> T)"
proof -
  obtain fsmS fsmT where "S = {xs. accepts fsmS xs}" "T = {xs. accepts fsmT xs}" using S T
    by (auto simp: regular_def)
  hence "S \<union> T = {xs. accepts (Plus fsmS fsmT) xs}"
    by (auto simp: accepts_Plus_iff [of fsmS fsmT])
  thus ?thesis
    by (metis regular_def)
qed

end
