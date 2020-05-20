(*  Title:      JinjaThreads/Framework/Bisimulation.thy
    Author:     Andreas Lochbihler
*)

section \<open>Various notions of bisimulation\<close>

theory Bisimulation
imports
  LTS
begin

type_synonym ('a, 'b) bisim = "'a \<Rightarrow> 'b \<Rightarrow> bool"

subsection \<open>Strong bisimulation\<close>

locale bisimulation_base = r1: trsys trsys1 + r2: trsys trsys2
  for trsys1 :: "('s1, 'tl1) trsys" ("_/ -1-_\<rightarrow>/ _" [50,0,50] 60)
  and trsys2 :: "('s2, 'tl2) trsys" ("_/ -2-_\<rightarrow>/ _" [50,0,50] 60) +
  fixes bisim :: "('s1, 's2) bisim" ("_/ \<approx> _" [50, 50] 60)
  and tlsim :: "('tl1, 'tl2) bisim" ("_/ \<sim> _" [50, 50] 60)
begin

notation
  r1.Trsys ("_/ -1-_\<rightarrow>*/ _" [50,0,50] 60) and
  r2.Trsys ("_/ -2-_\<rightarrow>*/ _" [50,0,50] 60)

notation
  r1.inf_step ("_ -1-_\<rightarrow>* \<infinity>" [50, 0] 80) and
  r2.inf_step ("_ -2-_\<rightarrow>* \<infinity>" [50, 0] 80)

notation
  r1.inf_step_table ("_ -1-_\<rightarrow>*t \<infinity>" [50, 0] 80) and
  r2.inf_step_table ("_ -2-_\<rightarrow>*t \<infinity>" [50, 0] 80)

abbreviation Tlsim :: "('tl1 list, 'tl2 list) bisim" ("_/ [\<sim>] _" [50, 50] 60)
where "Tlsim tl1 tl2 \<equiv> list_all2 tlsim tl1 tl2"

abbreviation Tlsiml :: "('tl1 llist, 'tl2 llist) bisim" ("_/ [[\<sim>]] _" [50, 50] 60)
where "Tlsiml tl1 tl2 \<equiv> llist_all2 tlsim tl1 tl2"

end

locale bisimulation = bisimulation_base +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  assumes simulation1: "\<lbrakk> s1 \<approx> s2; s1 -1-tl1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2' tl2. s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
  and simulation2: "\<lbrakk> s1 \<approx> s2; s2 -2-tl2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1' tl1. s1 -1-tl1\<rightarrow> s1' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
begin

lemma bisimulation_flip:
  "bisimulation trsys2 trsys1 (flip bisim) (flip tlsim)"
by(unfold_locales)(unfold flip_simps,(blast intro: simulation1 simulation2)+)

end

lemma bisimulation_flip_simps [flip_simps]:
  "bisimulation trsys2 trsys1 (flip bisim) (flip tlsim) = bisimulation trsys1 trsys2 bisim tlsim"
by(auto dest: bisimulation.bisimulation_flip simp only: flip_flip)

context bisimulation begin

lemma simulation1_rtrancl:
  "\<lbrakk>s1 -1-tls1\<rightarrow>* s1'; s1 \<approx> s2\<rbrakk>
  \<Longrightarrow> \<exists>s2' tls2. s2 -2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
proof(induct rule: rtrancl3p.induct)
  case rtrancl3p_refl thus ?case by(auto intro: rtrancl3p.rtrancl3p_refl)
next
  case (rtrancl3p_step s1 tls1 s1' tl1 s1'')
  from \<open>s1 \<approx> s2 \<Longrightarrow> \<exists>s2' tls2. s2 -2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2\<close> \<open>s1 \<approx> s2\<close>
  obtain s2' tls2 where "s2 -2-tls2\<rightarrow>* s2'" "s1' \<approx> s2'" "tls1 [\<sim>] tls2" by blast
  moreover from \<open>s1' -1-tl1\<rightarrow> s1''\<close> \<open>s1' \<approx> s2'\<close>
  obtain s2'' tl2 where "s2' -2-tl2\<rightarrow> s2''" "s1'' \<approx> s2''" "tl1 \<sim> tl2" by(auto dest: simulation1)
  ultimately have "s2 -2-tls2 @ [tl2]\<rightarrow>* s2''" "tls1 @ [tl1] [\<sim>] tls2 @ [tl2]"
    by(auto intro: rtrancl3p.rtrancl3p_step list_all2_appendI)
  with \<open>s1'' \<approx> s2''\<close> show ?case by(blast)
qed

lemma simulation2_rtrancl:
  "\<lbrakk>s2 -2-tls2\<rightarrow>* s2'; s1 \<approx> s2\<rbrakk>
  \<Longrightarrow> \<exists>s1' tls1. s1 -1-tls1\<rightarrow>* s1' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
using bisimulation.simulation1_rtrancl[OF bisimulation_flip]
unfolding flip_simps .

lemma simulation1_inf_step:
  assumes red1: "s1 -1-tls1\<rightarrow>* \<infinity>" and bisim: "s1 \<approx> s2"
  shows "\<exists>tls2. s2 -2-tls2\<rightarrow>* \<infinity> \<and> tls1 [[\<sim>]] tls2"
proof -
  from r1.inf_step_imp_inf_step_table[OF red1]
  obtain stls1 where red1': "s1 -1-stls1\<rightarrow>*t \<infinity>" 
    and tls1: "tls1 = lmap (fst \<circ> snd) stls1" by blast
  define tl1_to_tl2 where "tl1_to_tl2 s2 stls1 = unfold_llist
     (\<lambda>(s2, stls1). lnull stls1)
     (\<lambda>(s2, stls1). let (s1, tl1, s1') = lhd stls1;
                        (tl2, s2') = SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2
                    in (s2, tl2, s2'))
     (\<lambda>(s2, stls1). let (s1, tl1, s1') = lhd stls1;
                        (tl2, s2') = SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2
                    in (s2', ltl stls1))
     (s2, stls1)"
    for s2 :: 's2 and stls1 :: "('s1 \<times> 'tl1 \<times> 's1) llist"

  have tl1_to_tl2_simps [simp]:
    "\<And>s2 stls1. lnull (tl1_to_tl2 s2 stls1) \<longleftrightarrow> lnull stls1"
    "\<And>s2 stls1. \<not> lnull stls1 \<Longrightarrow> lhd (tl1_to_tl2 s2 stls1) =
    (let (s1, tl1, s1') = lhd stls1;
         (tl2, s2') = SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2
     in (s2, tl2, s2'))"
    "\<And>s2 stls1. \<not> lnull stls1 \<Longrightarrow> ltl (tl1_to_tl2 s2 stls1) =
    (let (s1, tl1, s1') = lhd stls1;
         (tl2, s2') = SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2
     in tl1_to_tl2 s2' (ltl stls1))"
    "\<And>s2. tl1_to_tl2 s2 LNil = LNil"
    "\<And>s2 s1 tl1 s1' stls1'. tl1_to_tl2 s2 (LCons (s1, tl1, s1') stls1') =
        LCons (s2, SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) 
              (tl1_to_tl2 (snd (SOME (tl2, s2'). trsys2 s2 tl2 s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2)) stls1')"
    by(simp_all add: tl1_to_tl2_def split_beta)

  have [simp]: "llength (tl1_to_tl2 s2 stls1) = llength stls1"
    by(coinduction arbitrary: s2 stls1 rule: enat_coinduct)(auto simp add: epred_llength split_beta)

  from red1' bisim have "s2 -2-tl1_to_tl2 s2 stls1\<rightarrow>*t \<infinity>"
  proof(coinduction arbitrary: s2 s1 stls1)
    case (inf_step_table s2 s1 stls1)
    note red1' = \<open>s1 -1-stls1\<rightarrow>*t \<infinity>\<close> and bisim = \<open>s1 \<approx> s2\<close>
    from red1' show ?case
    proof(cases)
      case (inf_step_tableI s1' stls1' tl1)
      hence stls1: "stls1 = LCons (s1, tl1, s1') stls1'"
        and r: "s1 -1-tl1\<rightarrow> s1'" and reds1: "s1' -1-stls1'\<rightarrow>*t \<infinity>" by simp_all
      let ?tl2s2' = "SOME (tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
      let ?tl2 = "fst ?tl2s2'" let ?s2' = "snd ?tl2s2'"
      from simulation1[OF bisim r] obtain s2' tl2
        where "s2 -2-tl2\<rightarrow> s2'" "s1' \<approx> s2'" "tl1 \<sim> tl2" by blast
      hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) (tl2, s2')" by simp
      hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) ?tl2s2'" by(rule someI)
      hence "s2 -2-?tl2\<rightarrow> ?s2'" "s1' \<approx> ?s2'" "tl1 \<sim> ?tl2" by(simp_all add: split_beta)
      then show ?thesis using reds1 stls1 by(fastforce intro: prod_eqI)
    qed
  qed
  hence "s2 -2-lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)\<rightarrow>* \<infinity>"
    by(rule r2.inf_step_table_imp_inf_step)
  moreover have "tls1 [[\<sim>]] lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)"
  proof(rule llist_all2_all_lnthI)
    show "llength tls1 = llength (lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1))"
      using tls1 by simp
  next
    fix n
    assume "enat n < llength tls1"
    thus "lnth tls1 n \<sim> lnth (lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)) n"
      using red1' bisim unfolding tls1
    proof(induct n arbitrary: s1 s2 stls1 rule: nat_less_induct)
      case (1 n)
      hence IH: "\<And>m s1 s2 stls1. \<lbrakk> m < n; enat m < llength (lmap (fst \<circ> snd) stls1);
                                   s1 -1-stls1\<rightarrow>*t \<infinity>; s1 \<approx> s2 \<rbrakk>
                 \<Longrightarrow> lnth (lmap (fst \<circ> snd) stls1) m \<sim> lnth (lmap (fst \<circ> snd) (tl1_to_tl2 s2 stls1)) m"
        by blast
      from \<open>s1 -1-stls1\<rightarrow>*t \<infinity>\<close> show ?case
      proof cases
        case (inf_step_tableI s1' stls1' tl1)
        hence  stls1: "stls1 = LCons (s1, tl1, s1') stls1'"
          and r: "s1 -1-tl1\<rightarrow> s1'" and reds: "s1' -1-stls1'\<rightarrow>*t \<infinity>" by simp_all
        let ?tl2s2' = "SOME (tl2, s2').  s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2"
        let ?tl2 = "fst ?tl2s2'" let ?s2' = "snd ?tl2s2'"
        from simulation1[OF \<open>s1 \<approx> s2\<close> r] obtain s2' tl2
          where "s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2" by blast
        hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) (tl2, s2')" by simp
        hence "(\<lambda>(tl2, s2'). s2 -2-tl2\<rightarrow> s2' \<and> s1' \<approx> s2' \<and> tl1 \<sim> tl2) ?tl2s2'" by(rule someI)
        hence bisim': "s1' \<approx> ?s2'" and tlsim: "tl1 \<sim> ?tl2" by(simp_all add: split_beta)
        show ?thesis
        proof(cases n)
          case 0
          with stls1 tlsim show ?thesis by simp
        next
          case (Suc m)
          hence "m < n" by simp
          moreover have "enat m < llength (lmap (fst \<circ> snd) stls1')"
            using stls1 \<open>enat n < llength (lmap (fst \<circ> snd) stls1)\<close> Suc by(simp add: Suc_ile_eq)
          ultimately have "lnth (lmap (fst \<circ> snd) stls1') m \<sim> lnth (lmap (fst \<circ> snd) (tl1_to_tl2 ?s2' stls1')) m"
            using reds bisim' by(rule IH)
          with Suc stls1 show ?thesis by(simp del: o_apply)
        qed
      qed
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma simulation2_inf_step:
  "\<lbrakk> s2 -2-tls2\<rightarrow>* \<infinity>; s1 \<approx> s2 \<rbrakk> \<Longrightarrow> \<exists>tls1. s1 -1-tls1\<rightarrow>* \<infinity> \<and> tls1 [[\<sim>]] tls2"
using bisimulation.simulation1_inf_step[OF bisimulation_flip]
unfolding flip_simps .

end

locale bisimulation_final_base =
  bisimulation_base + 
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  fixes final1 :: "'s1 \<Rightarrow> bool"
  and final2 :: "'s2 \<Rightarrow> bool"

locale bisimulation_final = bisimulation_final_base + bisimulation +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and final1 :: "'s1 \<Rightarrow> bool"
  and final2 :: "'s2 \<Rightarrow> bool"
  assumes bisim_final: "s1 \<approx> s2 \<Longrightarrow> final1 s1 \<longleftrightarrow> final2 s2"

begin

lemma bisimulation_final_flip:
  "bisimulation_final trsys2 trsys1 (flip bisim) (flip tlsim) final2 final1"
apply(intro_locales)
apply(rule bisimulation_flip)
apply(unfold_locales)
by(unfold flip_simps, rule bisim_final[symmetric])

end

lemma bisimulation_final_flip_simps [flip_simps]:
  "bisimulation_final trsys2 trsys1 (flip bisim) (flip tlsim) final2 final1 =
   bisimulation_final trsys1 trsys2 bisim tlsim final1 final2"
by(auto dest: bisimulation_final.bisimulation_final_flip simp only: flip_flip)

context bisimulation_final begin

lemma final_simulation1:
  "\<lbrakk> s1 \<approx> s2; s1 -1-tls1\<rightarrow>* s1'; final1 s1' \<rbrakk>
  \<Longrightarrow> \<exists>s2' tls2. s2 -2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> final2 s2' \<and> tls1 [\<sim>] tls2"
by(auto dest: bisim_final dest!: simulation1_rtrancl)

lemma final_simulation2:
  "\<lbrakk> s1 \<approx> s2; s2 -2-tls2\<rightarrow>* s2'; final2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' tls1. s1 -1-tls1\<rightarrow>* s1' \<and> s1' \<approx> s2' \<and> final1 s1' \<and> tls1 [\<sim>] tls2"
by(auto dest: bisim_final dest!: simulation2_rtrancl)

end

subsection \<open>Delay bisimulation\<close>

locale delay_bisimulation_base =
  bisimulation_base +
  trsys1?: \<tau>trsys trsys1 \<tau>move1 +
  trsys2?: \<tau>trsys trsys2 \<tau>move2 
  for \<tau>move1 \<tau>move2 +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
begin

notation
  trsys1.silent_move ("_/ -\<tau>1\<rightarrow> _" [50, 50] 60) and
  trsys2.silent_move ("_/ -\<tau>2\<rightarrow> _" [50, 50] 60)

notation
  trsys1.silent_moves ("_/ -\<tau>1\<rightarrow>* _" [50, 50] 60) and
  trsys2.silent_moves ("_/ -\<tau>2\<rightarrow>* _" [50, 50] 60)

notation
  trsys1.silent_movet ("_/ -\<tau>1\<rightarrow>+ _" [50, 50] 60) and
  trsys2.silent_movet ("_/ -\<tau>2\<rightarrow>+ _" [50, 50] 60)

notation
  trsys1.\<tau>rtrancl3p ("_ -\<tau>1-_\<rightarrow>* _" [50, 0, 50] 60) and
  trsys2.\<tau>rtrancl3p ("_ -\<tau>2-_\<rightarrow>* _" [50, 0, 50] 60)

notation
  trsys1.\<tau>inf_step ("_ -\<tau>1-_\<rightarrow>* \<infinity>" [50, 0] 80) and
  trsys2.\<tau>inf_step ("_ -\<tau>2-_\<rightarrow>* \<infinity>" [50, 0] 80)

notation
  trsys1.\<tau>diverge ("_ -\<tau>1\<rightarrow> \<infinity>" [50] 80) and
  trsys2.\<tau>diverge ("_ -\<tau>2\<rightarrow> \<infinity>" [50] 80)

notation
  trsys1.\<tau>inf_step_table ("_ -\<tau>1-_\<rightarrow>*t \<infinity>" [50, 0] 80) and
  trsys2.\<tau>inf_step_table ("_ -\<tau>2-_\<rightarrow>*t \<infinity>" [50, 0] 80)

notation
  trsys1.\<tau>Runs ("_ \<Down>1 _" [50, 50] 51) and
  trsys2.\<tau>Runs ("_ \<Down>2 _" [50, 50] 51)

lemma simulation_silent1I':
  assumes "\<exists>s2'. (if \<mu>1 s1' s1 then trsys2.silent_moves else trsys2.silent_movet) s2 s2' \<and> s1' \<approx> s2'"
  shows "s1' \<approx> s2 \<and> \<mu>1^++ s1' s1 \<or> (\<exists>s2'. s2 -\<tau>2\<rightarrow>+ s2' \<and> s1' \<approx> s2')"
proof -
  from assms obtain s2' where red: "(if \<mu>1 s1' s1 then trsys2.silent_moves else trsys2.silent_movet) s2 s2'" 
    and bisim: "s1' \<approx> s2'" by blast
  show ?thesis
  proof(cases "\<mu>1 s1' s1")
    case True
    with red have "s2 -\<tau>2\<rightarrow>* s2'" by simp
    thus ?thesis using bisim True by cases(blast intro: rtranclp_into_tranclp1)+
  next
    case False
    with red bisim show ?thesis by auto
  qed
qed

lemma simulation_silent2I':
  assumes "\<exists>s1'. (if \<mu>2 s2' s2 then trsys1.silent_moves else trsys1.silent_movet) s1 s1' \<and> s1' \<approx> s2'"
  shows "s1 \<approx> s2' \<and> \<mu>2^++ s2' s2 \<or> (\<exists>s1'. s1 -\<tau>1\<rightarrow>+ s1' \<and> s1' \<approx> s2')"
using assms
by(rule delay_bisimulation_base.simulation_silent1I')

end

locale delay_bisimulation_obs = delay_bisimulation_base _ _ _ _ \<tau>move1 \<tau>move2
  for \<tau>move1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>move2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool" +
  assumes simulation1:
  "\<lbrakk> s1 \<approx> s2; s1 -1-tl1\<rightarrow> s1'; \<not> \<tau>move1 s1 tl1 s1' \<rbrakk>
  \<Longrightarrow> \<exists>s2' s2'' tl2. s2 -\<tau>2\<rightarrow>* s2' \<and> s2' -2-tl2\<rightarrow> s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and> s1' \<approx> s2'' \<and> tl1 \<sim> tl2"
  and simulation2:
  "\<lbrakk> s1 \<approx> s2; s2 -2-tl2\<rightarrow> s2'; \<not> \<tau>move2 s2 tl2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' s1'' tl1. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' -1-tl1\<rightarrow> s1'' \<and> \<not> \<tau>move1 s1' tl1 s1'' \<and> s1'' \<approx> s2' \<and> tl1 \<sim> tl2"
begin

lemma delay_bisimulation_obs_flip: "delay_bisimulation_obs trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1"
apply(unfold_locales)
apply(unfold flip_simps)
by(blast intro: simulation1 simulation2)+

end

lemma delay_bisimulation_obs_flip_simps [flip_simps]:
  "delay_bisimulation_obs trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 =
   delay_bisimulation_obs trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
by(auto dest: delay_bisimulation_obs.delay_bisimulation_obs_flip simp only: flip_flip)

locale delay_bisimulation_diverge = delay_bisimulation_obs _ _ _ _ \<tau>move1 \<tau>move2
  for \<tau>move1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>move2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool" +
  assumes simulation_silent1:
  "\<lbrakk> s1 \<approx> s2; s1 -\<tau>1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'"
  and simulation_silent2:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2'"
  and \<tau>diverge_bisim_inv: "s1 \<approx> s2 \<Longrightarrow> s1 -\<tau>1\<rightarrow> \<infinity> \<longleftrightarrow> s2 -\<tau>2\<rightarrow> \<infinity>"
begin

lemma delay_bisimulation_diverge_flip: "delay_bisimulation_diverge trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1"
apply(rule delay_bisimulation_diverge.intro)
 apply(rule delay_bisimulation_obs_flip)
apply(unfold_locales)
apply(unfold flip_simps)
by(blast intro: simulation_silent1 simulation_silent2 \<tau>diverge_bisim_inv[symmetric] del: iffI)+

end


lemma delay_bisimulation_diverge_flip_simps [flip_simps]:
  "delay_bisimulation_diverge trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 =
   delay_bisimulation_diverge trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
by(auto dest: delay_bisimulation_diverge.delay_bisimulation_diverge_flip simp only: flip_flip)

context delay_bisimulation_diverge begin

lemma simulation_silents1:
  assumes bisim: "s1 \<approx> s2" and moves: "s1 -\<tau>1\<rightarrow>* s1'"
  shows "\<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'"
using moves bisim
proof induct
  case base thus ?case by(blast)
next
  case (step s1' s1'')
  from \<open>s1 \<approx> s2 \<Longrightarrow> \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'\<close> \<open>s1 \<approx> s2\<close>
  obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" "s1' \<approx> s2'" by blast
  from simulation_silent1[OF \<open>s1' \<approx> s2'\<close> \<open>s1' -\<tau>1\<rightarrow> s1''\<close>]
  obtain s2'' where "s2' -\<tau>2\<rightarrow>* s2''" "s1'' \<approx> s2''" by blast
  from \<open>s2 -\<tau>2\<rightarrow>* s2'\<close> \<open>s2' -\<tau>2\<rightarrow>* s2''\<close> have "s2 -\<tau>2\<rightarrow>* s2''" by(rule rtranclp_trans)
  with \<open>s1'' \<approx> s2''\<close> show ?case by blast
qed

lemma simulation_silents2:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2\<rightarrow>* s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2'"
using delay_bisimulation_diverge.simulation_silents1[OF delay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma simulation1_\<tau>rtrancl3p:
  "\<lbrakk> s1 -\<tau>1-tls1\<rightarrow>* s1'; s1 \<approx> s2 \<rbrakk>
  \<Longrightarrow> \<exists>tls2 s2'. s2 -\<tau>2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
proof(induct arbitrary: s2 rule: trsys1.\<tau>rtrancl3p.induct)
  case (\<tau>rtrancl3p_refl s)
  thus ?case by(auto intro: \<tau>trsys.\<tau>rtrancl3p.intros)
next
  case (\<tau>rtrancl3p_step s1 s1' tls1 s1'' tl1)
  from simulation1[OF \<open>s1 \<approx> s2\<close> \<open>s1 -1-tl1\<rightarrow> s1'\<close> \<open>\<not> \<tau>move1 s1 tl1 s1'\<close>]
  obtain s2' s2'' tl2 where \<tau>red: "s2 -\<tau>2\<rightarrow>* s2'"
    and red: "s2' -2-tl2\<rightarrow> s2''" and n\<tau>: "\<not> \<tau>move2 s2' tl2 s2''"
    and bisim': "s1' \<approx> s2''" and tlsim: "tl1 \<sim> tl2" by blast
  from bisim' \<open>s1' \<approx> s2'' \<Longrightarrow> \<exists>tls2 s2'. s2'' -\<tau>2-tls2\<rightarrow>* s2' \<and> s1'' \<approx> s2' \<and> tls1 [\<sim>] tls2\<close>
  obtain tls2 s2''' where IH: "s2'' -\<tau>2-tls2\<rightarrow>* s2'''" "s1'' \<approx> s2'''" "tls1 [\<sim>] tls2" by blast
  from \<tau>red have "s2 -\<tau>2-[]\<rightarrow>* s2'" by(rule trsys2.silent_moves_into_\<tau>rtrancl3p)
  also from red n\<tau> IH(1) have "s2' -\<tau>2-tl2 # tls2\<rightarrow>* s2'''" by(rule \<tau>rtrancl3p.\<tau>rtrancl3p_step)
  finally show ?case using IH tlsim by fastforce
next
  case (\<tau>rtrancl3p_\<tau>step s1 s1' tls1 s1'' tl1)
  from \<open>s1 -1-tl1\<rightarrow> s1'\<close> \<open>\<tau>move1 s1 tl1 s1'\<close> have "s1 -\<tau>1\<rightarrow> s1'" .. 
  from simulation_silent1[OF \<open>s1 \<approx> s2\<close> this]
  obtain s2' where \<tau>red: "s2 -\<tau>2\<rightarrow>* s2'" and bisim': "s1' \<approx> s2'" by blast
  from \<tau>red have "s2 -\<tau>2-[]\<rightarrow>* s2'" by(rule trsys2.silent_moves_into_\<tau>rtrancl3p)
  also from bisim' \<open>s1' \<approx> s2' \<Longrightarrow> \<exists>tls2 s2''. s2' -\<tau>2-tls2\<rightarrow>* s2'' \<and> s1'' \<approx> s2'' \<and> tls1 [\<sim>] tls2\<close>
  obtain tls2 s2'' where IH: "s2' -\<tau>2-tls2\<rightarrow>* s2''" "s1'' \<approx> s2''" "tls1 [\<sim>] tls2" by blast
  note \<open>s2' -\<tau>2-tls2\<rightarrow>* s2''\<close>
  finally show ?case using IH by auto
qed

lemma simulation2_\<tau>rtrancl3p:
  "\<lbrakk> s2 -\<tau>2-tls2\<rightarrow>* s2'; s1 \<approx> s2 \<rbrakk>
  \<Longrightarrow> \<exists>tls1 s1'. s1 -\<tau>1-tls1\<rightarrow>* s1' \<and> s1' \<approx> s2' \<and> tls1 [\<sim>] tls2"
using delay_bisimulation_diverge.simulation1_\<tau>rtrancl3p[OF delay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma simulation1_\<tau>inf_step:
  assumes \<tau>inf1: "s1 -\<tau>1-tls1\<rightarrow>* \<infinity>" and bisim: "s1 \<approx> s2"
  shows "\<exists>tls2. s2 -\<tau>2-tls2\<rightarrow>* \<infinity> \<and> tls1 [[\<sim>]] tls2"
proof -
  from trsys1.\<tau>inf_step_imp_\<tau>inf_step_table[OF \<tau>inf1]
  obtain sstls1 where \<tau>inf1': "s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>" 
    and tls1: "tls1 = lmap (fst \<circ> snd \<circ> snd) sstls1" by blast
  define tl1_to_tl2 where "tl1_to_tl2 s2 sstls1 = unfold_llist
     (\<lambda>(s2, sstls1). lnull sstls1)
     (\<lambda>(s2, sstls1).
        let (s1, s1', tl1, s1'') = lhd sstls1;
            (s2', tl2, s2'') = SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                     \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2
        in (s2, s2', tl2, s2''))
     (\<lambda>(s2, sstls1). 
        let (s1, s1', tl1, s1'') = lhd sstls1;
            (s2', tl2, s2'') = SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                     \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2
        in (s2'', ltl sstls1))
     (s2, sstls1)"
    for s2 :: 's2 and sstls1 :: "('s1 \<times> 's1 \<times> 'tl1 \<times> 's1) llist"
  have [simp]:
    "\<And>s2 sstls1. lnull (tl1_to_tl2 s2 sstls1) \<longleftrightarrow> lnull sstls1"
    "\<And>s2 sstls1. \<not> lnull sstls1 \<Longrightarrow> lhd (tl1_to_tl2 s2 sstls1) =
        (let (s1, s1', tl1, s1'') = lhd sstls1;
            (s2', tl2, s2'') = SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                     \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2
        in (s2, s2', tl2, s2''))"
    "\<And>s2 sstls1. \<not> lnull sstls1 \<Longrightarrow> ltl (tl1_to_tl2 s2 sstls1) =
        (let (s1, s1', tl1, s1'') = lhd sstls1;
            (s2', tl2, s2'') = SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                     \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2
        in tl1_to_tl2 s2'' (ltl sstls1))"
    "\<And>s2. tl1_to_tl2 s2 LNil = LNil"
    "\<And>s2 s1 s1' tl1 s1'' stls1'. tl1_to_tl2 s2 (LCons (s1, s1', tl1, s1'') stls1') =
        LCons (s2, SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and> 
                                          \<not> \<tau>move2 s2' tl2 s2'' \<and> s1'' \<approx> s2'' \<and> tl1 \<sim> tl2) 
              (tl1_to_tl2 (snd (snd (SOME (s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and>
                                                            \<not> \<tau>move2 s2' tl2 s2'' \<and> s1'' \<approx> s2'' \<and> tl1 \<sim> tl2)))
                           stls1')"
    by(simp_all add: tl1_to_tl2_def split_beta)

  have [simp]: "llength (tl1_to_tl2 s2 sstls1) = llength sstls1"
    by(coinduction arbitrary: s2 sstls1 rule: enat_coinduct)(auto simp add: epred_llength split_beta)

  define sstls2 where "sstls2 = tl1_to_tl2 s2 sstls1"
  with \<tau>inf1' bisim have "\<exists>s1 sstls1. s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity> \<and> sstls2 = tl1_to_tl2 s2 sstls1 \<and> s1 \<approx> s2" by blast

  from \<tau>inf1' bisim have "s2 -\<tau>2-tl1_to_tl2 s2 sstls1\<rightarrow>*t \<infinity>"
  proof(coinduction arbitrary: s2 s1 sstls1)
    case (\<tau>inf_step_table s2 s1 sstls1)
    note \<tau>inf' = \<open>s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>\<close> and bisim = \<open>s1 \<approx> s2\<close>
    from \<tau>inf' show ?case
    proof(cases)
      case (\<tau>inf_step_table_Cons s1' s1'' sstls1' tl1)
      hence sstls1: "sstls1 = LCons (s1, s1', tl1, s1'') sstls1'"
        and \<tau>s: "s1 -\<tau>1\<rightarrow>* s1'" and r: "s1' -1-tl1\<rightarrow> s1''" and n\<tau>: "\<not> \<tau>move1 s1' tl1 s1''"
        and reds1: "s1'' -\<tau>1-sstls1'\<rightarrow>*t \<infinity>" by simp_all
      let ?P = "\<lambda>(s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2"
      let ?s2tl2s2' = "Eps ?P"
      let ?s2'' = "snd (snd ?s2tl2s2')"
      from simulation_silents1[OF \<open>s1 \<approx> s2\<close> \<tau>s]
      obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" "s1' \<approx> s2'" by blast
      from simulation1[OF \<open>s1' \<approx> s2'\<close> r n\<tau>] obtain s2'' s2''' tl2
        where "s2' -\<tau>2\<rightarrow>* s2''" 
        and rest: "s2'' -2-tl2\<rightarrow> s2'''" "\<not> \<tau>move2 s2'' tl2 s2'''" "s1'' \<approx> s2'''" "tl1 \<sim> tl2" by blast
      from \<open>s2 -\<tau>2\<rightarrow>* s2'\<close> \<open>s2' -\<tau>2\<rightarrow>* s2''\<close> have "s2 -\<tau>2\<rightarrow>* s2''" by(rule rtranclp_trans)
      with rest have "?P (s2'', tl2, s2''')" by simp
      hence "?P ?s2tl2s2'" by(rule someI)
      then show ?thesis using reds1 sstls1 by fastforce
    next
      case \<tau>inf_step_table_Nil
      hence [simp]: "sstls1 = LNil" and "s1 -\<tau>1\<rightarrow> \<infinity>" by simp_all
      from \<open>s1 -\<tau>1\<rightarrow> \<infinity>\<close> \<open>s1 \<approx> s2\<close> have "s2 -\<tau>2\<rightarrow> \<infinity>" by(simp add: \<tau>diverge_bisim_inv)
      thus ?thesis using sstls2_def by simp
    qed
  qed
  hence "s2 -\<tau>2-lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)\<rightarrow>* \<infinity>"
    by(rule trsys2.\<tau>inf_step_table_into_\<tau>inf_step)
  moreover have "tls1 [[\<sim>]] lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)"
  proof(rule llist_all2_all_lnthI)
    show "llength tls1 = llength (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1))"
      using tls1 by simp
  next
    fix n
    assume "enat n < llength tls1"
    thus "lnth tls1 n \<sim> lnth (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)) n"
      using \<tau>inf1' bisim unfolding tls1
    proof(induct n arbitrary: s1 s2 sstls1 rule: less_induct)
      case (less n)
      note IH = \<open>\<And>m s1 s2 sstls1. \<lbrakk> m < n; enat m < llength (lmap (fst \<circ> snd \<circ> snd) sstls1);
                                   s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>; s1 \<approx> s2 \<rbrakk>
                 \<Longrightarrow> lnth (lmap (fst \<circ> snd \<circ> snd) sstls1) m \<sim> lnth (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 s2 sstls1)) m\<close>
      from \<open>s1 -\<tau>1-sstls1\<rightarrow>*t \<infinity>\<close> show ?case
      proof cases
        case (\<tau>inf_step_table_Cons s1' s1'' sstls1' tl1)
        hence sstls1: "sstls1 = LCons (s1, s1', tl1, s1'') sstls1'"
          and \<tau>s: "s1 -\<tau>1\<rightarrow>* s1'" and r: "s1' -1-tl1\<rightarrow> s1''"
          and n\<tau>: "\<not> \<tau>move1 s1' tl1 s1''" and reds: "s1'' -\<tau>1-sstls1'\<rightarrow>*t \<infinity>" by simp_all
        let ?P = "\<lambda>(s2', tl2, s2''). s2 -\<tau>2\<rightarrow>* s2' \<and> trsys2 s2' tl2 s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and>  s1'' \<approx> s2'' \<and> tl1 \<sim> tl2"
        let ?s2tl2s2' = "Eps ?P" let ?tl2 = "fst (snd ?s2tl2s2')" let ?s2'' = "snd (snd ?s2tl2s2')"
        from simulation_silents1[OF \<open>s1 \<approx> s2\<close> \<tau>s] obtain s2'
          where "s2 -\<tau>2\<rightarrow>* s2'" "s1' \<approx> s2'" by blast
        from simulation1[OF \<open>s1' \<approx> s2'\<close> r n\<tau>] obtain s2'' s2''' tl2
          where "s2' -\<tau>2\<rightarrow>* s2''"
          and rest: "s2'' -2-tl2\<rightarrow> s2'''" "\<not> \<tau>move2 s2'' tl2 s2'''" "s1'' \<approx> s2'''" "tl1 \<sim> tl2" by blast
        from \<open>s2 -\<tau>2\<rightarrow>* s2'\<close> \<open>s2' -\<tau>2\<rightarrow>* s2''\<close> have "s2 -\<tau>2\<rightarrow>* s2''" by(rule rtranclp_trans)
        with rest have "?P (s2'', tl2, s2''')" by auto
        hence "?P ?s2tl2s2'" by(rule someI)
        hence "s1'' \<approx> ?s2''" "tl1 \<sim> ?tl2" by(simp_all add: split_beta)
        show ?thesis
        proof(cases n)
          case 0
          with sstls1 \<open>tl1 \<sim> ?tl2\<close> show ?thesis by simp
        next
          case (Suc m)
          hence "m < n" by simp
          moreover have "enat m < llength (lmap (fst \<circ> snd \<circ> snd) sstls1')"
            using sstls1 \<open>enat n < llength (lmap (fst \<circ> snd \<circ> snd) sstls1)\<close> Suc by(simp add: Suc_ile_eq)
          ultimately have "lnth (lmap (fst \<circ> snd \<circ> snd) sstls1') m \<sim> lnth (lmap (fst \<circ> snd \<circ> snd) (tl1_to_tl2 ?s2'' sstls1')) m"
            using reds \<open>s1'' \<approx> ?s2''\<close> by(rule IH)
          with Suc sstls1 show ?thesis by(simp del: o_apply)
        qed
      next
        case \<tau>inf_step_table_Nil
        with \<open>enat n < llength (lmap (fst \<circ> snd \<circ> snd) sstls1)\<close> have False by simp
        thus ?thesis ..
      qed
    qed
  qed
  ultimately show ?thesis by blast
qed

lemma simulation2_\<tau>inf_step:
  "\<lbrakk> s2 -\<tau>2-tls2\<rightarrow>* \<infinity>; s1 \<approx> s2 \<rbrakk> \<Longrightarrow> \<exists>tls1. s1 -\<tau>1-tls1\<rightarrow>* \<infinity> \<and> tls1 [[\<sim>]] tls2"
using delay_bisimulation_diverge.simulation1_\<tau>inf_step[OF delay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma no_\<tau>move1_\<tau>s_to_no_\<tau>move2:
  assumes "s1 \<approx> s2"
  and no_\<tau>moves1: "\<And>s1'. \<not> s1 -\<tau>1\<rightarrow> s1'"
  shows "\<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> (\<forall>s2''. \<not> s2' -\<tau>2\<rightarrow> s2'') \<and> s1 \<approx> s2'"
proof -
  have "\<not> s1 -\<tau>1\<rightarrow> \<infinity>"
  proof
    assume "s1 -\<tau>1\<rightarrow> \<infinity>"
    then obtain s1' where "s1 -\<tau>1\<rightarrow> s1'" by cases
    with no_\<tau>moves1[of s1'] show False by contradiction
  qed
  with \<open>s1 \<approx> s2\<close> have "\<not> s2 -\<tau>2\<rightarrow> \<infinity>" by(simp add: \<tau>diverge_bisim_inv)
  from trsys2.not_\<tau>diverge_to_no_\<tau>move[OF this]
  obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" and "\<And>s2''. \<not> s2' -\<tau>2\<rightarrow> s2''" by blast
  moreover from simulation_silents2[OF \<open>s1 \<approx> s2\<close> \<open>s2 -\<tau>2\<rightarrow>* s2'\<close>]
  obtain s1' where "s1 -\<tau>1\<rightarrow>* s1'" and "s1' \<approx> s2'" by blast
  from \<open>s1 -\<tau>1\<rightarrow>* s1'\<close> no_\<tau>moves1 have "s1' = s1"
    by(auto elim: converse_rtranclpE)
  ultimately show ?thesis using \<open>s1' \<approx> s2'\<close> by blast
qed

lemma no_\<tau>move2_\<tau>s_to_no_\<tau>move1:
  "\<lbrakk> s1 \<approx> s2; \<And>s2'. \<not> s2 -\<tau>2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> \<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> (\<forall>s1''. \<not> s1' -\<tau>1\<rightarrow> s1'') \<and> s1' \<approx> s2"
using delay_bisimulation_diverge.no_\<tau>move1_\<tau>s_to_no_\<tau>move2[OF delay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma no_move1_to_no_move2:
  assumes "s1 \<approx> s2"
  and no_moves1: "\<And>tl1 s1'. \<not> s1 -1-tl1\<rightarrow> s1'"
  shows "\<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> (\<forall>tl2 s2''. \<not> s2' -2-tl2\<rightarrow> s2'') \<and> s1 \<approx> s2'"
proof -
  from no_moves1 have "\<And>s1'. \<not> s1 -\<tau>1\<rightarrow> s1'" by(auto)
  from no_\<tau>move1_\<tau>s_to_no_\<tau>move2[OF \<open>s1 \<approx> s2\<close> this]
  obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" and "s1 \<approx> s2'" 
    and no_\<tau>moves2: "\<And>s2''. \<not> s2' -\<tau>2\<rightarrow> s2''" by blast
  moreover
  have "\<And>tl2 s2''. \<not> s2' -2-tl2\<rightarrow> s2''"
  proof
    fix tl2 s2''
    assume "s2' -2-tl2\<rightarrow> s2''"
    with no_\<tau>moves2[of s2''] have "\<not> \<tau>move2 s2' tl2 s2''" by(auto)
    from simulation2[OF \<open>s1 \<approx> s2'\<close> \<open>s2' -2-tl2\<rightarrow> s2''\<close> this]
    obtain s1' s1'' tl1 where "s1 -\<tau>1\<rightarrow>* s1'" and "s1' -1-tl1\<rightarrow> s1''" by blast
    with no_moves1 show False by(fastforce elim: converse_rtranclpE)
  qed
  ultimately show ?thesis by blast
qed

lemma no_move2_to_no_move1:
  "\<lbrakk> s1 \<approx> s2; \<And>tl2 s2'. \<not> s2 -2-tl2\<rightarrow> s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> (\<forall>tl1 s1''. \<not> s1' -1-tl1\<rightarrow> s1'') \<and> s1' \<approx> s2"
using delay_bisimulation_diverge.no_move1_to_no_move2[OF delay_bisimulation_diverge_flip]
unfolding flip_simps .

lemma simulation_\<tau>Runs_table1:
  assumes bisim: "s1 \<approx> s2"
  and run1: "trsys1.\<tau>Runs_table s1 stlsss1"
  shows "\<exists>stlsss2. trsys2.\<tau>Runs_table s2 stlsss2 \<and> tllist_all2 (\<lambda>(tl1, s1'') (tl2, s2''). tl1 \<sim> tl2 \<and> s1'' \<approx> s2'') (rel_option bisim) stlsss1 stlsss2"
proof(intro exI conjI)
  let ?P = "\<lambda>(s2 :: 's2) (stlsss1 :: ('tl1 \<times> 's1, 's1 option) tllist) (tl2, s2'').
    \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s2' -2-tl2\<rightarrow> s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and> snd (thd stlsss1) \<approx> s2'' \<and> fst (thd stlsss1) \<sim> tl2"
  define tls1_to_tls2 where "tls1_to_tls2 s2 stlsss1 = unfold_tllist
      (\<lambda>(s2, stlsss1). is_TNil stlsss1)
      (\<lambda>(s2, stlsss1). map_option (\<lambda>s1'. SOME s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> (\<forall>tl s2''. \<not> s2' -2-tl\<rightarrow> s2'') \<and> s1' \<approx> s2') (terminal stlsss1))
      (\<lambda>(s2, stlsss1). let (tl2, s2'') = Eps (?P s2 stlsss1) in (tl2, s2''))
      (\<lambda>(s2, stlsss1). let (tl2, s2'') = Eps (?P s2 stlsss1) in (s2'', ttl stlsss1))
      (s2, stlsss1)"
    for s2 stlsss1
  have [simp]:
    "\<And>s2 stlsss1. is_TNil (tls1_to_tls2 s2 stlsss1) \<longleftrightarrow> is_TNil stlsss1"
    "\<And>s2 stlsss1. is_TNil stlsss1 \<Longrightarrow> terminal (tls1_to_tls2 s2 stlsss1) = map_option (\<lambda>s1'. SOME s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> (\<forall>tl s2''. \<not> s2' -2-tl\<rightarrow> s2'') \<and> s1' \<approx> s2') (terminal stlsss1)"
    "\<And>s2 stlsss1. \<not> is_TNil stlsss1 \<Longrightarrow> thd (tls1_to_tls2 s2 stlsss1) = (let (tl2, s2'') = Eps (?P s2 stlsss1) in (tl2, s2''))"
    "\<And>s2 stlsss1. \<not> is_TNil stlsss1 \<Longrightarrow> ttl (tls1_to_tls2 s2 stlsss1) = (let (tl2, s2'') = Eps (?P s2 stlsss1) in tls1_to_tls2 s2'' (ttl stlsss1))"
    "\<And>s2 os1. tls1_to_tls2 s2 (TNil os1) = 
               TNil (map_option (\<lambda>s1'. SOME s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> (\<forall>tl s2''. \<not> s2' -2-tl\<rightarrow> s2'') \<and> s1' \<approx> s2') os1)"
    by(simp_all add: tls1_to_tls2_def split_beta)
  have [simp]:
    "\<And>s2 s1 s1' tl1 s1'' stlsss1. 
     tls1_to_tls2 s2 (TCons (tl1, s1'') stlsss1) =
     (let (tl2, s2'') = SOME (tl2, s2''). \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s2' -2-tl2\<rightarrow> s2'' \<and> 
                             \<not> \<tau>move2 s2' tl2 s2'' \<and> s1'' \<approx> s2'' \<and> tl1 \<sim> tl2
      in TCons (tl2, s2'') (tls1_to_tls2 s2'' stlsss1))"
    by(rule tllist.expand)(simp_all add: split_beta)

  from bisim run1
  show "trsys2.\<tau>Runs_table s2 (tls1_to_tls2 s2 stlsss1)"
  proof(coinduction arbitrary: s2 s1 stlsss1)
    case (\<tau>Runs_table s2 s1 stlsss1)
    note bisim = \<open>s1 \<approx> s2\<close>
      and run1 = \<open>trsys1.\<tau>Runs_table s1 stlsss1\<close>
    from run1 show ?case
    proof cases
      case (Terminate s1')
      let ?P = "\<lambda>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> (\<forall>tl2 s2''. \<not> s2' -2-tl2\<rightarrow> s2'') \<and> s1' \<approx> s2'"
      from simulation_silents1[OF bisim \<open>s1 -\<tau>1\<rightarrow>* s1'\<close>]
      obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" and "s1' \<approx> s2'" by blast
      moreover from no_move1_to_no_move2[OF \<open>s1' \<approx> s2'\<close> \<open>\<And>tl1 s1''. \<not> s1' -1-tl1\<rightarrow> s1''\<close>]
      obtain s2'' where "s2' -\<tau>2\<rightarrow>* s2''" and "s1' \<approx> s2''" 
        and "\<And>tl2 s2'''. \<not> s2'' -2-tl2\<rightarrow> s2'''" by blast
      ultimately have "?P s2''" by(blast intro: rtranclp_trans)
      hence "?P (Eps ?P)" by(rule someI)
      hence ?Terminate using \<open>stlsss1 = TNil \<lfloor>s1'\<rfloor>\<close> by simp
      thus ?thesis ..
    next
      case Diverge
      with \<tau>diverge_bisim_inv[OF bisim]
      have ?Diverge by simp
      thus ?thesis by simp
    next
      case (Proceed s1' s1'' stlsss1' tl1)
      let ?P = "\<lambda>(tl2, s2''). \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s2' -2-tl2\<rightarrow> s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and> s1'' \<approx> s2'' \<and> tl1 \<sim> tl2"
      from simulation_silents1[OF bisim \<open>s1 -\<tau>1\<rightarrow>* s1'\<close>]
      obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" and "s1' \<approx> s2'" by blast
      moreover from simulation1[OF \<open>s1' \<approx> s2'\<close> \<open>s1' -1-tl1\<rightarrow> s1''\<close> \<open>\<not> \<tau>move1 s1' tl1 s1''\<close>]
      obtain s2'' s2''' tl2 where "s2' -\<tau>2\<rightarrow>* s2''"
        and "s2'' -2-tl2\<rightarrow> s2'''" and "\<not> \<tau>move2 s2'' tl2 s2'''"
        and "s1'' \<approx> s2'''" and "tl1 \<sim> tl2" by blast
      ultimately have "?P (tl2, s2''')" by(blast intro: rtranclp_trans)
      hence "?P (Eps ?P)" by(rule someI)
      hence ?Proceed 
        using \<open>stlsss1 = TCons (tl1, s1'') stlsss1'\<close> \<open>trsys1.\<tau>Runs_table s1'' stlsss1'\<close>
        by auto blast
      thus ?thesis by simp
    qed
  qed

  let ?Tlsim = "\<lambda>(tl1, s1'') (tl2, s2''). tl1 \<sim> tl2 \<and> s1'' \<approx> s2''"
  let ?Bisim = "rel_option bisim"
  from run1 bisim
  show "tllist_all2 ?Tlsim ?Bisim stlsss1 (tls1_to_tls2 s2 stlsss1)"
  proof(coinduction arbitrary: s1 s2 stlsss1)
    case (tllist_all2 s1 s2 stlsss1)
    note Runs = \<open>trsys1.\<tau>Runs_table s1 stlsss1\<close> and bisim = \<open>s1 \<approx> s2\<close>
    from Runs show ?case
    proof cases
      case (Terminate s1')
      let ?P = "\<lambda>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> (\<forall>tl2 s2''. \<not> s2' -2-tl2\<rightarrow> s2'') \<and> s1' \<approx> s2'"
      from simulation_silents1[OF bisim \<open>s1 -\<tau>1\<rightarrow>* s1'\<close>]
      obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" and "s1' \<approx> s2'" by blast
      moreover
      from no_move1_to_no_move2[OF \<open>s1' \<approx> s2'\<close> \<open>\<And>tl1 s1''. \<not> s1' -1-tl1\<rightarrow> s1''\<close>]
      obtain s2'' where "s2' -\<tau>2\<rightarrow>* s2''" and "s1' \<approx> s2''"
        and "\<And>tl2 s2'''. \<not> s2'' -2-tl2\<rightarrow> s2'''" by blast
      ultimately have "?P s2''" by(blast intro: rtranclp_trans)
      hence "?P (Eps ?P)" by(rule someI)
      thus ?thesis using \<open>stlsss1 = TNil \<lfloor>s1'\<rfloor>\<close> bisim by(simp)
    next
      case (Proceed s1' s1'' stlsss1' tl1)
      from simulation_silents1[OF bisim \<open>s1 -\<tau>1\<rightarrow>* s1'\<close>]
      obtain s2' where "s2 -\<tau>2\<rightarrow>* s2'" and "s1' \<approx> s2'" by blast
      moreover from simulation1[OF \<open>s1' \<approx> s2'\<close> \<open>s1' -1-tl1\<rightarrow> s1''\<close> \<open>\<not> \<tau>move1 s1' tl1 s1''\<close>]
      obtain s2'' s2''' tl2 where "s2' -\<tau>2\<rightarrow>* s2''"
        and "s2'' -2-tl2\<rightarrow> s2'''" and "\<not> \<tau>move2 s2'' tl2 s2'''"
        and "s1'' \<approx> s2'''" and "tl1 \<sim> tl2" by blast
      ultimately have "?P s2 stlsss1 (tl2, s2''')"
        using \<open>stlsss1 = TCons (tl1, s1'') stlsss1'\<close> by(auto intro: rtranclp_trans)
      hence "?P s2 stlsss1 (Eps (?P s2 stlsss1))" by(rule someI)
      thus ?thesis using \<open>stlsss1 = TCons (tl1, s1'') stlsss1'\<close> \<open>trsys1.\<tau>Runs_table s1'' stlsss1'\<close> bisim
        by auto blast
    qed simp
  qed
qed

lemma simulation_\<tau>Runs_table2:
  assumes "s1 \<approx> s2"
  and "trsys2.\<tau>Runs_table s2 stlsss2"
  shows "\<exists>stlsss1. trsys1.\<tau>Runs_table s1 stlsss1 \<and> tllist_all2 (\<lambda>(tl1, s1'') (tl2, s2''). tl1 \<sim> tl2 \<and> s1'' \<approx> s2'') (rel_option bisim) stlsss1 stlsss2"
using delay_bisimulation_diverge.simulation_\<tau>Runs_table1[OF delay_bisimulation_diverge_flip, unfolded flip_simps, OF assms]
by(subst tllist_all2_flip[symmetric])(simp only: flip_def split_def)

lemma simulation_\<tau>Runs1:
  assumes bisim: "s1 \<approx> s2"
  and run1: "s1 \<Down>1 tls1"
  shows "\<exists>tls2. s2 \<Down>2 tls2 \<and> tllist_all2 tlsim (rel_option bisim) tls1 tls2"
proof -
  from trsys1.\<tau>Runs_into_\<tau>Runs_table[OF run1]
  obtain stlsss1 where tls1: "tls1 = tmap fst id stlsss1"
    and \<tau>Runs1: "trsys1.\<tau>Runs_table s1 stlsss1" by blast
  from simulation_\<tau>Runs_table1[OF bisim \<tau>Runs1]
  obtain stlsss2 where \<tau>Runs2: "trsys2.\<tau>Runs_table s2 stlsss2"
    and tlsim: "tllist_all2 (\<lambda>(tl1, s1'') (tl2, s2''). tl1 \<sim> tl2 \<and> s1'' \<approx> s2'')
                            (rel_option bisim) stlsss1 stlsss2" by blast
  from \<tau>Runs2 have "s2 \<Down>2 tmap fst id stlsss2"
    by(rule \<tau>Runs_table_into_\<tau>Runs)
  moreover have "tllist_all2 tlsim (rel_option bisim) tls1 (tmap fst id stlsss2)"
    using tlsim unfolding tls1
    by(fastforce simp add: tllist_all2_tmap1 tllist_all2_tmap2 elim: tllist_all2_mono rel_option_mono)
  ultimately show ?thesis by blast
qed

lemma simulation_\<tau>Runs2:
  "\<lbrakk> s1 \<approx> s2; s2 \<Down>2 tls2 \<rbrakk>
  \<Longrightarrow> \<exists>tls1. s1 \<Down>1 tls1 \<and> tllist_all2 tlsim (rel_option bisim) tls1 tls2"
using delay_bisimulation_diverge.simulation_\<tau>Runs1[OF delay_bisimulation_diverge_flip]
unfolding flip_simps .

end

locale delay_bisimulation_final_base =
  delay_bisimulation_base _ _ _ _ \<tau>move1 \<tau>move2 +
  bisimulation_final_base _ _ _ _ final1 final2 
  for \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
  and final1 :: "'s1 \<Rightarrow> bool"
  and final2 :: "'s2 \<Rightarrow> bool" +
  assumes final1_simulation: "\<lbrakk> s1 \<approx> s2; final1 s1 \<rbrakk> \<Longrightarrow> \<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1 \<approx> s2' \<and> final2 s2'"
  and final2_simulation: "\<lbrakk> s1 \<approx> s2; final2 s2 \<rbrakk> \<Longrightarrow> \<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2 \<and> final1 s1'"
begin

lemma delay_bisimulation_final_base_flip:
  "delay_bisimulation_final_base trsys2 trsys1 (flip bisim) \<tau>move2 \<tau>move1 final2 final1"
apply(unfold_locales)
apply(unfold flip_simps)
by(blast intro: final1_simulation final2_simulation)+

end

lemma delay_bisimulation_final_base_flip_simps [flip_simps]:
  "delay_bisimulation_final_base trsys2 trsys1 (flip bisim) \<tau>move2 \<tau>move1 final2 final1 =
  delay_bisimulation_final_base trsys1 trsys2 bisim \<tau>move1 \<tau>move2 final1 final2"
by(auto dest: delay_bisimulation_final_base.delay_bisimulation_final_base_flip simp only: flip_flip)

context delay_bisimulation_final_base begin

lemma \<tau>Runs_terminate_final1:
  assumes "s1 \<Down>1 tls1"
  and "s2 \<Down>2 tls2"
  and "tllist_all2 tlsim (rel_option bisim) tls1 tls2"
  and "tfinite tls1"
  and "terminal tls1 = Some s1'"
  and "final1 s1'"
  shows "\<exists>s2'. tfinite tls2 \<and> terminal tls2 = Some s2' \<and> final2 s2'"
using assms(4) assms(1-3,5-)
apply(induct arbitrary: tls2 s1 s2 rule: tfinite_induct)
apply(auto 4 4 simp add: tllist_all2_TCons1 tllist_all2_TNil1 rel_option_Some1 trsys1.\<tau>Runs_simps trsys2.\<tau>Runs_simps dest: final1_simulation elim: converse_rtranclpE)
done

lemma \<tau>Runs_terminate_final2:
  "\<lbrakk> s1 \<Down>1 tls1; s2 \<Down>2 tls2; tllist_all2 tlsim (rel_option bisim) tls1 tls2;
     tfinite tls2; terminal tls2 = Some s2'; final2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1'. tfinite tls1 \<and> terminal tls1 = Some s1' \<and> final1 s1'"
using delay_bisimulation_final_base.\<tau>Runs_terminate_final1[where tlsim = "flip tlsim", OF delay_bisimulation_final_base_flip]
unfolding flip_simps by -

end

locale delay_bisimulation_diverge_final = 
  delay_bisimulation_diverge + 
  delay_bisimulation_final_base +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
  and final1 :: "'s1 \<Rightarrow> bool"
  and final2 :: "'s2 \<Rightarrow> bool"
begin

lemma delay_bisimulation_diverge_final_flip:
  "delay_bisimulation_diverge_final trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 final2 final1"
apply(rule delay_bisimulation_diverge_final.intro)
 apply(rule delay_bisimulation_diverge_flip)
apply(unfold_locales, unfold flip_simps)
apply(blast intro: final1_simulation final2_simulation)+
done

end

lemma delay_bisimulation_diverge_final_flip_simps [flip_simps]:
  "delay_bisimulation_diverge_final trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 final2 final1 =
   delay_bisimulation_diverge_final trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 final1 final2"
by(auto dest: delay_bisimulation_diverge_final.delay_bisimulation_diverge_final_flip simp only: flip_flip)

context delay_bisimulation_diverge_final begin

lemma delay_bisimulation_diverge:
  "delay_bisimulation_diverge trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
by(unfold_locales)

lemma delay_bisimulation_final_base:
  "delay_bisimulation_final_base trsys1 trsys2 bisim \<tau>move1 \<tau>move2 final1 final2"
by(unfold_locales)

lemma final_simulation1:
  "\<lbrakk> s1 \<approx> s2; s1 -\<tau>1-tls1\<rightarrow>* s1'; final1 s1' \<rbrakk>
  \<Longrightarrow> \<exists>s2' tls2. s2 -\<tau>2-tls2\<rightarrow>* s2' \<and> s1' \<approx> s2' \<and> final2 s2' \<and> tls1 [\<sim>] tls2"
by(blast dest: simulation1_\<tau>rtrancl3p final1_simulation intro: \<tau>rtrancl3p_trans[OF _ silent_moves_into_\<tau>rtrancl3p, simplified])

lemma final_simulation2:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2-tls2\<rightarrow>* s2'; final2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' tls1. s1 -\<tau>1-tls1\<rightarrow>* s1' \<and> s1' \<approx> s2' \<and> final1 s1' \<and> tls1 [\<sim>] tls2"
by(rule delay_bisimulation_diverge_final.final_simulation1[OF delay_bisimulation_diverge_final_flip, unfolded flip_simps])

end

locale delay_bisimulation_measure_base = 
  delay_bisimulation_base +
  constrains trsys1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and trsys2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool"
  and bisim :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
  and tlsim :: "'tl1 \<Rightarrow> 'tl2 \<Rightarrow> bool"
  and \<tau>move1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>move2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool"
  fixes \<mu>1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<mu>2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool"

locale delay_bisimulation_measure =
  delay_bisimulation_measure_base _ _ _ _ \<tau>move1 \<tau>move2 \<mu>1 \<mu>2 +
  delay_bisimulation_obs trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2
  for \<tau>move1 :: "'s1 \<Rightarrow> 'tl1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>move2 :: "'s2 \<Rightarrow> 'tl2 \<Rightarrow> 's2 \<Rightarrow> bool"
  and \<mu>1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<mu>2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool" +
  assumes simulation_silent1:
  "\<lbrakk> s1 \<approx> s2; s1 -\<tau>1\<rightarrow> s1' \<rbrakk> \<Longrightarrow> s1' \<approx> s2 \<and> \<mu>1^++ s1' s1 \<or> (\<exists>s2'. s2 -\<tau>2\<rightarrow>+ s2' \<and> s1' \<approx> s2')"
  and simulation_silent2:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> s1 \<approx> s2' \<and> \<mu>2^++ s2' s2 \<or> (\<exists>s1'. s1 -\<tau>1\<rightarrow>+ s1' \<and> s1' \<approx> s2')"
  and wf_\<mu>1: "wfP \<mu>1"
  and wf_\<mu>2: "wfP \<mu>2"
begin

lemma delay_bisimulation_measure_flip:
  "delay_bisimulation_measure trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 \<mu>2 \<mu>1"
apply(rule delay_bisimulation_measure.intro)
 apply(rule delay_bisimulation_obs_flip)
apply(unfold_locales)
apply(unfold flip_simps)
apply(rule simulation_silent1 simulation_silent2 wf_\<mu>1 wf_\<mu>2|assumption)+
done

end

lemma delay_bisimulation_measure_flip_simps [flip_simps]:
  "delay_bisimulation_measure trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 \<mu>2 \<mu>1 =
   delay_bisimulation_measure trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 \<mu>1 \<mu>2"
by(auto dest: delay_bisimulation_measure.delay_bisimulation_measure_flip simp only: flip_simps)

context delay_bisimulation_measure begin

lemma simulation_silentst1:
  assumes bisim: "s1 \<approx> s2" and moves: "s1 -\<tau>1\<rightarrow>+ s1'"
  shows "s1' \<approx> s2 \<and> \<mu>1^++ s1' s1 \<or> (\<exists>s2'. s2 -\<tau>2\<rightarrow>+ s2' \<and> s1' \<approx> s2')"
using moves bisim
proof induct
  case (base s1') thus ?case by(auto dest: simulation_silent1)
next
  case (step s1' s1'')
  hence "s1' \<approx> s2 \<and> \<mu>1\<^sup>+\<^sup>+ s1' s1 \<or> (\<exists>s2'. s2 -\<tau>2\<rightarrow>+ s2' \<and> s1' \<approx> s2')" by blast
  thus ?case
  proof
    assume "s1' \<approx> s2 \<and> \<mu>1\<^sup>+\<^sup>+ s1' s1"
    hence "s1' \<approx> s2" "\<mu>1\<^sup>+\<^sup>+ s1' s1" by simp_all
    with simulation_silent1[OF \<open>s1' \<approx> s2\<close> \<open>s1' -\<tau>1\<rightarrow> s1''\<close>]
    show ?thesis by(auto)
  next
    assume "\<exists>s2'. trsys2.silent_move\<^sup>+\<^sup>+ s2 s2' \<and> s1' \<approx> s2'"
    then obtain s2' where "s2 -\<tau>2\<rightarrow>+ s2'" "s1' \<approx> s2'" by blast
    with simulation_silent1[OF \<open>s1' \<approx> s2'\<close> \<open>s1' -\<tau>1\<rightarrow> s1''\<close>]
    show ?thesis by(auto intro: tranclp_trans)
  qed
qed

lemma simulation_silentst2:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2\<rightarrow>+ s2' \<rbrakk> \<Longrightarrow> s1 \<approx> s2' \<and> \<mu>2^++ s2' s2 \<or> (\<exists>s1'. s1 -\<tau>1\<rightarrow>+ s1' \<and> s1' \<approx> s2')"
using delay_bisimulation_measure.simulation_silentst1[OF delay_bisimulation_measure_flip]
unfolding flip_simps .

lemma \<tau>diverge_simulation1:
  assumes diverge1: "s1 -\<tau>1\<rightarrow> \<infinity>"
  and bisim: "s1 \<approx> s2"
  shows "s2 -\<tau>2\<rightarrow> \<infinity>"
proof -
  from assms have "s1 -\<tau>1\<rightarrow> \<infinity> \<and> s1 \<approx> s2" by blast
  thus ?thesis using wfP_trancl[OF wf_\<mu>1]
  proof(coinduct rule: trsys2.\<tau>diverge_trancl_measure_coinduct)
    case (\<tau>diverge s2 s1)
    hence "s1 -\<tau>1\<rightarrow> \<infinity>" "s1 \<approx> s2" by simp_all
    then obtain s1' where "trsys1.silent_move s1 s1'" "s1' -\<tau>1\<rightarrow> \<infinity>"
      by(fastforce elim: trsys1.\<tau>diverge.cases)
    from simulation_silent1[OF \<open>s1 \<approx> s2\<close> \<open>trsys1.silent_move s1 s1'\<close>] \<open>s1' -\<tau>1\<rightarrow> \<infinity>\<close>
    show ?case by auto
  qed
qed

lemma \<tau>diverge_simulation2:
  "\<lbrakk> s2 -\<tau>2\<rightarrow> \<infinity>; s1 \<approx> s2 \<rbrakk> \<Longrightarrow> s1 -\<tau>1\<rightarrow> \<infinity>"
using delay_bisimulation_measure.\<tau>diverge_simulation1[OF delay_bisimulation_measure_flip]
unfolding flip_simps .

lemma \<tau>diverge_bisim_inv:
  "s1 \<approx> s2 \<Longrightarrow> s1 -\<tau>1\<rightarrow> \<infinity> \<longleftrightarrow> s2 -\<tau>2\<rightarrow> \<infinity>"
by(blast intro: \<tau>diverge_simulation1 \<tau>diverge_simulation2)

end

sublocale delay_bisimulation_measure < delay_bisimulation_diverge
proof
  fix s1 s2 s1'
  assume "s1 \<approx> s2" "s1 -\<tau>1\<rightarrow> s1'"
  from simulation_silent1[OF this]
  show "\<exists>s2'. s2 -\<tau>2\<rightarrow>* s2' \<and> s1' \<approx> s2'" by(auto intro: tranclp_into_rtranclp)
next
  fix s1 s2 s2'
  assume "s1 \<approx> s2" "s2 -\<tau>2\<rightarrow> s2'"
  from simulation_silent2[OF this]
  show "\<exists>s1'. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' \<approx> s2'" by(auto intro: tranclp_into_rtranclp)
next
  fix s1 s2
  assume "s1 \<approx> s2"
  thus "s1 -\<tau>1\<rightarrow> \<infinity> \<longleftrightarrow> s2 -\<tau>2\<rightarrow> \<infinity>" by(rule \<tau>diverge_bisim_inv)
qed

text \<open>
  Counter example for
  @{prop "delay_bisimulation_diverge trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 \<Longrightarrow> \<exists>\<mu>1 \<mu>2. delay_bisimulation_measure trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 \<mu>1 \<mu>2"}

 (only \<open>\<tau>\<close>moves):
\begin{verbatim}
--|
| v
--a  ~  x
  |     |
  |     |
  v     v
--b  ~  y--
| ^     ^ |
--|     |--
\end{verbatim}
\<close>

locale delay_bisimulation_measure_final =
  delay_bisimulation_measure + 
  delay_bisimulation_final_base +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
  and \<mu>1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<mu>2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool"
  and final1 :: "'s1 \<Rightarrow> bool"
  and final2 :: "'s2 \<Rightarrow> bool"

sublocale delay_bisimulation_measure_final < delay_bisimulation_diverge_final
by unfold_locales

locale \<tau>inv = delay_bisimulation_base +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
  and \<tau>moves1 :: "'s1 \<Rightarrow> 's1 \<Rightarrow> bool"
  and \<tau>moves2 :: "'s2 \<Rightarrow> 's2 \<Rightarrow> bool"
  assumes \<tau>inv: "\<lbrakk> s1 \<approx> s2; s1 -1-tl1\<rightarrow> s1'; s2 -2-tl2\<rightarrow> s2'; s1' \<approx> s2'; tl1 \<sim> tl2 \<rbrakk>
                 \<Longrightarrow> \<tau>move1 s1 tl1 s1' \<longleftrightarrow> \<tau>move2 s2 tl2 s2'"
begin

lemma \<tau>inv_flip:
  "\<tau>inv trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1"
by(unfold_locales)(unfold flip_simps,rule \<tau>inv[symmetric])

end

lemma \<tau>inv_flip_simps [flip_simps]:
  "\<tau>inv trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 = \<tau>inv trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
by(auto dest: \<tau>inv.\<tau>inv_flip simp only: flip_simps)

locale bisimulation_into_delay =
  bisimulation + \<tau>inv +
  constrains trsys1 :: "('s1, 'tl1) trsys"
  and trsys2 :: "('s2, 'tl2) trsys"
  and bisim :: "('s1, 's2) bisim"
  and tlsim :: "('tl1, 'tl2) bisim"
  and \<tau>move1 :: "('s1, 'tl1) trsys"
  and \<tau>move2 :: "('s2, 'tl2) trsys"
begin

lemma bisimulation_into_delay_flip:
  "bisimulation_into_delay trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1"
by(intro_locales)(intro bisimulation_flip \<tau>inv_flip)+

end

lemma bisimulation_into_delay_flip_simps [flip_simps]:
  "bisimulation_into_delay trsys2 trsys1 (flip bisim) (flip tlsim) \<tau>move2 \<tau>move1 =
   bisimulation_into_delay trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
by(auto dest: bisimulation_into_delay.bisimulation_into_delay_flip simp only: flip_simps)

context bisimulation_into_delay begin

lemma simulation_silent1_aux:
  assumes bisim: "s1 \<approx> s2" and "s1 -\<tau>1\<rightarrow> s1'"
  shows "s1' \<approx> s2 \<and> \<mu>1\<^sup>+\<^sup>+ s1' s1 \<or> (\<exists>s2'. s2 -\<tau>2\<rightarrow>+ s2' \<and> s1' \<approx> s2')"
proof -
  from assms obtain tl1 where tr1: "s1 -1-tl1\<rightarrow> s1'"
    and \<tau>1: "\<tau>move1 s1 tl1 s1'" by(auto)
  from simulation1[OF bisim tr1]
  obtain s2' tl2 where tr2: "s2 -2-tl2\<rightarrow> s2'"
    and bisim': "s1' \<approx> s2'" and tlsim: "tl1 \<sim> tl2" by blast
  from \<tau>inv[OF bisim tr1 tr2 bisim' tlsim] \<tau>1 have \<tau>2: "\<tau>move2 s2 tl2 s2'" by simp
  from tr2 \<tau>2 have "s2 -\<tau>2\<rightarrow>+ s2'" by(auto)
  with bisim' show ?thesis by blast
qed

lemma simulation_silent2_aux:
  "\<lbrakk> s1 \<approx> s2; s2 -\<tau>2\<rightarrow> s2' \<rbrakk> \<Longrightarrow> s1 \<approx> s2' \<and> \<mu>2\<^sup>+\<^sup>+ s2' s2 \<or> (\<exists>s1'. s1 -\<tau>1\<rightarrow>+ s1' \<and> s1' \<approx> s2')"
using bisimulation_into_delay.simulation_silent1_aux[OF bisimulation_into_delay_flip]
unfolding flip_simps .

lemma simulation1_aux:
  assumes bisim: "s1 \<approx> s2" and tr1: "s1 -1-tl1\<rightarrow> s1'" and \<tau>1: "\<not> \<tau>move1 s1 tl1 s1'"
  shows "\<exists>s2' s2'' tl2. s2 -\<tau>2\<rightarrow>* s2' \<and> s2' -2-tl2\<rightarrow> s2'' \<and> \<not> \<tau>move2 s2' tl2 s2'' \<and> s1' \<approx> s2'' \<and> tl1 \<sim> tl2"
proof -
  from simulation1[OF bisim tr1]
  obtain s2' tl2 where tr2: "s2 -2-tl2\<rightarrow> s2'"
    and bisim': "s1' \<approx> s2'" and tlsim: "tl1 \<sim> tl2" by blast
  from \<tau>inv[OF bisim tr1 tr2 bisim' tlsim] \<tau>1 have \<tau>2: "\<not> \<tau>move2 s2 tl2 s2'" by simp
  with bisim' tr2 tlsim show ?thesis by blast
qed

lemma simulation2_aux:
  "\<lbrakk> s1 \<approx> s2; s2 -2-tl2\<rightarrow> s2'; \<not> \<tau>move2 s2 tl2 s2' \<rbrakk>
  \<Longrightarrow> \<exists>s1' s1'' tl1. s1 -\<tau>1\<rightarrow>* s1' \<and> s1' -1-tl1\<rightarrow> s1'' \<and> \<not> \<tau>move1 s1' tl1 s1'' \<and> s1'' \<approx> s2' \<and> tl1 \<sim> tl2"
using bisimulation_into_delay.simulation1_aux[OF bisimulation_into_delay_flip]
unfolding flip_simps .

lemma delay_bisimulation_measure:
  assumes wf_\<mu>1: "wfP \<mu>1"
  and wf_\<mu>2: "wfP \<mu>2"
  shows "delay_bisimulation_measure trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 \<mu>1 \<mu>2"
apply(unfold_locales)
apply(rule simulation_silent1_aux simulation_silent2_aux simulation1_aux simulation2_aux wf_\<mu>1 wf_\<mu>2|assumption)+
done

lemma delay_bisimulation:
  "delay_bisimulation_diverge trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2"
proof -
  interpret delay_bisimulation_measure trsys1 trsys2 bisim tlsim \<tau>move1 \<tau>move2 "\<lambda>s s'. False" "\<lambda>s s'. False"
    by(blast intro: delay_bisimulation_measure wfP_empty)
  show ?thesis ..
qed

end

sublocale bisimulation_into_delay < delay_bisimulation_diverge
by(rule delay_bisimulation)

lemma delay_bisimulation_conv_bisimulation:
  "delay_bisimulation_diverge trsys1 trsys2 bisim tlsim (\<lambda>s tl s'. False) (\<lambda>s tl s'. False) =
   bisimulation trsys1 trsys2 bisim tlsim"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then interpret delay_bisimulation_diverge trsys1 trsys2 bisim tlsim "\<lambda>s tl s'. False" "\<lambda>s tl s'. False" .
  show ?rhs by(unfold_locales)(fastforce simp add: \<tau>moves_False dest: simulation1 simulation2)+
next
  assume ?rhs
  then interpret bisimulation trsys1 trsys2 bisim tlsim .
  interpret bisimulation_into_delay trsys1 trsys2 bisim tlsim "\<lambda>s tl s'. False" "\<lambda>s tl s'. False"
    by(unfold_locales)(rule refl)
  show ?lhs by unfold_locales
qed

context bisimulation_final begin

lemma delay_bisimulation_final_base: 
  "delay_bisimulation_final_base trsys1 trsys2 bisim \<tau>move1 \<tau>move2 final1 final2"
by(unfold_locales)(auto simp add: bisim_final)

end

sublocale bisimulation_final < delay_bisimulation_final_base
by(rule delay_bisimulation_final_base)

subsection \<open>Transitivity for bisimulations\<close>

definition bisim_compose :: "('s1, 's2) bisim \<Rightarrow> ('s2, 's3) bisim \<Rightarrow> ('s1, 's3) bisim" (infixr "\<circ>\<^sub>B" 60)
where "(bisim1 \<circ>\<^sub>B bisim2) s1 s3 \<equiv> \<exists>s2. bisim1 s1 s2 \<and> bisim2 s2 s3"

lemma bisim_composeI [intro]:
  "\<lbrakk> bisim12 s1 s2; bisim23 s2 s3 \<rbrakk> \<Longrightarrow> (bisim12 \<circ>\<^sub>B bisim23) s1 s3"
by(auto simp add: bisim_compose_def)

lemma bisim_composeE [elim!]:
  assumes bisim: "(bisim12 \<circ>\<^sub>B bisim23) s1 s3"
  obtains s2 where "bisim12 s1 s2" "bisim23 s2 s3"
by(atomize_elim)(rule bisim[unfolded bisim_compose_def])

lemma bisim_compose_assoc [simp]:
  "(bisim12 \<circ>\<^sub>B bisim23) \<circ>\<^sub>B bisim34 = bisim12 \<circ>\<^sub>B bisim23 \<circ>\<^sub>B bisim34"
by(auto simp add: fun_eq_iff)

lemma bisim_compose_conv_relcomp:
  "case_prod (bisim_compose bisim12 bisim23) = (\<lambda>x. x \<in> relcomp (Collect (case_prod bisim12)) (Collect (case_prod bisim23)))"
by(auto simp add: relcomp_unfold)

lemma list_all2_bisim_composeI:
  "\<lbrakk> list_all2 A xs ys; list_all2 B ys zs \<rbrakk>
  \<Longrightarrow> list_all2 (A \<circ>\<^sub>B B) xs zs"
by(rule list_all2_trans) auto+

lemma delay_bisimulation_diverge_compose:
  assumes wbisim12: "delay_bisimulation_diverge trsys1 trsys2 bisim12 tlsim12 \<tau>move1 \<tau>move2"
  and wbisim23: "delay_bisimulation_diverge trsys2 trsys3 bisim23 tlsim23 \<tau>move2 \<tau>move3"
  shows "delay_bisimulation_diverge trsys1 trsys3 (bisim12 \<circ>\<^sub>B bisim23) (tlsim12 \<circ>\<^sub>B tlsim23) \<tau>move1 \<tau>move3"
proof -
  interpret trsys1: \<tau>trsys trsys1 \<tau>move1 .
  interpret trsys2: \<tau>trsys trsys2 \<tau>move2 .
  interpret trsys3: \<tau>trsys trsys3 \<tau>move3 .
  interpret wb12: delay_bisimulation_diverge trsys1 trsys2 bisim12 tlsim12 \<tau>move1 \<tau>move2 by(auto intro: wbisim12)
  interpret wb23: delay_bisimulation_diverge trsys2 trsys3 bisim23 tlsim23 \<tau>move2 \<tau>move3 by(auto intro: wbisim23)
  show ?thesis
  proof
    fix s1 s3 s1'
    assume bisim: "(bisim12 \<circ>\<^sub>B bisim23) s1 s3" and tr1: "trsys1.silent_move s1 s1'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb12.simulation_silent1[OF bisim1 tr1] obtain s2'
      where tr2: "trsys2.silent_moves s2 s2'" and bisim1': "bisim12 s1' s2'" by blast
    from wb23.simulation_silents1[OF bisim2 tr2] obtain s3'
      where "trsys3.silent_moves s3 s3'" "bisim23 s2' s3'" by blast
    with bisim1' show "\<exists>s3'. trsys3.silent_moves s3 s3' \<and> (bisim12 \<circ>\<^sub>B bisim23) s1' s3'"
      by(blast intro: bisim_composeI)
  next
    fix s1 s3 s3'
    assume bisim: "(bisim12 \<circ>\<^sub>B bisim23) s1 s3" and tr3: "trsys3.silent_move s3 s3'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb23.simulation_silent2[OF bisim2 tr3] obtain s2'
      where tr2: "trsys2.silent_moves s2 s2'" and bisim2': "bisim23 s2' s3'" by blast
    from wb12.simulation_silents2[OF bisim1 tr2] obtain s1'
      where "trsys1.silent_moves s1 s1'" "bisim12 s1' s2'" by blast
    with bisim2' show "\<exists>s1'. trsys1.silent_moves s1 s1' \<and> (bisim12 \<circ>\<^sub>B bisim23) s1' s3'"
      by(blast intro: bisim_composeI)
  next
    fix s1 s3 tl1 s1'
    assume bisim: "(bisim12 \<circ>\<^sub>B bisim23) s1 s3"
      and tr1: "trsys1 s1 tl1 s1'" and \<tau>1: "\<not> \<tau>move1 s1 tl1 s1'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb12.simulation1[OF bisim1 tr1 \<tau>1] obtain s2' s2'' tl2
      where tr21: "trsys2.silent_moves s2 s2'" and tr22: "trsys2 s2' tl2 s2''" and \<tau>2: "\<not> \<tau>move2 s2' tl2 s2''"
      and bisim1': "bisim12 s1' s2''" and tlsim1: "tlsim12 tl1 tl2" by blast
    from wb23.simulation_silents1[OF bisim2 tr21] obtain s3'
      where tr31: "trsys3.silent_moves s3 s3'" and bisim2': "bisim23 s2' s3'" by blast
    from wb23.simulation1[OF bisim2' tr22 \<tau>2] obtain s3'' s3''' tl3
      where "trsys3.silent_moves s3' s3''" "trsys3 s3'' tl3 s3'''"
      "\<not> \<tau>move3 s3'' tl3 s3'''" "bisim23 s2'' s3'''" "tlsim23 tl2 tl3" by blast
    with tr31 bisim1' tlsim1 
    show "\<exists>s3' s3'' tl3. trsys3.silent_moves s3 s3' \<and> trsys3 s3' tl3 s3'' \<and> \<not> \<tau>move3 s3' tl3 s3'' \<and>
                         (bisim12 \<circ>\<^sub>B bisim23) s1' s3'' \<and> (tlsim12 \<circ>\<^sub>B tlsim23) tl1 tl3"
      by(blast intro: rtranclp_trans bisim_composeI)
  next
    fix s1 s3 tl3 s3'
    assume bisim: "(bisim12 \<circ>\<^sub>B bisim23) s1 s3"
      and tr3: "trsys3 s3 tl3 s3'" and \<tau>3: "\<not> \<tau>move3 s3 tl3 s3'"
    from bisim obtain s2 where bisim1: "bisim12 s1 s2" and bisim2: "bisim23 s2 s3" by blast
    from wb23.simulation2[OF bisim2 tr3 \<tau>3] obtain s2' s2'' tl2
      where tr21: "trsys2.silent_moves s2 s2'" and tr22: "trsys2 s2' tl2 s2''" and \<tau>2: "\<not> \<tau>move2 s2' tl2 s2''"
      and bisim2': "bisim23 s2'' s3'" and tlsim2: "tlsim23 tl2 tl3" by blast
    from wb12.simulation_silents2[OF bisim1 tr21] obtain s1'
      where tr11: "trsys1.silent_moves s1 s1'" and bisim1': "bisim12 s1' s2'" by blast
    from wb12.simulation2[OF bisim1' tr22 \<tau>2] obtain s1'' s1''' tl1
      where "trsys1.silent_moves s1' s1''" "trsys1 s1'' tl1 s1'''"
      "\<not> \<tau>move1 s1'' tl1 s1'''" "bisim12 s1''' s2''" "tlsim12 tl1 tl2" by blast
    with tr11 bisim2' tlsim2
    show "\<exists>s1' s1'' tl1. trsys1.silent_moves s1 s1' \<and> trsys1 s1' tl1 s1'' \<and> \<not> \<tau>move1 s1' tl1 s1'' \<and>
                         (bisim12 \<circ>\<^sub>B bisim23) s1'' s3' \<and> (tlsim12 \<circ>\<^sub>B tlsim23) tl1 tl3"
      by(blast intro: rtranclp_trans bisim_composeI)
  next
    fix s1 s2
    assume "(bisim12 \<circ>\<^sub>B bisim23) s1 s2"
    thus "\<tau>trsys.\<tau>diverge trsys1 \<tau>move1 s1 = \<tau>trsys.\<tau>diverge trsys3 \<tau>move3 s2"
      by(auto simp add: wb12.\<tau>diverge_bisim_inv wb23.\<tau>diverge_bisim_inv)
  qed
qed

lemma bisimulation_bisim_compose:
  "\<lbrakk> bisimulation trsys1 trsys2 bisim12 tlsim12; bisimulation trsys2 trsys3 bisim23 tlsim23 \<rbrakk>
  \<Longrightarrow> bisimulation trsys1 trsys3 (bisim_compose bisim12 bisim23) (bisim_compose tlsim12 tlsim23)"
unfolding delay_bisimulation_conv_bisimulation[symmetric]
by(rule delay_bisimulation_diverge_compose)

lemma delay_bisimulation_diverge_final_compose:
  fixes \<tau>move1 \<tau>move2
  assumes wbisim12: "delay_bisimulation_diverge_final trsys1 trsys2 bisim12 tlsim12 \<tau>move1 \<tau>move2 final1 final2"
  and wbisim23: "delay_bisimulation_diverge_final trsys2 trsys3 bisim23 tlsim23 \<tau>move2 \<tau>move3 final2 final3"
  shows "delay_bisimulation_diverge_final trsys1 trsys3 (bisim12 \<circ>\<^sub>B bisim23) (tlsim12 \<circ>\<^sub>B tlsim23) \<tau>move1 \<tau>move3 final1 final3"
proof -
  interpret trsys1: \<tau>trsys trsys1 \<tau>move1 .
  interpret trsys2: \<tau>trsys trsys2 \<tau>move2 .
  interpret trsys3: \<tau>trsys trsys3 \<tau>move3 .
  interpret wb12: delay_bisimulation_diverge_final trsys1 trsys2 bisim12 tlsim12 \<tau>move1 \<tau>move2 final1 final2
    by(auto intro: wbisim12)
  interpret wb23: delay_bisimulation_diverge_final trsys2 trsys3 bisim23 tlsim23 \<tau>move2 \<tau>move3 final2 final3
    by(auto intro: wbisim23)
  interpret delay_bisimulation_diverge trsys1 trsys3 "bisim12 \<circ>\<^sub>B bisim23" "tlsim12 \<circ>\<^sub>B tlsim23" \<tau>move1 \<tau>move3
    by(rule delay_bisimulation_diverge_compose)(unfold_locales)
  show ?thesis
  proof
    fix s1 s3
    assume "(bisim12 \<circ>\<^sub>B bisim23) s1 s3" "final1 s1"
    from \<open>(bisim12 \<circ>\<^sub>B bisim23) s1 s3\<close> obtain s2 where "bisim12 s1 s2" and "bisim23 s2 s3" ..
    from wb12.final1_simulation[OF \<open>bisim12 s1 s2\<close> \<open>final1 s1\<close>]
    obtain s2' where "trsys2.silent_moves s2 s2'" "bisim12 s1 s2'" "final2 s2'" by blast
    from wb23.simulation_silents1[OF \<open>bisim23 s2 s3\<close> \<open>trsys2.silent_moves s2 s2'\<close>]
    obtain s3' where "trsys3.silent_moves s3 s3'" "bisim23 s2' s3'" by blast
    from wb23.final1_simulation[OF \<open>bisim23 s2' s3'\<close> \<open>final2 s2'\<close>]
    obtain s3'' where "trsys3.silent_moves s3' s3''" "bisim23 s2' s3''" "final3 s3''" by blast
    from \<open>trsys3.silent_moves s3 s3'\<close> \<open>trsys3.silent_moves s3' s3''\<close>
    have "trsys3.silent_moves s3 s3''" by(rule rtranclp_trans)
    moreover from \<open>bisim12 s1 s2'\<close> \<open>bisim23 s2' s3''\<close>
    have "(bisim12 \<circ>\<^sub>B bisim23) s1 s3''" ..
    ultimately show "\<exists>s3'. trsys3.silent_moves s3 s3' \<and> (bisim12 \<circ>\<^sub>B bisim23) s1 s3' \<and> final3 s3'"
      using \<open>final3 s3''\<close> by iprover
  next
    fix s1 s3
    assume "(bisim12 \<circ>\<^sub>B bisim23) s1 s3" "final3 s3"
    from \<open>(bisim12 \<circ>\<^sub>B bisim23) s1 s3\<close> obtain s2 where "bisim12 s1 s2" and "bisim23 s2 s3" ..
    from wb23.final2_simulation[OF \<open>bisim23 s2 s3\<close> \<open>final3 s3\<close>]
    obtain s2' where "trsys2.silent_moves s2 s2'" "bisim23 s2' s3" "final2 s2'" by blast
    from wb12.simulation_silents2[OF \<open>bisim12 s1 s2\<close> \<open>trsys2.silent_moves s2 s2'\<close>]
    obtain s1' where "trsys1.silent_moves s1 s1'" "bisim12 s1' s2'" by blast
    from wb12.final2_simulation[OF \<open>bisim12 s1' s2'\<close> \<open>final2 s2'\<close>]
    obtain s1'' where "trsys1.silent_moves s1' s1''" "bisim12 s1'' s2'" "final1 s1''" by blast
    from \<open>trsys1.silent_moves s1 s1'\<close> \<open>trsys1.silent_moves s1' s1''\<close>
    have "trsys1.silent_moves s1 s1''" by(rule rtranclp_trans)
    moreover from \<open>bisim12 s1'' s2'\<close> \<open>bisim23 s2' s3\<close>
    have "(bisim12 \<circ>\<^sub>B bisim23) s1'' s3" ..
    ultimately show "\<exists>s1'. trsys1.silent_moves s1 s1' \<and> (bisim12 \<circ>\<^sub>B bisim23) s1' s3 \<and> final1 s1'"
      using \<open>final1 s1''\<close> by iprover
  qed
qed

end
