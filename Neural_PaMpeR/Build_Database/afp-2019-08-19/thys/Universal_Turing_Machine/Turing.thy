(* Title: thys/Turing.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
*)

chapter \<open>Turing Machines\<close>

theory Turing
  imports Main
begin

section \<open>Basic definitions of Turing machine\<close>

datatype action = W0 | W1 | L | R | Nop

datatype cell = Bk | Oc

type_synonym tape = "cell list \<times> cell list"

type_synonym state = nat

type_synonym instr = "action \<times> state"

type_synonym tprog = "instr list \<times> nat"

type_synonym tprog0 = "instr list"

type_synonym config = "state \<times> tape"

fun nth_of where
  "nth_of xs i = (if i \<ge> length xs then None else Some (xs ! i))"

lemma nth_of_map [simp]:
  shows "nth_of (map f p) n = (case (nth_of p n) of None \<Rightarrow> None | Some x \<Rightarrow> Some (f x))"
  by simp

fun 
  fetch :: "instr list \<Rightarrow> state \<Rightarrow> cell \<Rightarrow> instr"
  where
    "fetch p 0 b = (Nop, 0)"
  | "fetch p (Suc s) Bk = 
     (case nth_of p (2 * s) of
        Some i \<Rightarrow> i
      | None \<Rightarrow> (Nop, 0))"
  |"fetch p (Suc s) Oc = 
     (case nth_of p ((2 * s) + 1) of
         Some i \<Rightarrow> i
       | None \<Rightarrow> (Nop, 0))"

lemma fetch_Nil [simp]:
  shows "fetch [] s b = (Nop, 0)"
  by (cases s,force) (cases b;force)

fun 
  update :: "action \<Rightarrow> tape \<Rightarrow> tape"
  where 
    "update W0 (l, r) = (l, Bk # (tl r))" 
  | "update W1 (l, r) = (l, Oc # (tl r))"
  | "update L (l, r) = (if l = [] then ([], Bk # r) else (tl l, (hd l) # r))" 
  | "update R (l, r) = (if r = [] then (Bk # l, []) else ((hd r) # l, tl r))" 
  | "update Nop (l, r) = (l, r)"

abbreviation 
  "read r == if (r = []) then Bk else hd r"

fun step :: "config \<Rightarrow> tprog \<Rightarrow> config"
  where 
    "step (s, l, r) (p, off) = 
     (let (a, s') = fetch p (s - off) (read r) in (s', update a (l, r)))"

abbreviation
  "step0 c p \<equiv> step c (p, 0)"

fun steps :: "config \<Rightarrow> tprog \<Rightarrow> nat \<Rightarrow> config"
  where
    "steps c p 0 = c" |
    "steps c p (Suc n) = steps (step c p) p n"

abbreviation
  "steps0 c p n \<equiv> steps c (p, 0) n"

lemma step_red [simp]: 
  shows "steps c p (Suc n) = step (steps c p n) p"
  by (induct n arbitrary: c) (auto)

lemma steps_add [simp]: 
  shows "steps c p (m + n) = steps (steps c p m) p n"
  by (induct m arbitrary: c) (auto)

lemma step_0 [simp]: 
  shows "step (0, (l, r)) p = (0, (l, r))"
  by (cases p, simp)

lemma steps_0 [simp]: 
  shows "steps (0, (l, r)) p n = (0, (l, r))"
  by (induct n) (simp_all)

fun
  is_final :: "config \<Rightarrow> bool"
  where
    "is_final (s, l, r) = (s = 0)"

lemma is_final_eq: 
  shows "is_final (s, tp) = (s = 0)"
  by (cases tp) (auto)

lemma is_finalI [intro]:
  shows "is_final (0, tp)"
  by (simp add: is_final_eq)

lemma after_is_final:
  assumes "is_final c"
  shows "is_final (steps c p n)"
  using assms 
  by(induct n;cases c;auto)

lemma is_final:
  assumes a: "is_final (steps c p n1)"
    and b: "n1 \<le> n2"
  shows "is_final (steps c p n2)"
proof - 
  obtain n3 where eq: "n2 = n1 + n3" using b by (metis le_iff_add)
  from a show "is_final (steps c p n2)" unfolding eq
    by (simp add: after_is_final)
qed

lemma not_is_final:
  assumes a: "\<not> is_final (steps c p n1)"
    and b: "n2 \<le> n1"
  shows "\<not> is_final (steps c p n2)"
proof (rule notI)
  obtain n3 where eq: "n1 = n2 + n3" using b by (metis le_iff_add)
  assume "is_final (steps c p n2)"
  then have "is_final (steps c p n1)" unfolding eq
    by (simp add: after_is_final)
  with a show "False" by simp
qed

(* if the machine is in the halting state, there must have 
   been a state just before the halting state *)
lemma before_final: 
  assumes "steps0 (1, tp) A n = (0, tp')"
  shows "\<exists> n'. \<not> is_final (steps0 (1, tp) A n') \<and> steps0 (1, tp) A (Suc n') = (0, tp')"
  using assms
proof(induct n arbitrary: tp')
  case (0 tp')
  have asm: "steps0 (1, tp) A 0 = (0, tp')" by fact
  then show "\<exists>n'. \<not> is_final (steps0 (1, tp) A n') \<and> steps0 (1, tp) A (Suc n') = (0, tp')"
    by simp
next
  case (Suc n tp')
  have ih: "\<And>tp'. steps0 (1, tp) A n = (0, tp') \<Longrightarrow>
    \<exists>n'. \<not> is_final (steps0 (1, tp) A n') \<and> steps0 (1, tp) A (Suc n') = (0, tp')" by fact
  have asm: "steps0 (1, tp) A (Suc n) = (0, tp')" by fact
  obtain s l r where cases: "steps0 (1, tp) A n = (s, l, r)"
    by (auto intro: is_final.cases)
  then show "\<exists>n'. \<not> is_final (steps0 (1, tp) A n') \<and> steps0 (1, tp) A (Suc n') = (0, tp')"
  proof (cases "s = 0")
    case True (* in halting state *)
    then have "steps0 (1, tp) A n = (0, tp')"
      using asm cases by (simp del: steps.simps)
    then show ?thesis using ih by simp
  next
    case False (* not in halting state *)
    then have "\<not> is_final (steps0 (1, tp) A n) \<and> steps0 (1, tp) A (Suc n) = (0, tp')"
      using asm cases by simp
    then show ?thesis by auto
  qed
qed

lemma least_steps: 
  assumes "steps0 (1, tp) A n = (0, tp')"
  shows "\<exists> n'. (\<forall>n'' < n'. \<not> is_final (steps0 (1, tp) A n'')) \<and> 
               (\<forall>n'' \<ge> n'. is_final (steps0 (1, tp) A n''))"
proof -
  from before_final[OF assms] 
  obtain n' where
    before: "\<not> is_final (steps0 (1, tp) A n')" and
    final: "steps0 (1, tp) A (Suc n') = (0, tp')" by auto
  from before
  have "\<forall>n'' < Suc n'. \<not> is_final (steps0 (1, tp) A n'')"
    using not_is_final by auto
  moreover
  from final 
  have "\<forall>n'' \<ge> Suc n'. is_final (steps0 (1, tp) A n'')" 
    using is_final[of _ _ "Suc n'"] by (auto simp add: is_final_eq)
  ultimately
  show "\<exists> n'. (\<forall>n'' < n'. \<not> is_final (steps0 (1, tp) A n'')) \<and> (\<forall>n'' \<ge> n'. is_final (steps0 (1, tp) A n''))"
    by blast
qed



(* well-formedness of Turing machine programs *)
abbreviation "is_even n \<equiv> (n::nat) mod 2 = 0"

fun 
  tm_wf :: "tprog \<Rightarrow> bool"
  where
    "tm_wf (p, off) = (length p \<ge> 2 \<and> is_even (length p) \<and> 
                    (\<forall>(a, s) \<in> set p. s \<le> length p div 2 + off \<and> s \<ge> off))"

abbreviation
  "tm_wf0 p \<equiv> tm_wf (p, 0)"

abbreviation exponent :: "'a \<Rightarrow> nat \<Rightarrow> 'a list" ("_ \<up> _" [100, 99] 100)
  where "x \<up> n == replicate n x"

lemma hd_repeat_cases:
  "P (hd (a \<up> m @ r)) \<longleftrightarrow> (m = 0 \<longrightarrow> P (hd r)) \<and> (\<forall>nat. m = Suc nat \<longrightarrow> P a)"
  by (cases m,auto)

class tape =
  fixes tape_of :: "'a \<Rightarrow> cell list" ("<_>" 100)


instantiation nat::tape begin
definition tape_of_nat where "tape_of_nat (n::nat) \<equiv> Oc \<up> (Suc n)"
instance by standard
end

type_synonym nat_list = "nat list"

instantiation list::(tape) tape begin
fun tape_of_nat_list :: "('a::tape) list \<Rightarrow> cell list" 
  where 
    "tape_of_nat_list [] = []" |
    "tape_of_nat_list [n] = <n>" |
    "tape_of_nat_list (n#ns) = <n> @ Bk # (tape_of_nat_list ns)"
definition tape_of_list where "tape_of_list \<equiv> tape_of_nat_list"
instance by standard
end

instantiation prod:: (tape, tape) tape begin
fun tape_of_nat_prod :: "('a::tape) \<times> ('b::tape) \<Rightarrow> cell list" 
  where "tape_of_nat_prod (n, m) = <n> @ [Bk] @ <m>" 
definition tape_of_prod where "tape_of_prod \<equiv> tape_of_nat_prod"
instance by standard
end

fun 
  shift :: "instr list \<Rightarrow> nat \<Rightarrow> instr list"
  where
    "shift p n = (map (\<lambda> (a, s). (a, (if s = 0 then 0 else s + n))) p)"

fun 
  adjust :: "instr list \<Rightarrow> nat \<Rightarrow> instr list"
  where
    "adjust p e = map (\<lambda> (a, s). (a, if s = 0 then e else s)) p"

abbreviation
  "adjust0 p \<equiv> adjust p (Suc (length p div 2))"

lemma length_shift [simp]: 
  shows "length (shift p n) = length p"
  by simp

lemma length_adjust [simp]: 
  shows "length (adjust p n) = length p"
  by (induct p) (auto)


(* composition of two Turing machines *)
fun
  tm_comp :: "instr list \<Rightarrow> instr list \<Rightarrow> instr list" ("_ |+| _" [0, 0] 100)
  where
    "tm_comp p1 p2 = ((adjust0 p1) @ (shift p2 (length p1 div 2)))"

lemma tm_comp_length:
  shows "length (A |+| B) = length A + length B"
  by auto

lemma tm_comp_wf[intro]: 
  "\<lbrakk>tm_wf (A, 0); tm_wf (B, 0)\<rbrakk> \<Longrightarrow> tm_wf (A |+| B, 0)"
  by (fastforce)

lemma tm_comp_step: 
  assumes unfinal: "\<not> is_final (step0 c A)"
  shows "step0 c (A |+| B) = step0 c A"
proof -
  obtain s l r where eq: "c = (s, l, r)" by (metis is_final.cases) 
  have "\<not> is_final (step0 (s, l, r) A)" using unfinal eq by simp
  then have "case (fetch A s (read r)) of (a, s) \<Rightarrow> s \<noteq> 0"
    by (auto simp add: is_final_eq)
  then have "fetch (A |+| B) s (read r) = fetch A s (read r)"
    apply (cases "read r";cases s)
    by (auto simp: tm_comp_length nth_append)
  then show "step0 c (A |+| B) = step0 c A" by (simp add: eq) 
qed

lemma tm_comp_steps:  
  assumes "\<not> is_final (steps0 c A n)" 
  shows "steps0 c (A |+| B) n = steps0 c A n"
  using assms
proof(induct n)
  case 0
  then show "steps0 c (A |+| B) 0 = steps0 c A 0" by auto
next 
  case (Suc n)
  have ih: "\<not> is_final (steps0 c A n) \<Longrightarrow> steps0 c (A |+| B) n = steps0 c A n" by fact
  have fin: "\<not> is_final (steps0 c A (Suc n))" by fact
  then have fin1: "\<not> is_final (step0 (steps0 c A n) A)" 
    by (auto simp only: step_red)
  then have fin2: "\<not> is_final (steps0 c A n)"
    by (metis is_final_eq step_0 surj_pair) 

  have "steps0 c (A |+| B) (Suc n) = step0 (steps0 c (A |+| B) n) (A |+| B)" 
    by (simp only: step_red)
  also have "... = step0 (steps0 c A n) (A |+| B)" by (simp only: ih[OF fin2])
  also have "... = step0 (steps0 c A n) A" by (simp only: tm_comp_step[OF fin1])
  finally show "steps0 c (A |+| B) (Suc n) = steps0 c A (Suc n)"
    by (simp only: step_red)
qed

lemma tm_comp_fetch_in_A:
  assumes h1: "fetch A s x = (a, 0)"
    and h2: "s \<le> length A div 2" 
    and h3: "s \<noteq> 0"
  shows "fetch (A |+| B) s x = (a, Suc (length A div 2))"
  using h1 h2 h3
  apply(cases s;cases x)
  by(auto simp: tm_comp_length nth_append)

lemma tm_comp_exec_after_first:
  assumes h1: "\<not> is_final c" 
    and h2: "step0 c A = (0, tp)"
    and h3: "fst c \<le> length A div 2"
  shows "step0 c (A |+| B) = (Suc (length A div 2), tp)"
  using h1 h2 h3
  apply(case_tac c)
  apply(auto simp del: tm_comp.simps)
   apply(case_tac "fetch A a Bk")
   apply(simp del: tm_comp.simps)
   apply(subst tm_comp_fetch_in_A;force)
  apply(case_tac "fetch A a (hd ca)")
  apply(simp del: tm_comp.simps)
  apply(subst tm_comp_fetch_in_A)
     apply(auto)[4]
  done

lemma step_in_range: 
  assumes h1: "\<not> is_final (step0 c A)"
    and h2: "tm_wf (A, 0)"
  shows "fst (step0 c A) \<le> length A div 2"
  using h1 h2
  apply(cases c;cases "fst c";cases "hd (snd (snd c))")
  by(auto simp add: Let_def case_prod_beta')

lemma steps_in_range: 
  assumes h1: "\<not> is_final (steps0 (1, tp) A stp)"
    and h2: "tm_wf (A, 0)"
  shows "fst (steps0 (1, tp) A stp) \<le> length A div 2"
  using h1
proof(induct stp)
  case 0
  then show "fst (steps0 (1, tp) A 0) \<le> length A div 2" using h2
    by (auto)
next
  case (Suc stp)
  have ih: "\<not> is_final (steps0 (1, tp) A stp) \<Longrightarrow> fst (steps0 (1, tp) A stp) \<le> length A div 2" by fact
  have h: "\<not> is_final (steps0 (1, tp) A (Suc stp))" by fact
  from ih h h2 show "fst (steps0 (1, tp) A (Suc stp)) \<le> length A div 2"
    by (metis step_in_range step_red)
qed

(* if A goes into the final state, then A |+| B will go into the first state of B *)
lemma tm_comp_next: 
  assumes a_ht: "steps0 (1, tp) A n = (0, tp')"
    and a_wf: "tm_wf (A, 0)"
  obtains n' where "steps0 (1, tp) (A |+| B) n' = (Suc (length A div 2), tp')"
proof -
  assume a: "\<And>n. steps (1, tp) (A |+| B, 0) n = (Suc (length A div 2), tp') \<Longrightarrow> thesis"
  obtain stp' where fin: "\<not> is_final (steps0 (1, tp) A stp')" and h: "steps0 (1, tp) A (Suc stp') = (0, tp')"
    using before_final[OF a_ht] by blast
  from fin have h1:"steps0 (1, tp) (A |+| B) stp' = steps0 (1, tp) A stp'"
    by (rule tm_comp_steps)
  from h have h2: "step0 (steps0 (1, tp) A stp') A = (0, tp')"
    by (simp only: step_red)

  have "steps0 (1, tp) (A |+| B) (Suc stp') = step0 (steps0 (1, tp) (A |+| B) stp') (A |+| B)" 
    by (simp only: step_red)
  also have "... = step0 (steps0 (1, tp) A stp') (A |+| B)" using h1 by simp
  also have "... = (Suc (length A div 2), tp')" 
    by (rule tm_comp_exec_after_first[OF fin h2 steps_in_range[OF fin a_wf]])
  finally show thesis using a by blast
qed

lemma tm_comp_fetch_second_zero:
  assumes h1: "fetch B s x = (a, 0)"
    and hs: "tm_wf (A, 0)" "s \<noteq> 0"
  shows "fetch (A |+| B) (s + (length A div 2)) x = (a, 0)"
  using h1 hs
  by(cases x; cases s; fastforce simp: tm_comp_length nth_append)

lemma tm_comp_fetch_second_inst:
  assumes h1: "fetch B sa x = (a, s)"
    and hs: "tm_wf (A, 0)" "sa \<noteq> 0" "s \<noteq> 0"
  shows "fetch (A |+| B) (sa + length A div 2) x = (a, s + length A div 2)"
  using h1 hs
  by(cases x; cases sa; fastforce simp: tm_comp_length nth_append)


lemma tm_comp_second:
  assumes a_wf: "tm_wf (A, 0)"
    and steps: "steps0 (1, l, r) B stp = (s', l', r')"
  shows "steps0 (Suc (length A div 2), l, r)  (A |+| B) stp 
    = (if s' = 0 then 0 else s' + length A div 2, l', r')"
  using steps
proof(induct stp arbitrary: s' l' r')
  case 0
  then show ?case by simp
next
  case (Suc stp s' l' r')
  obtain s'' l'' r'' where a: "steps0 (1, l, r) B stp = (s'', l'', r'')"
    by (metis is_final.cases)
  then have ih1: "s'' = 0 \<Longrightarrow> steps0 (Suc (length A div 2), l, r) (A |+| B) stp = (0, l'', r'')"
    and ih2: "s'' \<noteq> 0 \<Longrightarrow> steps0 (Suc (length A div 2), l, r) (A |+| B) stp = (s'' + length A div 2, l'', r'')"
    using Suc by (auto)
  have h: "steps0 (1, l, r) B (Suc stp) = (s', l', r')" by fact

  { assume "s'' = 0"
    then have ?case using a h ih1 by (simp del: steps.simps) 
  } moreover
  { assume as: "s'' \<noteq> 0" "s' = 0"
    from as a h 
    have "step0 (s'', l'', r'') B = (0, l', r')" by (simp del: steps.simps)
    with as have ?case
      apply(cases "fetch B s'' (read r'')")
      by (auto simp add: tm_comp_fetch_second_zero[OF _ a_wf] ih2[OF as(1)]
          simp del: tm_comp.simps steps.simps)
  } moreover
  { assume as: "s'' \<noteq> 0" "s' \<noteq> 0"
    from as a h
    have "step0 (s'', l'', r'') B = (s', l', r')" by (simp del: steps.simps)
    with as have ?case
      apply(simp add: ih2[OF as(1)] del: tm_comp.simps steps.simps)
      apply(case_tac "fetch B s'' (read r'')")
      apply(auto simp add: tm_comp_fetch_second_inst[OF _ a_wf as] simp del: tm_comp.simps)
      done
  }
  ultimately show ?case by blast
qed


lemma tm_comp_final:
  assumes "tm_wf (A, 0)"  
    and "steps0 (1, l, r) B stp = (0, l', r')"
  shows "steps0 (Suc (length A div 2), l, r)  (A |+| B) stp = (0, l', r')"
  using tm_comp_second[OF assms] by (simp)

end

