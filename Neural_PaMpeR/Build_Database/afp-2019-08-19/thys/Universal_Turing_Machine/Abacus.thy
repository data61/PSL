(* Title: thys/Abacus.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
*)

chapter \<open>Abacus Machines\<close>

theory Abacus
  imports Turing_Hoare Abacus_Mopup
begin

declare replicate_Suc[simp add]

(* Abacus instructions *)

datatype abc_inst =
  Inc nat
  | Dec nat nat
  | Goto nat

type_synonym abc_prog = "abc_inst list"

type_synonym abc_state = nat

text \<open>
  The memory of Abacus machine is defined as a list of contents, with 
  every units addressed by index into the list.
\<close>
type_synonym abc_lm = "nat list"

text \<open>
  Fetching contents out of memory. Units not represented by list elements are considered
  as having content \<open>0\<close>.
\<close>
fun abc_lm_v :: "abc_lm \<Rightarrow> nat \<Rightarrow> nat"
  where 
    "abc_lm_v lm n = (if (n < length lm) then (lm!n) else 0)"         


text \<open>
  Set the content of memory unit \<open>n\<close> to value \<open>v\<close>.
  \<open>am\<close> is the Abacus memory before setting.
  If address \<open>n\<close> is outside to scope of \<open>am\<close>, \<open>am\<close> 
  is extended so that \<open>n\<close> becomes in scope.
\<close>

fun abc_lm_s :: "abc_lm \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> abc_lm"
  where
    "abc_lm_s am n v = (if (n < length am) then (am[n:=v]) else 
                           am@ (replicate (n - length am) 0) @ [v])"


text \<open>
  The configuration of Abaucs machines consists of its current state and its
  current memory:
\<close>
type_synonym abc_conf = "abc_state \<times> abc_lm"

text \<open>
  Fetch instruction out of Abacus program:
\<close>

fun abc_fetch :: "nat \<Rightarrow> abc_prog \<Rightarrow> abc_inst option" 
  where
    "abc_fetch s p = (if (s < length p) then Some (p ! s) else None)"

text \<open>
  Single step execution of Abacus machine. If no instruction is feteched, 
  configuration does not change.
\<close>
fun abc_step_l :: "abc_conf \<Rightarrow> abc_inst option \<Rightarrow> abc_conf"
  where
    "abc_step_l (s, lm) a = (case a of 
               None \<Rightarrow> (s, lm) |
               Some (Inc n)  \<Rightarrow> (let nv = abc_lm_v lm n in
                       (s + 1, abc_lm_s lm n (nv + 1))) |
               Some (Dec n e) \<Rightarrow> (let nv = abc_lm_v lm n in
                       if (nv = 0) then (e, abc_lm_s lm n 0) 
                       else (s + 1,  abc_lm_s lm n (nv - 1))) |
               Some (Goto n) \<Rightarrow> (n, lm) 
               )"

text \<open>
  Multi-step execution of Abacus machine.
\<close>
fun abc_steps_l :: "abc_conf \<Rightarrow> abc_prog \<Rightarrow> nat \<Rightarrow> abc_conf"
  where
    "abc_steps_l (s, lm) p 0 = (s, lm)" |
    "abc_steps_l (s, lm) p (Suc n) = 
      abc_steps_l (abc_step_l (s, lm) (abc_fetch s p)) p n"

section \<open>
  Compiling Abacus machines into Turing machines
\<close>

subsection \<open>
  Compiling functions
\<close>

text \<open>
  \<open>findnth n\<close> returns the TM which locates the represention of
  memory cell \<open>n\<close> on the tape and changes representation of zero
  on the way.
\<close>

fun findnth :: "nat \<Rightarrow> instr list"
  where
    "findnth 0 = []" |
    "findnth (Suc n) = (findnth n @ [(W1, 2 * n + 1), 
           (R, 2 * n + 2), (R, 2 * n + 3), (R, 2 * n + 2)])"

text \<open>
  \<open>tinc_b\<close> returns the TM which increments the representation 
  of the memory cell under rw-head by one and move the representation 
  of cells afterwards to the right accordingly.
\<close>

definition tinc_b :: "instr list"
  where
    "tinc_b \<equiv> [(W1, 1), (R, 2), (W1, 3), (R, 2), (W1, 3), (R, 4), 
             (L, 7), (W0, 5), (R, 6), (W0, 5), (W1, 3), (R, 6),
             (L, 8), (L, 7), (R, 9), (L, 7), (R, 10), (W0, 9)]" 

text \<open>
  \<open>tinc ss n\<close> returns the TM which simulates the execution of 
  Abacus instruction \<open>Inc n\<close>, assuming that TM is located at
  location \<open>ss\<close> in the final TM complied from the whole
  Abacus program.
\<close>

fun tinc :: "nat \<Rightarrow> nat \<Rightarrow> instr list"
  where
    "tinc ss n = shift (findnth n @ shift tinc_b (2 * n)) (ss - 1)"

text \<open>
  \<open>tinc_b\<close> returns the TM which decrements the representation 
  of the memory cell under rw-head by one and move the representation 
  of cells afterwards to the left accordingly.
\<close>

definition tdec_b :: "instr list"
  where
    "tdec_b \<equiv>  [(W1, 1), (R, 2), (L, 14), (R, 3), (L, 4), (R, 3),
              (R, 5), (W0, 4), (R, 6), (W0, 5), (L, 7), (L, 8),
              (L, 11), (W0, 7), (W1, 8), (R, 9), (L, 10), (R, 9),
              (R, 5), (W0, 10), (L, 12), (L, 11), (R, 13), (L, 11),
              (R, 17), (W0, 13), (L, 15), (L, 14), (R, 16), (L, 14),
              (R, 0), (W0, 16)]"


text \<open>
  \<open>tdec ss n label\<close> returns the TM which simulates the execution of 
  Abacus instruction \<open>Dec n label\<close>, assuming that TM is located at
  location \<open>ss\<close> in the final TM complied from the whole
  Abacus program.
\<close>

fun tdec :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> instr list"
  where
    "tdec ss n e = shift (findnth n) (ss - 1) @ adjust (shift (shift tdec_b (2 * n)) (ss - 1)) e"

text \<open>
  \<open>tgoto f(label)\<close> returns the TM simulating the execution of Abacus instruction
  \<open>Goto label\<close>, where \<open>f(label)\<close> is the corresponding location of
  \<open>label\<close> in the final TM compiled from the overall Abacus program.
\<close>

fun tgoto :: "nat \<Rightarrow> instr list"
  where
    "tgoto n = [(Nop, n), (Nop, n)]"

text \<open>
  The layout of the final TM compiled from an Abacus program is represented
  as a list of natural numbers, where the list element at index \<open>n\<close> represents the 
  starting state of the TM simulating the execution of \<open>n\<close>-th instruction
  in the Abacus program.
\<close>

type_synonym layout = "nat list"

text \<open>
  \<open>length_of i\<close> is the length of the 
  TM simulating the Abacus instruction \<open>i\<close>.
\<close>
fun length_of :: "abc_inst \<Rightarrow> nat"
  where
    "length_of i = (case i of 
                    Inc n   \<Rightarrow> 2 * n + 9 |
                    Dec n e \<Rightarrow> 2 * n + 16 |
                    Goto n  \<Rightarrow> 1)"

text \<open>
  \<open>layout_of ap\<close> returns the layout of Abacus program \<open>ap\<close>.
\<close>
fun layout_of :: "abc_prog \<Rightarrow> layout"
  where "layout_of ap = map length_of ap"


text \<open>
  \<open>start_of layout n\<close> looks out the starting state of \<open>n\<close>-th
  TM in the finall TM.
\<close>

fun start_of :: "nat list \<Rightarrow> nat \<Rightarrow> nat"
  where
    "start_of ly x = (Suc (sum_list (take x ly))) "

text \<open>
  \<open>ci lo ss i\<close> complies Abacus instruction \<open>i\<close>
  assuming the TM of \<open>i\<close> starts from state \<open>ss\<close> 
  within the overal layout \<open>lo\<close>.
\<close>

fun ci :: "layout \<Rightarrow> nat \<Rightarrow> abc_inst \<Rightarrow> instr list"
  where
    "ci ly ss (Inc n) = tinc ss n"
  | "ci ly ss (Dec n e) = tdec ss n (start_of ly e)"
  | "ci ly ss (Goto n) = tgoto (start_of ly n)"

text \<open>
  \<open>tpairs_of ap\<close> transfroms Abacus program \<open>ap\<close> pairing
  every instruction with its starting state.
\<close>

fun tpairs_of :: "abc_prog \<Rightarrow> (nat \<times> abc_inst) list"
  where "tpairs_of ap = (zip (map (start_of (layout_of ap)) 
                         [0..<(length ap)]) ap)"

text \<open>
  \<open>tms_of ap\<close> returns the list of TMs, where every one of them simulates
  the corresponding Abacus intruction in \<open>ap\<close>.
\<close>

fun tms_of :: "abc_prog \<Rightarrow> (instr list) list"
  where "tms_of ap = map (\<lambda> (n, tm). ci (layout_of ap) n tm) 
                         (tpairs_of ap)"

text \<open>
  \<open>tm_of ap\<close> returns the final TM machine compiled from Abacus program \<open>ap\<close>.
\<close>
fun tm_of :: "abc_prog \<Rightarrow> instr list"
  where "tm_of ap = concat (tms_of ap)"

lemma length_findnth: 
  "length (findnth n) = 4 * n"
  by (induct n, auto)

lemma ci_length : "length (ci ns n ai) div 2 = length_of ai"
  apply(auto simp: ci.simps tinc_b_def tdec_b_def length_findnth
      split: abc_inst.splits simp del: adjust.simps)
  done

subsection \<open>Representation of Abacus memory by TM tapes\<close>

text \<open>
  \<open>crsp acf tcf\<close> meams the abacus configuration \<open>acf\<close>
  is corretly represented by the TM configuration \<open>tcf\<close>.
\<close>

fun crsp :: "layout \<Rightarrow> abc_conf \<Rightarrow> config \<Rightarrow> cell list \<Rightarrow> bool"
  where 
    "crsp ly (as, lm) (s, l, r) inres = 
           (s = start_of ly as \<and> (\<exists> x. r = <lm> @ Bk\<up>x) \<and> 
            l = Bk # Bk # inres)"

declare crsp.simps[simp del]

text \<open>
  The type of invarints expressing correspondence between 
  Abacus configuration and TM configuration.
\<close>

type_synonym inc_inv_t = "abc_conf \<Rightarrow> config \<Rightarrow> cell list \<Rightarrow> bool"

declare tms_of.simps[simp del] tm_of.simps[simp del]
  layout_of.simps[simp del] abc_fetch.simps [simp del]  
  tpairs_of.simps[simp del] start_of.simps[simp del]
  ci.simps [simp del] length_of.simps[simp del] 
  layout_of.simps[simp del]

text \<open>
  The lemmas in this section lead to the correctness of 
  the compilation of \<open>Inc n\<close> instruction.
\<close>

declare abc_step_l.simps[simp del] abc_steps_l.simps[simp del]
lemma start_of_nonzero[simp]: "start_of ly as > 0" "(start_of ly as = 0) = False"
   apply(auto simp: start_of.simps)
  done

lemma abc_steps_l_0: "abc_steps_l ac ap 0 = ac"
  by(cases ac, simp add: abc_steps_l.simps)

lemma abc_step_red: 
  "abc_steps_l (as, am) ap stp = (bs, bm) \<Longrightarrow> 
  abc_steps_l (as, am) ap (Suc stp) = abc_step_l (bs, bm) (abc_fetch bs ap) "
proof(induct stp arbitrary: as am bs bm)
  case 0
  thus "?case"
    by(simp add: abc_steps_l.simps abc_steps_l_0)
next
  case (Suc stp as am bs bm)
  have ind: "\<And>as am bs bm. abc_steps_l (as, am) ap stp = (bs, bm) \<Longrightarrow> 
    abc_steps_l (as, am) ap (Suc stp) = abc_step_l (bs, bm) (abc_fetch bs ap)"
    by fact
  have h:" abc_steps_l (as, am) ap (Suc stp) = (bs, bm)" by fact
  obtain as' am' where g: "abc_step_l (as, am) (abc_fetch as ap) = (as', am')"
    by(cases "abc_step_l (as, am) (abc_fetch as ap)", auto)
  then have "abc_steps_l (as', am') ap (Suc stp) = abc_step_l (bs, bm) (abc_fetch bs ap)"
    using h
    by(intro ind, simp add: abc_steps_l.simps)
  thus "?case"
    using g
    by(simp add: abc_steps_l.simps)
qed

lemma tm_shift_fetch: 
  "\<lbrakk>fetch A s b = (ac, ns); ns \<noteq> 0 \<rbrakk>
  \<Longrightarrow> fetch (shift A off) s b = (ac, ns + off)"
  apply(cases b;cases s)
     apply(auto simp: fetch.simps shift.simps)
  done

lemma tm_shift_eq_step:
  assumes exec: "step (s, l, r) (A, 0) = (s', l', r')"
    and notfinal: "s' \<noteq> 0"
  shows "step (s + off, l, r) (shift A off, off) = (s' + off, l', r')"
  using assms
  apply(simp add: step.simps)
  apply(cases "fetch A s (read r)", auto)
   apply(drule_tac [!] off = off in tm_shift_fetch, simp_all)
  done

declare step.simps[simp del] steps.simps[simp del] shift.simps[simp del]

lemma tm_shift_eq_steps: 
  assumes exec: "steps (s, l, r) (A, 0) stp = (s', l', r')"
    and notfinal: "s' \<noteq> 0"
  shows "steps (s + off, l, r) (shift A off, off) stp = (s' + off, l', r')"
  using exec notfinal
proof(induct stp arbitrary: s' l' r', simp add: steps.simps)
  fix stp s' l' r'
  assume ind: "\<And>s' l' r'. \<lbrakk>steps (s, l, r) (A, 0) stp = (s', l', r'); s' \<noteq> 0\<rbrakk> 
     \<Longrightarrow> steps (s + off, l, r) (shift A off, off) stp = (s' + off, l', r')"
    and h: " steps (s, l, r) (A, 0) (Suc stp) = (s', l', r')" "s' \<noteq> 0"
  obtain s1 l1 r1 where g: "steps (s, l, r) (A, 0) stp = (s1, l1, r1)" 
    apply(cases "steps (s, l, r) (A, 0) stp") by blast
  moreover then have "s1 \<noteq> 0"
    using h
    apply(simp add: step_red)
    apply(cases "0 < s1", auto)
    done
  ultimately have "steps (s + off, l, r) (shift A off, off) stp =
                   (s1 + off, l1, r1)"
    apply(intro ind, simp_all)
    done
  thus "steps (s + off, l, r) (shift A off, off) (Suc stp) = (s' + off, l', r')"
    using h g assms
    apply(simp add: step_red)
    apply(intro tm_shift_eq_step, auto)
    done
qed

lemma startof_ge1[simp]: "Suc 0 \<le> start_of ly as"
  apply(simp add: start_of.simps)
  done

lemma start_of_Suc1: "\<lbrakk>ly = layout_of ap; 
       abc_fetch as ap = Some (Inc n)\<rbrakk>
       \<Longrightarrow> start_of ly (Suc as) = start_of ly as + 2 * n + 9"
  apply(auto simp: start_of.simps layout_of.simps  
      length_of.simps abc_fetch.simps 
      take_Suc_conv_app_nth split: if_splits)
  done

lemma start_of_Suc2:
  "\<lbrakk>ly = layout_of ap;
  abc_fetch as ap = Some (Dec n e)\<rbrakk> \<Longrightarrow> 
        start_of ly (Suc as) = 
            start_of ly as + 2 * n + 16"
  apply(auto simp: start_of.simps layout_of.simps  
      length_of.simps abc_fetch.simps 
      take_Suc_conv_app_nth split: if_splits)
  done

lemma start_of_Suc3:
  "\<lbrakk>ly = layout_of ap;
  abc_fetch as ap = Some (Goto n)\<rbrakk> \<Longrightarrow> 
  start_of ly (Suc as) = start_of ly as + 1"
  apply(auto simp: start_of.simps layout_of.simps  
      length_of.simps abc_fetch.simps 
      take_Suc_conv_app_nth split: if_splits)
  done

lemma length_ci_inc: 
  "length (ci ly ss (Inc n)) = 4*n + 18"
  apply(auto simp: ci.simps length_findnth tinc_b_def)
  done

lemma length_ci_dec: 
  "length (ci ly ss (Dec n e)) = 4*n + 32"
  apply(auto simp: ci.simps length_findnth tdec_b_def)
  done

lemma length_ci_goto: 
  "length (ci ly ss (Goto n )) = 2"
  apply(auto simp: ci.simps length_findnth tdec_b_def)
  done

lemma take_Suc_last[elim]: "Suc as \<le> length xs \<Longrightarrow> 
            take (Suc as) xs = take as xs @ [xs ! as]"
proof(induct xs arbitrary: as)
  case (Cons a xs)
  then show ?case by ( simp, cases as;simp)
qed simp

lemma concat_suc: "Suc as \<le> length xs \<Longrightarrow> 
       concat (take (Suc as) xs) = concat (take as xs) @ xs! as"
  apply(subgoal_tac "take (Suc as) xs = take as xs @ [xs ! as]", simp)
  by auto

lemma concat_drop_suc_iff: 
  "Suc n < length tps \<Longrightarrow> concat (drop (Suc n) tps) = 
           tps ! Suc n @ concat (drop (Suc (Suc n)) tps)"
proof(induct tps arbitrary: n)
  case (Cons a tps)
  then show ?case 
    apply(cases tps, simp, simp)
    apply(cases n, simp, simp)
    done
qed simp

declare append_assoc[simp del]

lemma  tm_append:
  "\<lbrakk>n < length tps; tp = tps ! n\<rbrakk> \<Longrightarrow> 
  \<exists> tp1 tp2. concat tps = tp1 @ tp @ tp2 \<and> tp1 = 
  concat (take n tps) \<and> tp2 = concat (drop (Suc n) tps)"
  apply(rule_tac x = "concat (take n tps)" in exI)
  apply(rule_tac x = "concat (drop (Suc n) tps)" in exI)
  apply(auto)
proof(induct n)
  case 0
  then show ?case by(cases tps; simp)
next
  case (Suc n)
  then show ?case 
    apply(subgoal_tac "concat (take n tps) @ (tps ! n) = 
               concat (take (Suc n) tps)")
     apply(simp only: append_assoc[THEN sym], simp only: append_assoc)
     apply(subgoal_tac " concat (drop (Suc n) tps) = tps ! Suc n @ 
                  concat (drop (Suc (Suc n)) tps)")
      apply (metis append_take_drop_id concat_append)
     apply(rule concat_drop_suc_iff,force)
    by (simp add: concat_suc)
qed

declare append_assoc[simp]

lemma length_tms_of[simp]: "length (tms_of aprog) = length aprog"
  apply(auto simp: tms_of.simps tpairs_of.simps)
  done

lemma ci_nth: 
  "\<lbrakk>ly = layout_of aprog; 
  abc_fetch as aprog = Some ins\<rbrakk>
  \<Longrightarrow> ci ly (start_of ly as) ins = tms_of aprog ! as"
  apply(simp add: tms_of.simps tpairs_of.simps 
      abc_fetch.simps del: map_append split: if_splits)
  done

lemma t_split:"\<lbrakk>
        ly = layout_of aprog;
        abc_fetch as aprog = Some ins\<rbrakk>
      \<Longrightarrow> \<exists> tp1 tp2. concat (tms_of aprog) = 
            tp1 @ (ci ly (start_of ly as) ins) @ tp2
            \<and> tp1 = concat (take as (tms_of aprog)) \<and> 
              tp2 = concat (drop (Suc as) (tms_of aprog))"
  apply(insert tm_append[of "as" "tms_of aprog" 
        "ci ly (start_of ly as) ins"], simp)
  apply(subgoal_tac "ci ly (start_of ly as) ins = (tms_of aprog) ! as")
   apply(subgoal_tac "length (tms_of aprog) = length aprog")
    apply(simp add: abc_fetch.simps split: if_splits, simp)
  apply(intro ci_nth, auto)
  done

lemma div_apart: "\<lbrakk>x mod (2::nat) = 0; y mod 2 = 0\<rbrakk> 
          \<Longrightarrow> (x + y) div 2 = x div 2 + y div 2"
  by(auto)

lemma length_layout_of[simp]: "length (layout_of aprog) = length aprog"
  by(auto simp: layout_of.simps)

lemma length_tms_of_elem_even[intro]:  "n < length ap \<Longrightarrow> length (tms_of ap ! n) mod 2 = 0"
  apply(cases "ap ! n")
  by (auto simp: tms_of.simps tpairs_of.simps ci.simps length_findnth tinc_b_def tdec_b_def)

lemma compile_mod2: "length (concat (take n (tms_of ap))) mod 2 = 0"
proof(induct n)
  case 0
  then show ?case by (auto simp add: take_Suc_conv_app_nth)
next
  case (Suc n)
  hence "n < length (tms_of ap) \<Longrightarrow> is_even (length (concat (take (Suc n) (tms_of ap))))"
    unfolding take_Suc_conv_app_nth by fastforce
  with Suc show ?case by(cases "n < length (tms_of ap)", auto)
qed

lemma tpa_states:
  "\<lbrakk>tp = concat (take as (tms_of ap));
  as \<le> length ap\<rbrakk> \<Longrightarrow> 
  start_of (layout_of ap) as = Suc (length tp div 2)"
proof(induct as arbitrary: tp)
  case 0
  thus "?case"
    by(simp add: start_of.simps)
next
  case (Suc as tp)
  have ind: "\<And>tp. \<lbrakk>tp = concat (take as (tms_of ap)); as \<le> length ap\<rbrakk> \<Longrightarrow>
    start_of (layout_of ap) as = Suc (length tp div 2)" by fact
  have tp: "tp = concat (take (Suc as) (tms_of ap))" by fact
  have le: "Suc as \<le> length ap" by fact
  have a: "start_of (layout_of ap) as = Suc (length (concat (take as (tms_of ap))) div 2)"
    using le
    by(intro ind, simp_all)
  from a tp le show "?case"
    apply(simp add: start_of.simps take_Suc_conv_app_nth)
    apply(subgoal_tac "length (concat (take as (tms_of ap))) mod 2= 0")
     apply(subgoal_tac " length (tms_of ap ! as) mod 2 = 0")
      apply(simp add: Abacus.div_apart) 
      apply(simp add: layout_of.simps ci_length  tms_of.simps tpairs_of.simps)
     apply(auto  intro: compile_mod2)
    done
qed

declare fetch.simps[simp]
lemma append_append_fetch: 
  "\<lbrakk>length tp1 mod 2 = 0; length tp mod 2 = 0;
      length tp1 div 2 < a \<and> a \<le> length tp1 div 2 + length tp div 2\<rbrakk>
    \<Longrightarrow>fetch (tp1 @ tp @ tp2) a b = fetch tp (a - length tp1 div 2) b "
  apply(subgoal_tac "\<exists> x. a = length tp1 div 2 + x", erule exE)
   apply(rename_tac x)
   apply(case_tac x, simp)
   apply(subgoal_tac "length tp1 div 2 + Suc nat = 
             Suc (length tp1 div 2 + nat)")
    apply(simp only: fetch.simps nth_of.simps, auto)
   apply(cases b, simp)
    apply(subgoal_tac "2 * (length tp1 div 2) = length tp1", simp)
     apply(subgoal_tac "2 * nat < length tp", simp add: nth_append, simp)
    apply(subgoal_tac "2 * (length tp1 div 2) = length tp1", simp)
    apply(subgoal_tac "2 * nat < length tp", simp add: nth_append, auto)
   apply(auto simp: nth_append)
  apply(rule_tac x = "a - length tp1 div 2" in exI, simp)
  done

lemma step_eq_fetch':
  assumes layout: "ly = layout_of ap"
    and compile: "tp = tm_of ap"
    and fetch: "abc_fetch as ap = Some ins"
    and range1: "s \<ge> start_of ly as"
    and range2: "s < start_of ly (Suc as)"
  shows "fetch tp s b = fetch (ci ly (start_of ly as) ins)
       (Suc s - start_of ly as) b "
proof -
  have "\<exists>tp1 tp2. concat (tms_of ap) = tp1 @ ci ly (start_of ly as) ins @ tp2 \<and>
    tp1 = concat (take as (tms_of ap)) \<and> tp2 = concat (drop (Suc as) (tms_of ap))"
    using assms
    by(intro t_split, simp_all)
  then obtain tp1 tp2 where a: "concat (tms_of ap) = tp1 @ ci ly (start_of ly as) ins @ tp2 \<and>
    tp1 = concat (take as (tms_of ap)) \<and> tp2 = concat (drop (Suc as) (tms_of ap))" by blast
  then have b: "start_of (layout_of ap) as = Suc (length tp1 div 2)"
    using fetch
    by(intro tpa_states, simp, simp add: abc_fetch.simps split: if_splits)
  have "fetch (tp1 @ (ci ly (start_of ly as) ins) @ tp2)  s b = 
        fetch (ci ly (start_of ly as) ins) (s - length tp1 div 2) b"
  proof(intro append_append_fetch)
    show "length tp1 mod 2 = 0"
      using a
      by(auto, rule_tac compile_mod2)
  next
    show "length (ci ly (start_of ly as) ins) mod 2 = 0"
      by(cases ins, auto simp: ci.simps length_findnth tinc_b_def tdec_b_def)
  next
    show "length tp1 div 2 < s \<and> s \<le> 
      length tp1 div 2 + length (ci ly (start_of ly as) ins) div 2"
    proof -
      have "length (ci ly (start_of ly as) ins) div 2 = length_of ins"
        using ci_length by simp
      moreover have "start_of ly (Suc as) = start_of ly as + length_of ins"
        using fetch layout
        apply(simp add: start_of.simps abc_fetch.simps List.take_Suc_conv_app_nth 
            split: if_splits)
        apply(simp add: layout_of.simps)
        done
      ultimately show "?thesis"
        using b layout range1 range2
        apply(simp)
        done
    qed
  qed
  thus "?thesis"
    using b layout a compile  
    apply(simp add: tm_of.simps)
    done
qed

lemma step_eq_fetch: 
  assumes layout: "ly = layout_of ap"
    and compile: "tp = tm_of ap"
    and abc_fetch: "abc_fetch as ap = Some ins" 
    and fetch: "fetch (ci ly (start_of ly as) ins)
       (Suc s - start_of ly as) b = (ac, ns)"
    and notfinal: "ns \<noteq> 0"
  shows "fetch tp s b = (ac, ns)"
proof -
  have "s \<ge> start_of ly as"
  proof(cases "s \<ge> start_of ly as")
    case True thus "?thesis" by simp
  next
    case False 
    have "\<not> start_of ly as \<le> s" by fact
    then have "Suc s - start_of ly as = 0"
      by arith
    then have "fetch (ci ly (start_of ly as) ins)
       (Suc s - start_of ly as) b = (Nop, 0)"
      by(simp add: fetch.simps)
    with notfinal fetch show "?thesis"
      by(simp)
  qed
  moreover have "s < start_of ly (Suc as)"
  proof(cases "s < start_of ly (Suc as)")
    case True thus "?thesis" by simp
  next
    case False
    have h: "\<not> s < start_of ly (Suc as)"
      by fact
    then have "s > start_of ly as"
      using abc_fetch layout
      apply(simp add: start_of.simps abc_fetch.simps split: if_splits)
      apply(simp add: List.take_Suc_conv_app_nth, auto)
      apply(subgoal_tac "layout_of ap ! as > 0") 
       apply arith
      apply(simp add: layout_of.simps)
      apply(cases "ap!as", auto simp: length_of.simps)
      done
    from this and h have "fetch (ci ly (start_of ly as) ins) (Suc s - start_of ly as) b = (Nop, 0)"
      using abc_fetch layout
      apply(cases b;cases ins)
           apply(simp_all add:Suc_diff_le start_of_Suc2 start_of_Suc1 start_of_Suc3)
      by (simp_all only: length_ci_inc length_ci_dec length_ci_goto, auto)
    from fetch and notfinal this show "?thesis"by simp
  qed
  ultimately show "?thesis"
    using assms
    by(drule_tac b= b and ins = ins in step_eq_fetch', auto)
qed


lemma step_eq_in:
  assumes layout: "ly = layout_of ap"
    and compile: "tp = tm_of ap"
    and fetch: "abc_fetch as ap = Some ins"    
    and exec: "step (s, l, r) (ci ly (start_of ly as) ins, start_of ly as - 1) 
  = (s', l', r')"
    and notfinal: "s' \<noteq> 0"
  shows "step (s, l, r) (tp, 0) = (s', l', r')"
  using assms
  apply(simp add: step.simps)
  apply(cases "fetch (ci (layout_of ap) (start_of (layout_of ap) as) ins)
    (Suc s - start_of (layout_of ap) as) (read r)", simp)
  using layout
  apply(drule_tac s = s and b = "read r" and ac = a in step_eq_fetch, auto)
  done

lemma steps_eq_in:
  assumes layout: "ly = layout_of ap"
    and compile: "tp = tm_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
    and fetch: "abc_fetch as ap = Some ins"    
    and exec: "steps (s, l, r) (ci ly (start_of ly as) ins, start_of ly as - 1) stp 
  = (s', l', r')"
    and notfinal: "s' \<noteq> 0"
  shows "steps (s, l, r) (tp, 0) stp = (s', l', r')"
  using exec notfinal
proof(induct stp arbitrary: s' l' r', simp add: steps.simps)
  fix stp s' l' r'
  assume ind: 
    "\<And>s' l' r'. \<lbrakk>steps (s, l, r) (ci ly (start_of ly as) ins, start_of ly as - 1) stp = (s', l', r'); s' \<noteq> 0\<rbrakk>
              \<Longrightarrow> steps (s, l, r) (tp, 0) stp = (s', l', r')"
    and h: "steps (s, l, r) (ci ly (start_of ly as) ins, start_of ly as - 1) (Suc stp) = (s', l', r')" "s' \<noteq> 0"
  obtain s1 l1 r1 where g: "steps (s, l, r) (ci ly (start_of ly as) ins, start_of ly as - 1) stp = 
                        (s1, l1, r1)"
    apply(cases "steps (s, l, r) (ci ly (start_of ly as) ins, start_of ly as - 1) stp") by blast
  moreover hence "s1 \<noteq> 0"
    using h
    apply(simp add: step_red)
    apply(cases "0 < s1", simp_all)
    done
  ultimately have "steps (s, l, r) (tp, 0) stp = (s1, l1, r1)"
    apply(rule_tac ind, auto)
    done
  thus "steps (s, l, r) (tp, 0) (Suc stp) = (s', l', r')"
    using h g assms
    apply(simp add: step_red)
    apply(rule_tac step_eq_in, auto)
    done
qed

lemma tm_append_fetch_first: 
  "\<lbrakk>fetch A s b = (ac, ns); ns \<noteq> 0\<rbrakk> \<Longrightarrow> 
    fetch (A @ B) s b = (ac, ns)"
  by(cases b;cases s;force simp: fetch.simps nth_append split: if_splits)

lemma tm_append_first_step_eq: 
  assumes "step (s, l, r) (A, off) = (s', l', r')"
    and "s' \<noteq> 0"
  shows "step (s, l, r) (A @ B, off) = (s', l', r')"
  using assms
  apply(simp add: step.simps)
  apply(cases "fetch A (s - off) (read r)")
  apply(frule_tac  B = B and b = "read r" in tm_append_fetch_first, auto)
  done

lemma tm_append_first_steps_eq: 
  assumes "steps (s, l, r) (A, off) stp = (s', l', r')"
    and "s' \<noteq> 0"
  shows "steps (s, l, r) (A @ B, off) stp = (s', l', r')"
  using assms
proof(induct stp arbitrary: s' l' r', simp add: steps.simps)
  fix stp s' l' r'
  assume ind: "\<And>s' l' r'. \<lbrakk>steps (s, l, r) (A, off) stp = (s', l', r'); s' \<noteq> 0\<rbrakk>
    \<Longrightarrow> steps (s, l, r) (A @ B, off) stp = (s', l', r')"
    and h: "steps (s, l, r) (A, off) (Suc stp) = (s', l', r')" "s' \<noteq> 0"
  obtain sa la ra where a: "steps (s, l, r) (A, off) stp = (sa, la, ra)"
    apply(cases "steps (s, l, r) (A, off) stp") by blast
  hence "steps (s, l, r) (A @ B, off) stp = (sa, la, ra) \<and> sa \<noteq> 0"
    using h ind[of sa la ra]
    apply(cases sa, simp_all)
    done
  thus "steps (s, l, r) (A @ B, off) (Suc stp) = (s', l', r')"
    using h a
    apply(simp add: step_red)
    apply(intro tm_append_first_step_eq, simp_all)
    done
qed

lemma tm_append_second_fetch_eq:
  assumes
    even: "length A mod 2 = 0"
    and off: "off = length A div 2"
    and fetch: "fetch B s b = (ac, ns)"
    and notfinal: "ns \<noteq> 0"
  shows "fetch (A @ shift B off) (s + off) b = (ac, ns + off)"
  using assms
  by(cases b;cases s,auto simp: nth_append shift.simps split: if_splits)

lemma tm_append_second_step_eq: 
  assumes 
    exec: "step0 (s, l, r) B = (s', l', r')"
    and notfinal: "s' \<noteq> 0"
    and off: "off = length A div 2"
    and even: "length A mod 2 = 0"
  shows "step0 (s + off, l, r) (A @ shift B off) = (s' + off, l', r')"
  using assms
  apply(simp add: step.simps)
  apply(cases "fetch B s (read r)")
  apply(frule_tac tm_append_second_fetch_eq, simp_all, auto)
  done


lemma tm_append_second_steps_eq: 
  assumes 
    exec: "steps (s, l, r) (B, 0) stp = (s', l', r')"
    and notfinal: "s' \<noteq> 0"
    and off: "off = length A div 2"
    and even: "length A mod 2 = 0"
  shows "steps (s + off, l, r) (A @ shift B off, 0) stp = (s' + off, l', r')"
  using exec notfinal
proof(induct stp arbitrary: s' l' r')
  case 0
  thus "steps0 (s + off, l, r) (A @ shift B off) 0 = (s' + off, l', r')"
    by(simp add: steps.simps)
next
  case (Suc stp s' l' r')
  have ind: "\<And>s' l' r'. \<lbrakk>steps0 (s, l, r) B stp = (s', l', r'); s' \<noteq> 0\<rbrakk> \<Longrightarrow> 
    steps0 (s + off, l, r) (A @ shift B off) stp = (s' + off, l', r')"
    by fact
  have h: "steps0 (s, l, r) B (Suc stp) = (s', l', r')" by fact
  have k: "s' \<noteq> 0" by fact
  obtain s'' l'' r'' where a: "steps0 (s, l, r) B stp = (s'', l'', r'')"
    by (metis prod_cases3)
  then have b: "s'' \<noteq> 0"
    using h k
    by(intro notI, auto)
  from a b have c: "steps0 (s + off, l, r) (A @ shift B off) stp = (s'' + off, l'', r'')"
    by(erule_tac ind, simp)
  from c b h a k assms show "?case"
    by(auto intro:tm_append_second_step_eq)
qed

lemma tm_append_second_fetch0_eq:
  assumes
    even: "length A mod 2 = 0"
    and off: "off = length A div 2"
    and fetch: "fetch B s b = (ac, 0)"
    and notfinal: "s \<noteq> 0"
  shows "fetch (A @ shift B off) (s + off) b = (ac, 0)"
  using assms
  apply(cases b;cases s)
     apply(auto simp: fetch.simps nth_append shift.simps split: if_splits)
  done

lemma tm_append_second_halt_eq:
  assumes 
    exec: "steps (Suc 0, l, r) (B, 0) stp = (0, l', r')"
    and wf_B: "tm_wf (B, 0)"
    and off: "off = length A div 2"
    and even: "length A mod 2 = 0"
  shows "steps (Suc off, l, r) (A @ shift B off, 0) stp = (0, l', r')"
proof -
  have "\<exists>n. \<not> is_final (steps0 (1, l, r) B n) \<and> steps0 (1, l, r) B (Suc n) = (0, l', r')"
    using exec by(rule_tac before_final, simp)
  then obtain n where a: 
    "\<not> is_final (steps0 (1, l, r) B n) \<and> steps0 (1, l, r) B (Suc n) = (0, l', r')" ..
  obtain s'' l'' r'' where b: "steps0 (1, l, r) B n = (s'', l'', r'') \<and> s'' >0"
    using a
    by(cases "steps0 (1, l, r) B n", auto)
  have c: "steps (Suc 0 + off, l, r) (A @ shift B off, 0) n = (s'' + off, l'', r'')"
    using a b assms
    by(rule_tac tm_append_second_steps_eq, simp_all)
  obtain ac where d: "fetch B s'' (read r'') = (ac, 0)"
    using  b a
    by(cases "fetch B s'' (read r'')", auto simp: step_red step.simps)
  then have "fetch (A @ shift B off) (s'' + off) (read r'') = (ac, 0)"
    using assms b
    by(rule_tac tm_append_second_fetch0_eq, simp_all)
  then have e: "steps (Suc 0 + off, l, r) (A @ shift B off, 0) (Suc n) = (0, l', r')"
    using a b assms c d
    by(simp add: step_red step.simps)
  from a have "n < stp"
    using exec
  proof(cases "n < stp")
    case  True thus "?thesis" by simp
  next
    case False
    have "\<not> n < stp" by fact
    then obtain d where  "n = stp + d"
      by (metis add.comm_neutral less_imp_add_positive nat_neq_iff)
    thus "?thesis"
      using a e exec
      by(simp)
  qed
  then obtain d where "stp = Suc n + d"
    by(metis add_Suc less_iff_Suc_add)
  thus "?thesis"
    using e
    by(simp only: steps_add, simp)
qed

lemma tm_append_steps: 
  assumes 
    aexec: "steps (s, l, r) (A, 0) stpa = (Suc (length A div 2), la, ra)"
    and bexec: "steps (Suc 0, la, ra) (B, 0) stpb =  (sb, lb, rb)"
    and notfinal: "sb \<noteq> 0"
    and off: "off = length A div 2"
    and even: "length A mod 2 = 0"
  shows "steps (s, l, r) (A @ shift B off, 0) (stpa + stpb) = (sb + off, lb, rb)"
proof -
  have "steps (s, l, r) (A@shift B off, 0) stpa = (Suc (length A div 2), la, ra)"
    apply(intro tm_append_first_steps_eq)
     apply(auto simp: assms)
    done
  moreover have "steps (1 + off, la, ra) (A @ shift B off, 0) stpb = (sb + off, lb, rb)"
    apply(intro tm_append_second_steps_eq)
       apply(auto simp: assms bexec)
    done
  ultimately show "steps (s, l, r) (A @ shift B off, 0) (stpa + stpb) = (sb + off, lb, rb)"
    apply(simp add: steps_add off)
    done
qed

subsection \<open>Crsp of Inc\<close>

fun at_begin_fst_bwtn :: "inc_inv_t"
  where
    "at_begin_fst_bwtn (as, lm) (s, l, r) ires = 
      (\<exists> lm1 tn rn. lm1 = (lm @ 0\<up>tn) \<and> length lm1 = s \<and> 
          (if lm1 = [] then l = Bk # Bk # ires
           else l = [Bk]@<rev lm1>@Bk#Bk#ires) \<and> r = Bk\<up>rn)" 


fun at_begin_fst_awtn :: "inc_inv_t"
  where
    "at_begin_fst_awtn (as, lm) (s, l, r) ires = 
      (\<exists> lm1 tn rn. lm1 = (lm @ 0\<up>tn) \<and> length lm1 = s \<and>
         (if lm1 = []  then l = Bk # Bk # ires
          else l = [Bk]@<rev lm1>@Bk#Bk#ires) \<and> r = [Oc]@Bk\<up>rn)"

fun at_begin_norm :: "inc_inv_t"
  where
    "at_begin_norm (as, lm) (s, l, r) ires= 
      (\<exists> lm1 lm2 rn. lm = lm1 @ lm2 \<and> length lm1 = s \<and> 
        (if lm1 = [] then l = Bk # Bk # ires
         else l = Bk # <rev lm1> @ Bk # Bk # ires ) \<and> r = <lm2>@Bk\<up>rn)"

fun in_middle :: "inc_inv_t"
  where
    "in_middle (as, lm) (s, l, r) ires = 
      (\<exists> lm1 lm2 tn m ml mr rn. lm @ 0\<up>tn = lm1 @ [m] @ lm2
       \<and> length lm1 = s \<and> m + 1 = ml + mr \<and>  
         ml \<noteq> 0 \<and> tn = s + 1 - length lm \<and> 
       (if lm1 = [] then l = Oc\<up>ml @ Bk # Bk # ires 
        else l = Oc\<up>ml@[Bk]@<rev lm1>@
                 Bk # Bk # ires) \<and> (r = Oc\<up>mr @ [Bk] @ <lm2>@ Bk\<up>rn \<or> 
      (lm2 = [] \<and> r = Oc\<up>mr))
      )"

fun inv_locate_a :: "inc_inv_t"
  where "inv_locate_a (as, lm) (s, l, r) ires = 
     (at_begin_norm (as, lm) (s, l, r) ires \<or>
      at_begin_fst_bwtn (as, lm) (s, l, r) ires \<or>
      at_begin_fst_awtn (as, lm) (s, l, r) ires
      )"

fun inv_locate_b :: "inc_inv_t"
  where "inv_locate_b (as, lm) (s, l, r) ires = 
        (in_middle (as, lm) (s, l, r)) ires "

fun inv_after_write :: "inc_inv_t"
  where "inv_after_write (as, lm) (s, l, r) ires = 
           (\<exists> rn m lm1 lm2. lm = lm1 @ m # lm2 \<and>
             (if lm1 = [] then l = Oc\<up>m @ Bk # Bk # ires
              else Oc # l = Oc\<up>Suc m@ Bk # <rev lm1> @ 
                      Bk # Bk # ires) \<and> r = [Oc] @ <lm2> @ Bk\<up>rn)"

fun inv_after_move :: "inc_inv_t"
  where "inv_after_move (as, lm) (s, l, r) ires = 
      (\<exists> rn m lm1 lm2. lm = lm1 @ m # lm2 \<and>
        (if lm1 = [] then l = Oc\<up>Suc m @ Bk # Bk # ires
         else l = Oc\<up>Suc m@ Bk # <rev lm1> @ Bk # Bk # ires) \<and> 
        r = <lm2> @ Bk\<up>rn)"

fun inv_after_clear :: "inc_inv_t"
  where "inv_after_clear (as, lm) (s, l, r) ires =
       (\<exists> rn m lm1 lm2 r'. lm = lm1 @ m # lm2 \<and> 
        (if lm1 = [] then l = Oc\<up>Suc m @ Bk # Bk # ires
         else l = Oc\<up>Suc m @ Bk # <rev lm1> @ Bk # Bk # ires) \<and> 
          r = Bk # r' \<and> Oc # r' = <lm2> @ Bk\<up>rn)"

fun inv_on_right_moving :: "inc_inv_t"
  where "inv_on_right_moving (as, lm) (s, l, r) ires = 
       (\<exists> lm1 lm2 m ml mr rn. lm = lm1 @ [m] @ lm2 \<and> 
            ml + mr = m \<and> 
          (if lm1 = [] then l = Oc\<up>ml @ Bk # Bk # ires
          else l = Oc\<up>ml  @ [Bk] @ <rev lm1> @ Bk # Bk # ires) \<and> 
         ((r = Oc\<up>mr @ [Bk] @ <lm2> @ Bk\<up>rn) \<or> 
          (r = Oc\<up>mr \<and> lm2 = [])))"

fun inv_on_left_moving_norm :: "inc_inv_t"
  where "inv_on_left_moving_norm (as, lm) (s, l, r) ires =
      (\<exists> lm1 lm2 m ml mr rn. lm = lm1 @ [m] @ lm2 \<and>  
             ml + mr = Suc m \<and> mr > 0 \<and> (if lm1 = [] then l = Oc\<up>ml @ Bk # Bk # ires
                                         else l =  Oc\<up>ml @ Bk # <rev lm1> @ Bk # Bk # ires)
        \<and> (r = Oc\<up>mr @ Bk # <lm2> @ Bk\<up>rn \<or> 
           (lm2 = [] \<and> r = Oc\<up>mr)))"

fun inv_on_left_moving_in_middle_B:: "inc_inv_t"
  where "inv_on_left_moving_in_middle_B (as, lm) (s, l, r) ires =
                (\<exists> lm1 lm2 rn. lm = lm1 @ lm2 \<and>  
                     (if lm1 = [] then l = Bk # ires
                      else l = <rev lm1> @ Bk # Bk # ires) \<and> 
                      r = Bk # <lm2> @ Bk\<up>rn)"

fun inv_on_left_moving :: "inc_inv_t"
  where "inv_on_left_moving (as, lm) (s, l, r) ires = 
       (inv_on_left_moving_norm  (as, lm) (s, l, r) ires \<or>
        inv_on_left_moving_in_middle_B (as, lm) (s, l, r) ires)"


fun inv_check_left_moving_on_leftmost :: "inc_inv_t"
  where "inv_check_left_moving_on_leftmost (as, lm) (s, l, r) ires = 
                (\<exists> rn. l = ires \<and> r = [Bk, Bk] @ <lm> @  Bk\<up>rn)"

fun inv_check_left_moving_in_middle :: "inc_inv_t"
  where "inv_check_left_moving_in_middle (as, lm) (s, l, r) ires = 
              (\<exists> lm1 lm2 r' rn. lm = lm1 @ lm2 \<and>
                 (Oc # l = <rev lm1> @ Bk # Bk # ires) \<and> r = Oc # Bk # r' \<and> 
                           r' = <lm2> @  Bk\<up>rn)"

fun inv_check_left_moving :: "inc_inv_t"
  where "inv_check_left_moving (as, lm) (s, l, r) ires = 
             (inv_check_left_moving_on_leftmost (as, lm) (s, l, r) ires \<or>
             inv_check_left_moving_in_middle (as, lm) (s, l, r) ires)"

fun inv_after_left_moving :: "inc_inv_t"
  where "inv_after_left_moving (as, lm) (s, l, r) ires= 
              (\<exists> rn. l = Bk # ires \<and> r = Bk # <lm> @  Bk\<up>rn)"

fun inv_stop :: "inc_inv_t"
  where "inv_stop (as, lm) (s, l, r) ires= 
              (\<exists> rn. l = Bk # Bk # ires \<and> r = <lm> @  Bk\<up>rn)"

lemma halt_lemma2': 
  "\<lbrakk>wf LE;  \<forall> n. ((\<not> P (f n) \<and> Q (f n)) \<longrightarrow> 
    (Q (f (Suc n)) \<and> (f (Suc n), (f n)) \<in> LE)); Q (f 0)\<rbrakk> 
      \<Longrightarrow> \<exists> n. P (f n)"
  apply(intro exCI, simp)
  apply(subgoal_tac "\<forall> n. Q (f n)")
   apply(drule_tac f = f in wf_inv_image)
   apply(erule wf_induct)
   apply(auto)
  apply(rename_tac n,induct_tac n; simp)
  done

lemma halt_lemma2'': 
  "\<lbrakk>P (f n); \<not> P (f (0::nat))\<rbrakk> \<Longrightarrow> 
         \<exists> n. (P (f n) \<and> (\<forall> i < n. \<not> P (f i)))"
  apply(induct n rule: nat_less_induct, auto)
  done

lemma halt_lemma2''':
  "\<lbrakk>\<forall>n. \<not> P (f n) \<and> Q (f n) \<longrightarrow> Q (f (Suc n)) \<and> (f (Suc n), f n) \<in> LE;
                 Q (f 0);  \<forall>i<na. \<not> P (f i)\<rbrakk> \<Longrightarrow> Q (f na)"
  apply(induct na, simp, simp)
  done

lemma halt_lemma2: 
  "\<lbrakk>wf LE;  
    Q (f 0); \<not> P (f 0);
    \<forall> n. ((\<not> P (f n) \<and> Q (f n)) \<longrightarrow> (Q (f (Suc n)) \<and> (f (Suc n), (f n)) \<in> LE))\<rbrakk> 
  \<Longrightarrow> \<exists> n. P (f n) \<and> Q (f n)"
  apply(insert halt_lemma2' [of LE P f Q], simp, erule_tac exE)
  apply(subgoal_tac "\<exists> n. (P (f n) \<and> (\<forall> i < n. \<not> P (f i)))")
   apply(erule_tac exE)+
   apply(rename_tac n na)
   apply(rule_tac x = na in exI, auto)
   apply(rule halt_lemma2''', simp, simp, simp)
  apply(erule_tac halt_lemma2'', simp)
  done


fun findnth_inv :: "layout \<Rightarrow> nat \<Rightarrow> inc_inv_t"
  where
    "findnth_inv ly n (as, lm) (s, l, r) ires =
              (if s = 0 then False
               else if s \<le> Suc (2*n) then 
                  if s mod 2 = 1 then inv_locate_a (as, lm) ((s - 1) div 2, l, r) ires
                  else inv_locate_b (as, lm) ((s - 1) div 2, l, r) ires
               else False)"


fun findnth_state :: "config \<Rightarrow> nat \<Rightarrow> nat"
  where
    "findnth_state (s, l, r) n = (Suc (2*n) - s)"

fun findnth_step :: "config \<Rightarrow> nat \<Rightarrow> nat"
  where
    "findnth_step (s, l, r) n = 
           (if s mod 2 = 1 then
                   (if (r \<noteq> [] \<and> hd r = Oc) then 0
                    else 1)
            else length r)"

fun findnth_measure :: "config \<times> nat \<Rightarrow> nat \<times> nat"
  where
    "findnth_measure (c, n) = 
     (findnth_state c n, findnth_step c n)"

definition lex_pair :: "((nat \<times> nat) \<times> nat \<times> nat) set"
  where
    "lex_pair \<equiv> less_than <*lex*> less_than"

definition findnth_LE :: "((config \<times> nat) \<times> (config \<times> nat)) set"
  where
    "findnth_LE \<equiv> (inv_image lex_pair findnth_measure)"

lemma wf_findnth_LE: "wf findnth_LE"
  by(auto simp: findnth_LE_def lex_pair_def)

declare findnth_inv.simps[simp del]

lemma x_is_2n_arith[simp]: 
  "\<lbrakk>x < Suc (Suc (2 * n)); Suc x mod 2 = Suc 0; \<not> x < 2 * n\<rbrakk>
 \<Longrightarrow> x = 2*n"
  by arith


lemma between_sucs:"x < Suc n \<Longrightarrow> \<not> x < n \<Longrightarrow> x = n" by auto

lemma fetch_findnth[simp]: 
  "\<lbrakk>0 < a; a < Suc (2 * n); a mod 2 = Suc 0\<rbrakk> \<Longrightarrow> fetch (findnth n) a Oc = (R, Suc a)"
  "\<lbrakk>0 < a; a < Suc (2 * n); a mod 2 \<noteq> Suc 0\<rbrakk> \<Longrightarrow> fetch (findnth n) a Oc = (R, a)"
  "\<lbrakk>0 < a; a < Suc (2 * n); a mod 2 \<noteq> Suc 0\<rbrakk> \<Longrightarrow> fetch (findnth n) a Bk = (R, Suc a)"
  "\<lbrakk>0 < a; a < Suc (2 * n); a mod 2 = Suc 0\<rbrakk> \<Longrightarrow> fetch (findnth n) a Bk = (W1, a)"
  by(cases a;induct n;force simp: length_findnth nth_append dest!:between_sucs)+

declare at_begin_norm.simps[simp del] at_begin_fst_bwtn.simps[simp del] 
  at_begin_fst_awtn.simps[simp del] in_middle.simps[simp del] 
  abc_lm_s.simps[simp del] abc_lm_v.simps[simp del]  
  ci.simps[simp del] inv_after_move.simps[simp del] 
  inv_on_left_moving_norm.simps[simp del] 
  inv_on_left_moving_in_middle_B.simps[simp del]
  inv_after_clear.simps[simp del] 
  inv_after_write.simps[simp del] inv_on_left_moving.simps[simp del]
  inv_on_right_moving.simps[simp del] 
  inv_check_left_moving.simps[simp del] 
  inv_check_left_moving_in_middle.simps[simp del]
  inv_check_left_moving_on_leftmost.simps[simp del] 
  inv_after_left_moving.simps[simp del]
  inv_stop.simps[simp del] inv_locate_a.simps[simp del] 
  inv_locate_b.simps[simp del]

lemma replicate_once[intro]: "\<exists>rn. [Bk] = Bk \<up> rn"
  by (metis replicate.simps)

lemma at_begin_norm_Bk[intro]:  "at_begin_norm (as, am) (q, aaa, []) ires
             \<Longrightarrow> at_begin_norm (as, am) (q, aaa, [Bk]) ires"
  apply(simp add: at_begin_norm.simps)
  by fastforce

lemma at_begin_fst_bwtn_Bk[intro]: "at_begin_fst_bwtn (as, am) (q, aaa, []) ires 
            \<Longrightarrow> at_begin_fst_bwtn (as, am) (q, aaa, [Bk]) ires"
  apply(simp only: at_begin_fst_bwtn.simps)
  using replicate_once by blast

lemma at_begin_fst_awtn_Bk[intro]: "at_begin_fst_awtn (as, am) (q, aaa, []) ires
           \<Longrightarrow> at_begin_fst_awtn (as, am) (q, aaa, [Bk]) ires"
  apply(auto simp: at_begin_fst_awtn.simps)
  done 

lemma inv_locate_a_Bk[intro]: "inv_locate_a (as, am) (q, aaa, []) ires
            \<Longrightarrow> inv_locate_a (as, am) (q, aaa, [Bk]) ires"
  apply(simp only: inv_locate_a.simps)
  apply(erule disj_forward)
   defer
   apply(erule disj_forward, auto)
  done

lemma locate_a_2_locate_a[simp]: "inv_locate_a (as, am) (q, aaa, Bk # xs) ires
       \<Longrightarrow> inv_locate_a (as, am) (q, aaa, Oc # xs) ires"
  apply(simp only: inv_locate_a.simps at_begin_norm.simps 
      at_begin_fst_bwtn.simps at_begin_fst_awtn.simps)
  apply(erule_tac disjE, erule exE, erule exE, erule exE, 
      rule disjI2, rule disjI2)
   defer
   apply(erule_tac disjE, erule exE, erule exE, 
      erule exE, rule disjI2, rule disjI2)
    prefer 2
    apply(simp)
proof-
  fix lm1 tn rn
  assume k: "lm1 = am @ 0\<up>tn \<and> length lm1 = q \<and> (if lm1 = [] then aaa = Bk # Bk # 
    ires else aaa = [Bk] @ <rev lm1> @ Bk # Bk # ires) \<and> Bk # xs = Bk\<up>rn"
  thus "\<exists>lm1 tn rn. lm1 = am @ 0 \<up> tn \<and> length lm1 = q \<and> 
    (if lm1 = [] then aaa = Bk # Bk # ires else aaa = [Bk] @ <rev lm1> @ Bk # Bk # ires) \<and> Oc # xs = [Oc] @ Bk \<up> rn"
    (is "\<exists>lm1 tn rn. ?P lm1 tn rn")
  proof -
    from k have "?P lm1 tn (rn - 1)"
      by (auto simp: Cons_replicate_eq)
    thus ?thesis by blast
  qed
next
  fix lm1 lm2 rn
  assume h1: "am = lm1 @ lm2 \<and> length lm1 = q \<and> (if lm1 = [] 
    then aaa = Bk # Bk # ires else aaa = Bk # <rev lm1> @ Bk # Bk # ires) \<and>
    Bk # xs = <lm2> @ Bk\<up>rn"
  from h1 have h2: "lm2 = []"
    apply(auto split: if_splits;cases lm2;simp add: tape_of_nl_cons split: if_splits)
    done
  from h1 and h2 show "\<exists>lm1 tn rn. lm1 = am @ 0\<up>tn \<and> length lm1 = q \<and> 
    (if lm1 = [] then aaa = Bk # Bk # ires else aaa = [Bk] @ <rev lm1> @ Bk # Bk # ires) \<and>
    Oc # xs = [Oc] @ Bk\<up>rn" 
    (is "\<exists>lm1 tn rn. ?P lm1 tn rn")
  proof -
    from h1 and h2  have "?P lm1 0 (rn - 1)"
      apply(auto simp:tape_of_nat_def)
      by(cases rn, simp, simp)
    thus ?thesis by blast
  qed
qed

lemma inv_locate_a[simp]: "inv_locate_a (as, am) (q, aaa, []) ires \<Longrightarrow> 
               inv_locate_a (as, am) (q, aaa, [Oc]) ires"
  apply(insert locate_a_2_locate_a [of as am q aaa "[]"])
  apply(subgoal_tac "inv_locate_a (as, am) (q, aaa, [Bk]) ires", auto)
  done

(*inv: from locate_b to locate_b*)
lemma inv_locate_b[simp]: "inv_locate_b (as, am) (q, aaa, Oc # xs) ires
         \<Longrightarrow> inv_locate_b (as, am) (q, Oc # aaa, xs) ires"
  apply(simp only: inv_locate_b.simps in_middle.simps)
  apply(erule exE)+
  apply(rename_tac lm1 lm2 tn m ml mr rn)
  apply(rule_tac x = lm1 in exI, rule_tac x = lm2 in exI, 
      rule_tac x = tn in exI, rule_tac x = m in exI)
  apply(rule_tac x = "Suc ml" in exI, rule_tac x = "mr - 1" in exI,
      rule_tac x = rn in exI)
  apply(case_tac mr, simp_all, auto)
  done

lemma tape_nat[simp]:  "<[x::nat]> = Oc\<up>(Suc x)"
  apply(simp add: tape_of_nat_def tape_of_list_def)
  done

lemma inv_locate[simp]: "\<lbrakk>inv_locate_b (as, am) (q, aaa, Bk # xs) ires; \<exists>n. xs = Bk\<up>n\<rbrakk>
            \<Longrightarrow> inv_locate_a (as, am) (Suc q, Bk # aaa, xs) ires"
  apply(simp add: inv_locate_b.simps inv_locate_a.simps)
  apply(rule_tac disjI2, rule_tac disjI1)
  apply(simp only: in_middle.simps at_begin_fst_bwtn.simps)
  apply(erule_tac exE)+
  apply(rename_tac lm1 n lm2 tn m ml mr rn)
  apply(rule_tac x = "lm1 @ [m]" in exI, rule_tac x = tn in exI, simp split: if_splits)
   apply(case_tac mr, simp_all)
   apply(cases "length am", simp_all, case_tac tn, simp_all)
   apply(case_tac lm2, simp_all add: tape_of_nl_cons split: if_splits)
     apply(cases am, simp_all)
    apply(case_tac n, simp_all)
   apply(case_tac n, simp_all)
  apply(case_tac mr, simp_all)
  apply(case_tac lm2, simp_all add: tape_of_nl_cons split: if_splits, auto)
   apply(case_tac [!] n, simp_all)
  done

lemma repeat_Bk_no_Oc[simp]: "(Oc # r = Bk \<up> rn) = False"
  apply(cases rn, simp_all)
  done

lemma repeat_Bk[simp]: "(\<exists>rna. Bk \<up> rn = Bk # Bk \<up> rna) \<or> rn = 0"
  apply(cases rn, auto)
  done

lemma inv_locate_b_Oc_via_a[simp]: 
  assumes "inv_locate_a (as, lm) (q, l, Oc # r) ires"
  shows "inv_locate_b (as, lm) (q, Oc # l, r) ires"
proof -
  show ?thesis using assms unfolding inv_locate_a.simps inv_locate_b.simps
      at_begin_norm.simps at_begin_fst_bwtn.simps at_begin_fst_awtn.simps
    apply(simp only:in_middle.simps)
    apply(erule disjE, erule exE, erule exE, erule exE)
     apply(rename_tac Lm1 Lm2 Rn)
     apply(rule_tac x = Lm1 in exI, rule_tac x = "tl Lm2" in exI)
     apply(rule_tac x = 0 in exI, rule_tac x = "hd Lm2" in exI)
     apply(rule_tac x = 1 in exI, rule_tac x = "hd Lm2" in exI)
     apply(case_tac Lm2, force simp: tape_of_nl_cons )
     apply(case_tac "tl Lm2", simp_all)
     apply(case_tac Rn, auto simp: tape_of_nl_cons )
    apply(rename_tac tn rn)
    apply(rule_tac x = "lm @ replicate tn 0" in exI, 
        rule_tac x = "[]" in exI, 
        rule_tac x = "Suc tn" in exI, 
        rule_tac x = 0 in exI, auto simp add: replicate_append_same)
    apply(rule_tac x = "Suc 0" in exI, auto)
    done
qed

lemma length_equal: "xs = ys \<Longrightarrow> length xs = length ys"
  by auto

lemma inv_locate_a_Bk_via_b[simp]: "\<lbrakk>inv_locate_b (as, am) (q, aaa, Bk # xs) ires; 
                \<not> (\<exists>n. xs = Bk\<up>n)\<rbrakk> 
       \<Longrightarrow> inv_locate_a (as, am) (Suc q, Bk # aaa, xs) ires"
  apply(simp add: inv_locate_b.simps inv_locate_a.simps)
  apply(rule_tac disjI1)
  apply(simp only: in_middle.simps at_begin_norm.simps)
  apply(erule_tac exE)+
  apply(rename_tac lm1 lm2 tn m ml mr rn)
  apply(rule_tac x = "lm1 @ [m]" in exI, rule_tac x = lm2 in exI, simp)
  apply(subgoal_tac "tn = 0", simp , auto split: if_splits)
    apply(simp add: tape_of_nl_cons)
   apply(drule_tac length_equal, simp)
   apply(cases "length am", simp_all, erule_tac x = rn in allE, simp)
  apply(drule_tac length_equal, simp)
  apply(case_tac "(Suc (length lm1) - length am)", simp_all)
  apply(case_tac lm2, simp, simp)
  done

lemma locate_b_2_a[intro]: 
  "inv_locate_b (as, am) (q, aaa, Bk # xs) ires
    \<Longrightarrow> inv_locate_a (as, am) (Suc q, Bk # aaa, xs) ires"
  apply(cases "\<exists> n. xs = Bk\<up>n", simp, simp)
  done


lemma inv_locate_b_Bk[simp]:  "inv_locate_b (as, am) (q, l, []) ires 
           \<Longrightarrow>  inv_locate_b (as, am) (q, l, [Bk]) ires"
  by(force simp add: inv_locate_b.simps in_middle.simps)

(*inv: from locate_b to after_write*)

lemma div_rounding_down[simp]: "(2*q - Suc 0) div 2 = (q - 1)" "(Suc (2*q)) div 2 = q"
  by arith+

lemma even_plus_one_odd[simp]: "x mod 2 = 0 \<Longrightarrow> Suc x mod 2 = Suc 0"
  by arith

lemma odd_plus_one_even[simp]: "x mod 2 = Suc 0 \<Longrightarrow> Suc x mod 2 = 0"
  by arith

lemma locate_b_2_locate_a[simp]: 
  "\<lbrakk>q > 0;  inv_locate_b (as, am) (q - Suc 0, aaa, Bk # xs) ires\<rbrakk>
   \<Longrightarrow>  inv_locate_a (as, am) (q, Bk # aaa, xs) ires"
  apply(insert locate_b_2_a [of as am "q - 1" aaa xs ires], simp)
  done

(*inv: from locate_b to after_write*)

lemma findnth_inv_layout_of_via_crsp[simp]:
  "crsp (layout_of ap) (as, lm) (s, l, r) ires
  \<Longrightarrow> findnth_inv (layout_of ap) n (as, lm) (Suc 0, l, r) ires"
  by(auto simp: crsp.simps findnth_inv.simps inv_locate_a.simps
      at_begin_norm.simps at_begin_fst_awtn.simps at_begin_fst_bwtn.simps)

lemma findnth_correct_pre: 
  assumes layout: "ly = layout_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
    and not0: "n > 0"
    and f: "f = (\<lambda> stp. (steps (Suc 0, l, r) (findnth n, 0) stp, n))"
    and P: "P = (\<lambda> ((s, l, r), n). s = Suc (2 * n))"
    and Q: "Q = (\<lambda> ((s, l, r), n). findnth_inv ly n (as, lm) (s, l, r) ires)"
  shows "\<exists> stp. P (f stp) \<and> Q (f stp)"
proof(rule_tac LE = findnth_LE in halt_lemma2)
  show "wf findnth_LE"  by(intro wf_findnth_LE)
next
  show "Q (f 0)"
    using crsp layout
    apply(simp add: f P Q steps.simps)
    done
next
  show "\<not> P (f 0)"
    using not0
    apply(simp add: f P steps.simps)
    done
next
  have "\<not> P (f na) \<and> Q (f na) \<Longrightarrow> Q (f (Suc na)) \<and> (f (Suc na), f na) 
        \<in> findnth_LE" for na
  proof(simp add: f, 
      cases "steps (Suc 0, l, r) (findnth n, 0) na", simp add: P)
    fix na a b c
    assume "a \<noteq> Suc (2 * n) \<and> Q ((a, b, c), n)"
    thus  "Q (step (a, b, c) (findnth n, 0), n) \<and> 
        ((step (a, b, c) (findnth n, 0), n), (a, b, c), n) \<in> findnth_LE"
      apply(cases c, case_tac [2] "hd c")
        apply(simp_all add: step.simps findnth_LE_def Q findnth_inv.simps mod_2  lex_pair_def split: if_splits)
         apply(auto simp: mod_ex1 mod_ex2)
      done
  qed
  thus "\<forall>n. \<not> P (f n) \<and> Q (f n) \<longrightarrow>
        Q (f (Suc n)) \<and> (f (Suc n), f n) \<in> findnth_LE" by blast
qed

lemma inv_locate_a_via_crsp[simp]:
  "crsp ly (as, lm) (s, l, r) ires \<Longrightarrow> inv_locate_a (as, lm) (0, l, r) ires"
  apply(auto simp: crsp.simps inv_locate_a.simps at_begin_norm.simps)
  done

lemma findnth_correct: 
  assumes layout: "ly = layout_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
  shows "\<exists> stp l' r'. steps (Suc 0, l, r) (findnth n, 0) stp = (Suc (2 * n), l', r')
              \<and> inv_locate_a (as, lm) (n, l', r') ires"
  using crsp
  apply(cases "n = 0")
   apply(rule_tac x = 0 in exI, auto simp: steps.simps)
  using assms
  apply(drule_tac findnth_correct_pre, auto)
  using findnth_inv.simps by auto

fun inc_inv :: "nat \<Rightarrow> inc_inv_t"
  where
    "inc_inv n (as, lm) (s, l, r) ires =
              (let lm' = abc_lm_s lm n (Suc (abc_lm_v lm n)) in
                if s = 0 then False
                else if s = 1 then 
                   inv_locate_a (as, lm) (n, l, r) ires
                else if s = 2 then 
                   inv_locate_b (as, lm) (n, l, r) ires
                else if s = 3 then 
                   inv_after_write (as, lm') (s, l, r) ires
                else if s = Suc 3 then 
                   inv_after_move (as, lm') (s, l, r) ires
                else if s = Suc 4 then 
                   inv_after_clear (as, lm') (s, l, r) ires
                else if s = Suc (Suc 4) then 
                   inv_on_right_moving (as, lm') (s, l, r) ires
                else if s = Suc (Suc 5) then 
                   inv_on_left_moving (as, lm') (s, l, r) ires
                else if s = Suc (Suc (Suc 5)) then 
                   inv_check_left_moving (as, lm') (s, l, r) ires
                else if s = Suc (Suc (Suc (Suc 5))) then 
                   inv_after_left_moving (as, lm') (s, l, r) ires
                else if s = Suc (Suc (Suc (Suc (Suc 5)))) then 
                   inv_stop (as, lm') (s, l, r) ires
                else False)"


fun abc_inc_stage1 :: "config \<Rightarrow> nat"
  where
    "abc_inc_stage1 (s, l, r) = 
            (if s = 0 then 0
             else if s \<le> 2 then 5
             else if s \<le> 6 then 4
             else if s \<le> 8 then 3
             else if s = 9 then 2
             else 1)"

fun abc_inc_stage2 :: "config \<Rightarrow> nat"
  where
    "abc_inc_stage2 (s, l, r) =
                (if s = 1 then 2
                 else if s = 2 then 1
                 else if s = 3 then length r
                 else if s = 4 then length r
                 else if s = 5 then length r
                 else if s = 6 then 
                                  if r \<noteq> [] then length r
                                  else 1
                 else if s = 7 then length l
                 else if s = 8 then length l
                 else 0)"

fun abc_inc_stage3 :: "config \<Rightarrow>  nat"
  where
    "abc_inc_stage3 (s, l, r) = (
              if s = 4 then 4
              else if s = 5 then 3
              else if s = 6 then 
                   if r \<noteq> [] \<and> hd r = Oc then 2
                   else 1
              else if s = 3 then 0
              else if s = 2 then length r
              else if s = 1 then 
                      if (r \<noteq> [] \<and> hd r = Oc) then 0
                      else 1
              else 10 - s)"


definition inc_measure :: "config \<Rightarrow> nat \<times> nat \<times> nat"
  where
    "inc_measure c = 
    (abc_inc_stage1 c, abc_inc_stage2 c, abc_inc_stage3 c)"

definition lex_triple :: 
  "((nat \<times> (nat \<times> nat)) \<times> (nat \<times> (nat \<times> nat))) set"
  where "lex_triple \<equiv> less_than <*lex*> lex_pair"

definition inc_LE :: "(config \<times> config) set"
  where
    "inc_LE \<equiv> (inv_image lex_triple inc_measure)"

declare inc_inv.simps[simp del]

lemma wf_inc_le[intro]: "wf inc_LE"
  by(auto simp: inc_LE_def lex_triple_def lex_pair_def)

lemma inv_locate_b_2_after_write[simp]:
  assumes "inv_locate_b (as, am) (n, aaa, Bk # xs) ires"
  shows "inv_after_write (as, abc_lm_s am n (Suc (abc_lm_v am n))) (s, aaa, Oc # xs) ires"
proof -
  from assms show ?thesis
    apply(auto simp: in_middle.simps inv_after_write.simps 
        abc_lm_v.simps abc_lm_s.simps inv_locate_b.simps simp del:split_head_repeat)
     apply(rename_tac lm1 lm2 m ml mr rn)
     apply(case_tac [!] mr, auto split: if_splits)
    apply(rename_tac lm1 lm2 m rn)
    apply(rule_tac x = rn in exI, rule_tac x = "Suc m" in exI,
        rule_tac x = "lm1" in exI, simp)
    apply(rule_tac x = "lm2" in exI)
    apply(simp only: Suc_diff_le exp_ind)
    by(subgoal_tac "lm2 = []"; force dest:length_equal)
qed

(*inv: from after_write to after_move*)
lemma inv_after_move_Oc_via_write[simp]: "inv_after_write (as, lm) (x, l, Oc # r) ires
                \<Longrightarrow> inv_after_move (as, lm) (y, Oc # l, r) ires"
  apply(auto simp:inv_after_move.simps inv_after_write.simps split: if_splits)
  done

lemma inv_after_write_Suc[simp]: "inv_after_write (as, abc_lm_s am n (Suc (abc_lm_v am n)
                )) (x, aaa, Bk # xs) ires = False"
  "inv_after_write (as, abc_lm_s am n (Suc (abc_lm_v am n))) 
                        (x, aaa, []) ires = False"
   apply(auto simp: inv_after_write.simps )
  done

(*inv: from after_move to after_clear*)
lemma inv_after_clear_Bk_via_Oc[simp]: "inv_after_move (as, lm) (s, l, Oc # r) ires
                \<Longrightarrow> inv_after_clear (as, lm) (s', l, Bk # r) ires"
  apply(auto simp: inv_after_move.simps inv_after_clear.simps split: if_splits)
  done


lemma inv_after_move_2_inv_on_left_moving[simp]:  
  assumes "inv_after_move (as, lm) (s, l, Bk # r) ires"
  shows "(l = [] \<longrightarrow> 
         inv_on_left_moving (as, lm) (s', [], Bk # Bk # r) ires) \<and>
      (l \<noteq> [] \<longrightarrow> 
         inv_on_left_moving (as, lm) (s', tl l, hd l # Bk # r) ires)"
proof (cases l)
  case (Cons a list)
  from assms Cons show ?thesis
    apply(simp only: inv_after_move.simps inv_on_left_moving.simps)
    apply(rule conjI, force, rule impI, rule disjI1, simp only: inv_on_left_moving_norm.simps)
    apply(erule exE)+
    apply(rename_tac rn m lm1 lm2)
    apply(subgoal_tac "lm2 = []")
     apply(rule_tac x = lm1 in exI, rule_tac x = lm2 in exI,  
        rule_tac x = m in exI, rule_tac x = m in exI, 
        rule_tac x = 1 in exI,  
        rule_tac x = "rn - 1" in exI)
     apply (auto split:if_splits)
       apply(case_tac [1-2] rn, simp_all)
    by(case_tac [!] lm2, simp_all add: tape_of_nl_cons split: if_splits)
next
  case Nil thus ?thesis using assms
    unfolding inv_after_move.simps inv_on_left_moving.simps
    by (auto split:if_splits)
qed


lemma inv_after_move_2_inv_on_left_moving_B[simp]: 
  "inv_after_move (as, lm) (s, l, []) ires
      \<Longrightarrow> (l = [] \<longrightarrow> inv_on_left_moving (as, lm) (s', [], [Bk]) ires) \<and>
          (l \<noteq> [] \<longrightarrow> inv_on_left_moving (as, lm) (s', tl l, [hd l]) ires)"
  apply(simp only: inv_after_move.simps inv_on_left_moving.simps)
  apply(subgoal_tac "l \<noteq> []", rule conjI, simp, rule impI, rule disjI1,
      simp only: inv_on_left_moving_norm.simps)
   apply(erule exE)+
   apply(rename_tac rn m lm1 lm2)
   apply(subgoal_tac "lm2 = []")
    apply(rule_tac x = lm1 in exI, rule_tac x = lm2 in exI,  
      rule_tac x = m in exI, rule_tac x = m in exI, 
      rule_tac x = 1 in exI, rule_tac x = "rn - 1" in exI, force)
   apply(metis append_Cons list.distinct(1) list.exhaust replicate_Suc tape_of_nl_cons)
  apply(metis append_Cons list.distinct(1) replicate_Suc)
  done

lemma inv_after_clear_2_inv_on_right_moving[simp]: 
  "inv_after_clear (as, lm) (x, l, Bk # r) ires
      \<Longrightarrow> inv_on_right_moving (as, lm) (y, Bk # l, r) ires"
  apply(auto simp: inv_after_clear.simps inv_on_right_moving.simps simp del:split_head_repeat)
  apply(rename_tac rn m lm1 lm2)
  apply(subgoal_tac "lm2 \<noteq> []")
   apply(rule_tac x = "lm1 @ [m]" in exI, rule_tac x = "tl lm2" in exI, 
      rule_tac x = "hd lm2" in exI, simp del:split_head_repeat)
   apply(rule_tac x = 0 in exI, rule_tac x = "hd lm2" in exI)
   apply(simp, rule conjI)
    apply(case_tac [!] "lm2::nat list", auto)
    apply(case_tac rn, auto split: if_splits simp: tape_of_nl_cons)
   apply(case_tac [!] rn, simp_all)
  done

(*inv: from on_right_moving to on_right_moving*)
lemma inv_on_right_moving_Oc[simp]: "inv_on_right_moving (as, lm) (x, l, Oc # r) ires
      \<Longrightarrow> inv_on_right_moving (as, lm) (y, Oc # l, r) ires"
  apply(auto simp: inv_on_right_moving.simps)
   apply(rename_tac lm1 lm2 ml mr rn)
   apply(rule_tac x = lm1 in exI, rule_tac x = lm2 in exI, 
      rule_tac x = "ml + mr" in exI, simp)
   apply(rule_tac x = "Suc ml" in exI, 
      rule_tac x = "mr - 1" in exI, simp) 
   apply (metis One_nat_def Suc_pred cell.distinct(1) empty_replicate list.inject
      list.sel(3) neq0_conv self_append_conv2 tl_append2 tl_replicate)
  apply(rule_tac x = lm1 in exI, rule_tac x = "[]" in exI, 
      rule_tac x = "ml + mr" in exI, simp)
  apply(rule_tac x = "Suc ml" in exI, 
      rule_tac x = "mr - 1" in exI)
  apply (auto simp add: Cons_replicate_eq)
  done

lemma inv_on_right_moving_2_inv_on_right_moving[simp]: 
  "inv_on_right_moving (as, lm) (x, l, Bk # r) ires
     \<Longrightarrow> inv_after_write (as, lm) (y, l, Oc # r) ires"
  apply(auto simp: inv_on_right_moving.simps inv_after_write.simps)
  by (metis append.left_neutral append_Cons )

lemma inv_on_right_moving_singleton_Bk[simp]: "inv_on_right_moving (as, lm) (x, l, []) ires\<Longrightarrow> 
             inv_on_right_moving (as, lm) (y, l, [Bk]) ires"
  apply(auto simp: inv_on_right_moving.simps)
  by fastforce

(*inv: from on_left_moving to on_left_moving*)
lemma no_inv_on_left_moving_in_middle_B_Oc[simp]: "inv_on_left_moving_in_middle_B (as, lm) 
               (s, l, Oc # r) ires = False"
  by(auto simp: inv_on_left_moving_in_middle_B.simps )

lemma no_inv_on_left_moving_norm_Bk[simp]: "inv_on_left_moving_norm (as, lm) (s, l, Bk # r) ires 
             = False"
  by(auto simp: inv_on_left_moving_norm.simps)

lemma inv_on_left_moving_in_middle_B_Bk[simp]: 
  "\<lbrakk>inv_on_left_moving_norm (as, lm) (s, l, Oc # r) ires;
    hd l = Bk; l \<noteq> []\<rbrakk> \<Longrightarrow> 
     inv_on_left_moving_in_middle_B (as, lm) (s, tl l, Bk # Oc # r) ires"
  apply(cases l, simp, simp)
  apply(simp only: inv_on_left_moving_norm.simps 
      inv_on_left_moving_in_middle_B.simps)
  apply(erule_tac exE)+ unfolding tape_of_nl_cons
  apply(rename_tac a list lm1 lm2 m ml mr rn)
  apply(rule_tac x = lm1 in exI, rule_tac x = "m # lm2" in exI, auto)
   apply(auto simp: tape_of_nl_cons split: if_splits)
  done

lemma inv_on_left_moving_norm_Oc_Oc[simp]: "\<lbrakk>inv_on_left_moving_norm (as, lm) (s, l, Oc # r) ires; 
                hd l = Oc; l \<noteq> []\<rbrakk>
            \<Longrightarrow> inv_on_left_moving_norm (as, lm) 
                                        (s, tl l, Oc # Oc # r) ires"
  apply(simp only: inv_on_left_moving_norm.simps)
  apply(erule exE)+
  apply(rename_tac lm1 lm2 m ml mr rn)
  apply(rule_tac x = lm1 in exI, rule_tac x = lm2 in exI, 
      rule_tac x = m in exI, rule_tac x = "ml - 1" in exI,
      rule_tac x = "Suc mr" in exI, rule_tac x = rn in exI, simp)
  apply(case_tac ml, auto simp: split: if_splits)
  done

lemma inv_on_left_moving_in_middle_B_Bk_Oc[simp]: "inv_on_left_moving_norm (as, lm) (s, [], Oc # r) ires
     \<Longrightarrow> inv_on_left_moving_in_middle_B (as, lm) (s, [], Bk # Oc # r) ires"
  by(auto simp: inv_on_left_moving_norm.simps 
      inv_on_left_moving_in_middle_B.simps split: if_splits)

lemma inv_on_left_moving_Oc_cases[simp]:"inv_on_left_moving (as, lm) (s, l, Oc # r) ires
    \<Longrightarrow> (l = [] \<longrightarrow> inv_on_left_moving (as, lm) (s, [], Bk # Oc # r) ires)
 \<and>  (l \<noteq> [] \<longrightarrow> inv_on_left_moving (as, lm) (s, tl l, hd l # Oc # r) ires)"
  apply(simp add: inv_on_left_moving.simps)
  apply(cases "l \<noteq> []", rule conjI, simp, simp)
   apply(cases "hd l", simp, simp, simp)
  done

lemma from_on_left_moving_to_check_left_moving[simp]: "inv_on_left_moving_in_middle_B (as, lm) 
                                      (s, Bk # list, Bk # r) ires
          \<Longrightarrow> inv_check_left_moving_on_leftmost (as, lm) 
                                      (s', list, Bk # Bk # r) ires"
  apply(simp only: inv_on_left_moving_in_middle_B.simps inv_check_left_moving_on_leftmost.simps)
  apply(erule_tac exE)+
  apply(rename_tac lm1 lm2 rn)
  apply(case_tac "rev lm1", simp_all)
  apply(case_tac "tl (rev lm1)", simp_all add: tape_of_nat_def tape_of_list_def)
  done

lemma inv_check_left_moving_in_middle_no_Bk[simp]:
  "inv_check_left_moving_in_middle (as, lm) (s, l, Bk # r) ires= False"
  by(auto simp: inv_check_left_moving_in_middle.simps )

lemma inv_check_left_moving_on_leftmost_Bk_Bk[simp]: 
  "inv_on_left_moving_in_middle_B (as, lm) (s, [], Bk # r) ires\<Longrightarrow> 
  inv_check_left_moving_on_leftmost (as, lm) (s', [], Bk # Bk # r) ires"
  apply(auto simp: inv_on_left_moving_in_middle_B.simps 
      inv_check_left_moving_on_leftmost.simps split: if_splits)
  done

lemma inv_check_left_moving_on_leftmost_no_Oc[simp]: "inv_check_left_moving_on_leftmost (as, lm) 
                                       (s, list, Oc # r) ires= False"
  by(auto simp: inv_check_left_moving_on_leftmost.simps split: if_splits)

lemma inv_check_left_moving_in_middle_Oc_Bk[simp]: "inv_on_left_moving_in_middle_B (as, lm) 
                                         (s, Oc # list, Bk # r) ires
 \<Longrightarrow> inv_check_left_moving_in_middle (as, lm) (s', list, Oc # Bk # r) ires"
  apply(auto simp: inv_on_left_moving_in_middle_B.simps 
      inv_check_left_moving_in_middle.simps  split: if_splits)
  done

lemma inv_on_left_moving_2_check_left_moving[simp]:
  "inv_on_left_moving (as, lm) (s, l, Bk # r) ires
 \<Longrightarrow> (l = [] \<longrightarrow> inv_check_left_moving (as, lm) (s', [], Bk # Bk # r) ires)
 \<and> (l \<noteq> [] \<longrightarrow> 
      inv_check_left_moving (as, lm) (s', tl l, hd l # Bk # r) ires)"
  by (cases l;cases "hd l", auto simp: inv_on_left_moving.simps inv_check_left_moving.simps)

lemma inv_on_left_moving_norm_no_empty[simp]: "inv_on_left_moving_norm (as, lm) (s, l, []) ires = False"
  apply(auto simp: inv_on_left_moving_norm.simps)
  done

lemma inv_on_left_moving_no_empty[simp]: "inv_on_left_moving (as, lm) (s, l, []) ires = False"
  apply(simp add: inv_on_left_moving.simps)
  apply(simp add: inv_on_left_moving_in_middle_B.simps)
  done

lemma 
  inv_check_left_moving_in_middle_2_on_left_moving_in_middle_B[simp]:
  assumes "inv_check_left_moving_in_middle (as, lm) (s, Bk # list, Oc # r) ires"
  shows "inv_on_left_moving_in_middle_B (as, lm) (s', list, Bk # Oc # r) ires"
  using assms
  apply(simp only: inv_check_left_moving_in_middle.simps 
      inv_on_left_moving_in_middle_B.simps)
  apply(erule_tac exE)+
  apply(rename_tac lm1 lm2 r' rn)
  apply(rule_tac x = "rev (tl (rev lm1))" in exI, 
      rule_tac x = "[hd (rev lm1)] @ lm2" in exI, auto)
       apply(case_tac [!] "rev lm1",case_tac [!] "tl (rev lm1)")
                      apply(simp_all add: tape_of_nat_def tape_of_list_def tape_of_nat_list.simps)
   apply(case_tac [1] lm2, auto simp:tape_of_nat_def)
  apply(case_tac lm2, auto simp:tape_of_nat_def)
  done

lemma inv_check_left_moving_in_middle_Bk_Oc[simp]: 
  "inv_check_left_moving_in_middle (as, lm) (s, [], Oc # r) ires\<Longrightarrow>
     inv_check_left_moving_in_middle (as, lm) (s', [Bk], Oc # r) ires"
  apply(auto simp: inv_check_left_moving_in_middle.simps )
  done

lemma inv_on_left_moving_norm_Oc_Oc_via_middle[simp]: "inv_check_left_moving_in_middle (as, lm) 
                       (s, Oc # list, Oc # r) ires
   \<Longrightarrow> inv_on_left_moving_norm (as, lm) (s', list, Oc # Oc # r) ires"
  apply(auto simp: inv_check_left_moving_in_middle.simps 
      inv_on_left_moving_norm.simps)
  apply(rename_tac lm1 lm2 rn)
  apply(rule_tac x = "rev (tl (rev lm1))" in exI, 
      rule_tac x = lm2 in exI, rule_tac x = "hd (rev lm1)" in exI)
  apply(rule_tac conjI)
   apply(case_tac "rev lm1", simp, simp)
  apply(rule_tac x = "hd (rev lm1) - 1" in exI, auto)
   apply(rule_tac [!] x = "Suc (Suc 0)" in exI, simp)
   apply(case_tac [!] "rev lm1", simp_all)
   apply(case_tac [!] "last lm1", simp_all add: tape_of_nl_cons split: if_splits)
  done

lemma inv_check_left_moving_Oc_cases[simp]: "inv_check_left_moving (as, lm) (s, l, Oc # r) ires
\<Longrightarrow> (l = [] \<longrightarrow> inv_on_left_moving (as, lm) (s', [], Bk # Oc # r) ires) \<and>
   (l \<noteq> [] \<longrightarrow> inv_on_left_moving (as, lm) (s', tl l, hd l # Oc # r) ires)"
  apply(cases l;cases "hd l", auto simp: inv_check_left_moving.simps inv_on_left_moving.simps)
  done

(*inv: check_left_moving to after_left_moving*)
lemma inv_after_left_moving_Bk_via_check[simp]: "inv_check_left_moving (as, lm) (s, l, Bk # r) ires
                \<Longrightarrow> inv_after_left_moving (as, lm) (s', Bk # l, r) ires"
  apply(auto simp: inv_check_left_moving.simps 
      inv_check_left_moving_on_leftmost.simps inv_after_left_moving.simps)
  done


lemma inv_after_left_moving_Bk_empty_via_check[simp]:"inv_check_left_moving (as, lm) (s, l, []) ires
      \<Longrightarrow> inv_after_left_moving (as, lm) (s', Bk # l, []) ires"
  by(simp add: inv_check_left_moving.simps  
      inv_check_left_moving_in_middle.simps 
      inv_check_left_moving_on_leftmost.simps)

(*inv: after_left_moving to inv_stop*)
lemma inv_stop_Bk_move[simp]: "inv_after_left_moving (as, lm) (s, l, Bk # r) ires
       \<Longrightarrow> inv_stop (as, lm) (s', Bk # l, r) ires"
  apply(auto simp: inv_after_left_moving.simps inv_stop.simps)
  done

lemma inv_stop_Bk_empty[simp]: "inv_after_left_moving (as, lm) (s, l, []) ires
             \<Longrightarrow> inv_stop (as, lm) (s', Bk # l, []) ires"
  by(auto simp: inv_after_left_moving.simps)

(*inv: stop to stop*)
lemma inv_stop_indep_fst[simp]: "inv_stop (as, lm) (x, l, r) ires \<Longrightarrow> 
               inv_stop (as, lm) (y, l, r) ires"
  apply(simp add: inv_stop.simps)
  done

lemma inv_after_clear_no_Oc[simp]: "inv_after_clear (as, lm) (s, aaa, Oc # xs) ires= False"
  apply(auto simp: inv_after_clear.simps )
  done

lemma inv_after_left_moving_no_Oc[simp]: 
  "inv_after_left_moving (as, lm) (s, aaa, Oc # xs) ires = False"
  by(auto simp: inv_after_left_moving.simps  )

lemma inv_after_clear_Suc_nonempty[simp]:
  "inv_after_clear (as, abc_lm_s lm n (Suc (abc_lm_v lm n))) (s, b, []) ires = False"
  apply(auto simp: inv_after_clear.simps)
  done

lemma inv_on_left_moving_Suc_nonempty[simp]: "inv_on_left_moving (as, abc_lm_s lm n (Suc (abc_lm_v lm n))) 
           (s, b, Oc # list) ires \<Longrightarrow> b \<noteq> []"
  apply(auto simp: inv_on_left_moving.simps inv_on_left_moving_norm.simps split: if_splits)
  done

lemma inv_check_left_moving_Suc_nonempty[simp]:
  "inv_check_left_moving (as, abc_lm_s lm n (Suc (abc_lm_v lm n))) (s, b, Oc # list) ires \<Longrightarrow> b \<noteq> []"
  apply(auto simp: inv_check_left_moving.simps inv_check_left_moving_in_middle.simps split: if_splits)
  done

lemma tinc_correct_pre:
  assumes layout: "ly = layout_of ap"
    and inv_start: "inv_locate_a (as, lm) (n, l, r) ires"
    and lm': "lm' = abc_lm_s lm n (Suc (abc_lm_v lm n))"
    and f: "f = steps (Suc 0, l, r) (tinc_b, 0)"
    and P: "P = (\<lambda> (s, l, r). s = 10)"
    and Q: "Q = (\<lambda> (s, l, r). inc_inv n (as, lm) (s, l, r) ires)" 
  shows "\<exists> stp. P (f stp) \<and> Q (f stp)"
proof(rule_tac LE = inc_LE in halt_lemma2)
  show "wf inc_LE" by(auto)
next
  show "Q (f 0)"
    using inv_start
    apply(simp add: f P Q steps.simps inc_inv.simps)
    done
next
  show "\<not> P (f 0)"
    apply(simp add: f P steps.simps)
    done
next
  have "\<not> P (f n) \<and> Q (f n) \<Longrightarrow> Q (f (Suc n)) \<and> (f (Suc n), f n) 
        \<in> inc_LE" for n
  proof(simp add: f, 
      cases "steps (Suc 0, l, r) (tinc_b, 0) n", simp add: P)
    fix n a b c
    assume "a \<noteq> 10 \<and> Q (a, b, c)"
    thus  "Q (step (a, b, c) (tinc_b, 0)) \<and> (step (a, b, c) (tinc_b, 0), a, b, c) \<in> inc_LE"
      apply(simp add:Q)
      apply(simp add: inc_inv.simps)
      apply(cases c; cases "hd c")
         apply(auto simp: Let_def step.simps tinc_b_def split: if_splits) (* ~ 12 sec *)
                          apply(simp_all add: inc_inv.simps inc_LE_def lex_triple_def lex_pair_def
          inc_measure_def numeral)         
      done
  qed
  thus "\<forall>n. \<not> P (f n) \<and> Q (f n) \<longrightarrow> Q (f (Suc n)) \<and> (f (Suc n), f n) \<in> inc_LE" by blast
qed

lemma tinc_correct: 
  assumes layout: "ly = layout_of ap"
    and inv_start: "inv_locate_a (as, lm) (n, l, r) ires"
    and lm': "lm' = abc_lm_s lm n (Suc (abc_lm_v lm n))"
  shows "\<exists> stp l' r'. steps (Suc 0, l, r) (tinc_b, 0) stp = (10, l', r')
              \<and> inv_stop (as, lm') (10, l', r') ires"
  using assms
  apply(drule_tac tinc_correct_pre, auto)
  apply(rule_tac x = stp in exI, simp)
  apply(simp add: inc_inv.simps)
  done

lemma is_even_4[simp]: "(4::nat) * n mod 2 = 0"
  apply(arith)
  done

lemma crsp_step_inc_pre:
  assumes layout: "ly = layout_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
    and aexec: "abc_step_l (as, lm) (Some (Inc n)) = (asa, lma)"
  shows "\<exists> stp k. steps (Suc 0, l, r) (findnth n @ shift tinc_b (2 * n), 0) stp 
        = (2*n + 10, Bk # Bk # ires, <lma> @ Bk\<up>k) \<and> stp > 0"
proof -
  have "\<exists> stp l' r'. steps (Suc 0, l, r) (findnth n, 0) stp = (Suc (2 * n), l', r')
    \<and> inv_locate_a (as, lm) (n, l', r') ires"
    using assms
    apply(rule_tac findnth_correct, simp_all add: crsp layout)
    done
  from this obtain stp l' r' where a:
    "steps (Suc 0, l, r) (findnth n, 0) stp = (Suc (2 * n), l', r')
    \<and> inv_locate_a (as, lm) (n, l', r') ires" by blast
  moreover have
    "\<exists> stp la ra. steps (Suc 0, l', r') (tinc_b, 0) stp = (10, la, ra)
                        \<and> inv_stop (as, lma) (10, la, ra) ires"
    using assms a
  proof(rule_tac lm' = lma and n = n and lm = lm and ly = ly and ap = ap in tinc_correct,
      simp, simp)
    show "lma = abc_lm_s lm n (Suc (abc_lm_v lm n))"
      using aexec
      apply(simp add: abc_step_l.simps)
      done
  qed
  from this obtain stpa la ra where b:
    "steps (Suc 0, l', r') (tinc_b, 0) stpa = (10, la, ra)
    \<and> inv_stop (as, lma) (10, la, ra) ires" by blast
  from a b show "\<exists>stp k. steps (Suc 0, l, r) (findnth n @ shift tinc_b (2 * n), 0) stp
    = (2 * n + 10, Bk # Bk # ires, <lma> @ Bk \<up> k) \<and> stp > 0"
    apply(rule_tac x = "stp + stpa" in exI)
    using tm_append_steps[of "Suc 0" l r "findnth n" stp l' r' tinc_b stpa 10 la ra "length (findnth n) div 2"]
    apply(simp add: length_findnth inv_stop.simps)
    apply(cases stpa, simp_all add: steps.simps)
    done
qed 

lemma crsp_step_inc:
  assumes layout: "ly = layout_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
    and fetch: "abc_fetch as ap = Some (Inc n)"
  shows "\<exists>stp > 0. crsp ly (abc_step_l (as, lm) (Some (Inc n)))
  (steps (s, l, r) (ci ly (start_of ly as) (Inc n), start_of ly as - Suc 0) stp) ires"
proof(cases "(abc_step_l (as, lm) (Some (Inc n)))")
  fix a b
  assume aexec: "abc_step_l (as, lm) (Some (Inc n)) = (a, b)"
  then have "\<exists> stp k. steps (Suc 0, l, r) (findnth n @ shift tinc_b (2 * n), 0) stp 
        = (2*n + 10, Bk # Bk # ires, <b> @ Bk\<up>k) \<and> stp > 0"
    using assms
    apply(rule_tac crsp_step_inc_pre, simp_all)
    done
  thus "?thesis"
    using assms aexec
    apply(erule_tac exE)
    apply(erule_tac exE)
    apply(erule_tac conjE)
    apply(rename_tac stp k)
    apply(rule_tac x = stp in exI, simp add: ci.simps tm_shift_eq_steps)
    apply(drule_tac off = "(start_of (layout_of ap) as - Suc 0)" in tm_shift_eq_steps)
     apply(auto simp: crsp.simps abc_step_l.simps fetch start_of_Suc1)
    done
qed

subsection\<open>Crsp of Dec n e\<close>

type_synonym dec_inv_t = "(nat * nat list) \<Rightarrow> config \<Rightarrow> cell list \<Rightarrow>  bool"

fun dec_first_on_right_moving :: "nat \<Rightarrow> dec_inv_t"
  where
    "dec_first_on_right_moving n (as, lm) (s, l, r) ires = 
               (\<exists> lm1 lm2 m ml mr rn. lm = lm1 @ [m] @ lm2 \<and> 
         ml + mr = Suc m \<and> length lm1 = n \<and> ml > 0 \<and> m > 0 \<and>
             (if lm1 = [] then l = Oc\<up>ml @ Bk # Bk # ires
                          else  l = Oc\<up>ml @ [Bk] @ <rev lm1> @ Bk # Bk # ires) \<and> 
    ((r = Oc\<up>mr @ [Bk] @ <lm2> @ Bk\<up>rn) \<or> (r = Oc\<up>mr \<and> lm2 = [])))"

fun dec_on_right_moving :: "dec_inv_t"
  where
    "dec_on_right_moving (as, lm) (s, l, r) ires =  
   (\<exists> lm1 lm2 m ml mr rn. lm = lm1 @ [m] @ lm2 \<and> 
                             ml + mr = Suc (Suc m) \<and>
   (if lm1 = [] then l = Oc\<up>ml@ Bk # Bk # ires
                else  l = Oc\<up>ml @ [Bk] @ <rev lm1> @ Bk # Bk # ires) \<and> 
   ((r = Oc\<up>mr @ [Bk] @ <lm2> @ Bk\<up>rn) \<or> (r = Oc\<up>mr \<and> lm2 = [])))"

fun dec_after_clear :: "dec_inv_t"
  where
    "dec_after_clear (as, lm) (s, l, r) ires = 
              (\<exists> lm1 lm2 m ml mr rn. lm = lm1 @ [m] @ lm2 \<and> 
                ml + mr = Suc m \<and> ml = Suc m \<and> r \<noteq> [] \<and> r \<noteq> [] \<and>
               (if lm1 = [] then l = Oc\<up>ml@ Bk # Bk # ires
                            else l = Oc\<up>ml @ [Bk] @ <rev lm1> @ Bk # Bk # ires) \<and> 
               (tl r = Bk # <lm2> @ Bk\<up>rn \<or> tl r = [] \<and> lm2 = []))"

fun dec_after_write :: "dec_inv_t"
  where
    "dec_after_write (as, lm) (s, l, r) ires = 
         (\<exists> lm1 lm2 m ml mr rn. lm = lm1 @ [m] @ lm2 \<and> 
       ml + mr = Suc m \<and> ml = Suc m \<and> lm2 \<noteq> [] \<and>
       (if lm1 = [] then l = Bk # Oc\<up>ml @ Bk # Bk # ires
                    else l = Bk # Oc\<up>ml @ [Bk] @ <rev lm1> @ Bk # Bk # ires) \<and> 
       tl r = <lm2> @ Bk\<up>rn)"

fun dec_right_move :: "dec_inv_t"
  where
    "dec_right_move (as, lm) (s, l, r) ires = 
        (\<exists> lm1 lm2 m ml mr rn. lm = lm1 @ [m] @ lm2 
            \<and> ml = Suc m \<and> mr = (0::nat) \<and> 
              (if lm1 = [] then l = Bk # Oc\<up>ml @ Bk # Bk # ires
                          else l = Bk # Oc\<up>ml @ [Bk] @ <rev lm1> @ Bk # Bk # ires) 
           \<and> (r = Bk # <lm2> @ Bk\<up>rn \<or> r = [] \<and> lm2 = []))"

fun dec_check_right_move :: "dec_inv_t"
  where
    "dec_check_right_move (as, lm) (s, l, r) ires = 
        (\<exists> lm1 lm2 m ml mr rn. lm = lm1 @ [m] @ lm2 \<and> 
           ml = Suc m \<and> mr = (0::nat) \<and> 
           (if lm1 = [] then l = Bk # Bk # Oc\<up>ml @ Bk # Bk # ires
                       else l = Bk # Bk # Oc\<up>ml @ [Bk] @ <rev lm1> @ Bk # Bk # ires) \<and> 
           r = <lm2> @ Bk\<up>rn)"

fun dec_left_move :: "dec_inv_t"
  where
    "dec_left_move (as, lm) (s, l, r) ires = 
    (\<exists> lm1 m rn. (lm::nat list) = lm1 @ [m::nat] \<and>   
    rn > 0 \<and> 
   (if lm1 = [] then l = Bk # Oc\<up>Suc m @ Bk # Bk # ires
    else l = Bk # Oc\<up>Suc m @ Bk # <rev lm1> @ Bk # Bk # ires) \<and> r = Bk\<up>rn)"

declare
  dec_on_right_moving.simps[simp del] dec_after_clear.simps[simp del] 
  dec_after_write.simps[simp del] dec_left_move.simps[simp del] 
  dec_check_right_move.simps[simp del] dec_right_move.simps[simp del] 
  dec_first_on_right_moving.simps[simp del]

fun inv_locate_n_b :: "inc_inv_t"
  where
    "inv_locate_n_b (as, lm) (s, l, r) ires= 
    (\<exists> lm1 lm2 tn m ml mr rn. lm @ 0\<up>tn = lm1 @ [m] @ lm2 \<and> 
     length lm1 = s \<and> m + 1 = ml + mr \<and> 
     ml = 1 \<and> tn = s + 1 - length lm \<and>
     (if lm1 = [] then l = Oc\<up>ml @ Bk # Bk # ires
      else l = Oc\<up>ml @ Bk # <rev lm1> @ Bk # Bk # ires) \<and> 
     (r = Oc\<up>mr @ [Bk] @ <lm2>@ Bk\<up>rn \<or> (lm2 = [] \<and> r = Oc\<up>mr))
  )"

fun dec_inv_1 :: "layout \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dec_inv_t"
  where
    "dec_inv_1 ly n e (as, am) (s, l, r) ires = 
           (let ss = start_of ly as in
            let am' = abc_lm_s am n (abc_lm_v am n - Suc 0) in
            let am'' = abc_lm_s am n (abc_lm_v am n) in
              if s = start_of ly e then inv_stop (as, am'') (s, l, r) ires
              else if s = ss then False
              else if s = ss + 2 * n + 1 then 
                  inv_locate_b (as, am) (n, l, r) ires
              else if s = ss + 2 * n + 13 then 
                  inv_on_left_moving (as, am'') (s, l, r) ires
              else if s = ss + 2 * n + 14 then 
                  inv_check_left_moving (as, am'') (s, l, r) ires
              else if s = ss + 2 * n + 15 then 
                  inv_after_left_moving (as, am'') (s, l, r) ires
              else False)"

declare fetch.simps[simp del]


lemma x_plus_helpers:
  "x + 4 = Suc (x + 3)"
  "x + 5 = Suc (x + 4)"
  "x + 6 = Suc (x + 5)"
  "x + 7 = Suc (x + 6)"
  "x + 8 = Suc (x + 7)"
  "x + 9 = Suc (x + 8)"
  "x + 10 = Suc (x + 9)"
  "x + 11 = Suc (x + 10)"
  "x + 12 = Suc (x + 11)"
  "x + 13 = Suc (x + 12)"
  "14 + x = Suc (x + 13)"
  "15 + x = Suc (x + 14)"
  "16 + x = Suc (x + 15)"
  by auto

lemma fetch_Dec[simp]: 
  "fetch (ci ly (start_of ly as) (Dec n e)) (Suc (2 * n)) Bk = (W1,  start_of ly as + 2 *n)"
  "fetch (ci ly (start_of ly as) (Dec n e)) (Suc (2 * n)) Oc = (R,  Suc (start_of ly as) + 2 *n)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (Suc (Suc (2 * n))) Oc
     = (R, start_of ly as + 2*n + 2)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (Suc (Suc (2 * n))) Bk
     = (L, start_of ly as + 2*n + 13)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (Suc (Suc (Suc (2 * n)))) Oc
     = (R, start_of ly as + 2*n + 2)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (Suc (Suc (Suc (2 * n)))) Bk
     = (L, start_of ly as + 2*n + 3)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 4) Oc = (W0, start_of ly as + 2*n + 3)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 4) Bk = (R, start_of ly as + 2*n + 4)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 5) Bk = (R, start_of ly as + 2*n + 5)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 6) Bk = (L, start_of ly as + 2*n + 6)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 6) Oc = (L, start_of ly as + 2*n + 7)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 7) Bk = (L, start_of ly as + 2*n + 10)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 8) Bk = (W1, start_of ly as + 2*n + 7)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 8) Oc = (R, start_of ly as + 2*n + 8)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 9) Bk = (L, start_of ly as + 2*n + 9)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 9) Oc = (R, start_of ly as + 2*n + 8)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 10) Bk = (R, start_of ly as + 2*n + 4)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 10) Oc = (W0, start_of ly as + 2*n + 9)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 11) Oc = (L, start_of ly as + 2*n + 10)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 11) Bk = (L, start_of ly as + 2*n + 11)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 12) Oc = (L, start_of ly as + 2*n + 10)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 12) Bk = (R, start_of ly as + 2*n + 12)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (2 * n + 13) Bk = (R, start_of ly as + 2*n + 16)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (14 + 2 * n) Oc = (L, start_of ly as + 2*n + 13)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (14 + 2 * n) Bk = (L, start_of ly as + 2*n + 14)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (15 + 2 * n) Oc = (L, start_of ly as + 2*n + 13)"
  "fetch (ci (ly) (start_of ly as) (Dec n e)) (15 + 2 * n) Bk = (R, start_of ly as + 2*n + 15)"
  "fetch (ci (ly) (start_of (ly) as) (Dec n e)) (16 + 2 * n) Bk = (R, start_of (ly) e)"
  unfolding x_plus_helpers fetch.simps
  by(auto simp: ci.simps shift.simps nth_append tdec_b_def length_findnth adjust.simps)

lemma steps_start_of_invb_inv_locate_a1[simp]: 
  "\<lbrakk>r = [] \<or> hd r = Bk; inv_locate_a (as, lm) (n, l, r) ires\<rbrakk>
    \<Longrightarrow> \<exists>stp la ra.
  steps (start_of ly as + 2 * n, l, r) (ci ly (start_of ly as) (Dec n e), 
  start_of ly as - Suc 0) stp = (Suc (start_of ly as + 2 * n), la, ra) \<and>
  inv_locate_b (as, lm) (n, la, ra) ires"
  apply(rule_tac x = "Suc (Suc 0)" in exI)
  apply(auto simp: steps.simps step.simps length_ci_dec)
  apply(cases r, simp_all)
  done

lemma steps_start_of_invb_inv_locate_a2[simp]: 
  "\<lbrakk>inv_locate_a (as, lm) (n, l, r) ires; r \<noteq> [] \<and> hd r \<noteq> Bk\<rbrakk>
    \<Longrightarrow> \<exists>stp la ra.
  steps (start_of ly as + 2 * n, l, r) (ci ly (start_of ly as) (Dec n e), 
  start_of ly as - Suc 0) stp = (Suc (start_of ly as + 2 * n), la, ra) \<and>
  inv_locate_b (as, lm) (n, la, ra) ires"
  apply(rule_tac x = "(Suc 0)" in exI, cases "hd r", simp_all)
  apply(auto simp: steps.simps step.simps length_ci_dec)
  apply(cases r, simp_all)
  done

fun abc_dec_1_stage1:: "config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "abc_dec_1_stage1 (s, l, r) ss n = 
       (if s > ss \<and> s \<le> ss + 2*n + 1 then 4
        else if s = ss + 2 * n + 13 \<or> s = ss + 2*n + 14 then 3
        else if s = ss + 2*n + 15 then 2
        else 0)"

fun abc_dec_1_stage2:: "config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "abc_dec_1_stage2 (s, l, r) ss n = 
       (if s \<le> ss + 2 * n + 1 then (ss + 2 * n + 16 - s)
        else if s = ss + 2*n + 13 then length l
        else if s = ss + 2*n + 14 then length l
        else 0)"

fun abc_dec_1_stage3 :: "config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "abc_dec_1_stage3 (s, l, r) ss n  = 
        (if s \<le> ss + 2*n + 1 then 
             if (s - ss) mod 2 = 0 then 
                         if r \<noteq> [] \<and> hd r = Oc then 0 else 1  
                         else length r
         else if s = ss + 2 * n + 13 then 
             if r \<noteq> [] \<and> hd r = Oc then 2 
             else 1
         else if s = ss + 2 * n + 14 then 
             if r \<noteq> [] \<and> hd r = Oc then 3 else 0 
         else 0)"

fun abc_dec_1_measure :: "(config \<times> nat \<times> nat) \<Rightarrow> (nat \<times> nat \<times> nat)"
  where
    "abc_dec_1_measure (c, ss, n) = (abc_dec_1_stage1 c ss n, 
                   abc_dec_1_stage2 c ss n, abc_dec_1_stage3 c ss n)"

definition abc_dec_1_LE ::
  "((config \<times> nat \<times>
  nat) \<times> (config \<times> nat \<times> nat)) set"
  where "abc_dec_1_LE \<equiv> (inv_image lex_triple abc_dec_1_measure)"

lemma wf_dec_le: "wf abc_dec_1_LE"
  by(auto intro:wf_inv_image simp:abc_dec_1_LE_def lex_triple_def lex_pair_def)

lemma startof_Suc2:
  "abc_fetch as ap = Some (Dec n e) \<Longrightarrow> 
        start_of (layout_of ap) (Suc as) = 
            start_of (layout_of ap) as + 2 * n + 16"
  apply(auto simp: start_of.simps layout_of.simps  
      length_of.simps abc_fetch.simps 
      take_Suc_conv_app_nth split: if_splits)
  done

lemma start_of_less_2: 
  "start_of ly e \<le> start_of ly (Suc e)"
  apply(cases "e < length ly")
   apply(auto simp: start_of.simps take_Suc take_Suc_conv_app_nth)
  done

lemma start_of_less_1: "start_of ly e \<le> start_of ly (e + d)"
proof(induct d)
  case 0 thus "?case" by simp
next
  case (Suc d)
  have "start_of ly e \<le> start_of ly (e + d)"  by fact
  moreover have "start_of ly (e + d) \<le> start_of ly (Suc (e + d))"
    by(rule_tac start_of_less_2)
  ultimately show"?case"
    by(simp)
qed

lemma start_of_less: 
  assumes "e < as"
  shows "start_of ly e \<le> start_of ly as"
proof -
  obtain d where " as = e + d"
    using assms by (metis less_imp_add_positive)
  thus "?thesis"
    by(simp add: start_of_less_1)
qed

lemma start_of_ge: 
  assumes fetch: "abc_fetch as ap = Some (Dec n e)"
    and layout: "ly = layout_of ap"
    and great: "e > as"
  shows "start_of ly e \<ge> start_of ly as + 2*n + 16"
proof(cases "e = Suc as")
  case True
  have "e = Suc as" by fact
  moreover hence "start_of ly (Suc as) = start_of ly as + 2*n + 16"
    using layout fetch
    by(simp add: startof_Suc2)
  ultimately show "?thesis" by (simp)
next
  case False
  have "e \<noteq> Suc as" by fact
  then have "e > Suc as" using great by arith
  then have "start_of ly (Suc as) \<le> start_of ly e"
    by(simp add: start_of_less)
  moreover have "start_of ly (Suc as) = start_of ly as + 2*n + 16"
    using layout fetch
    by(simp add: startof_Suc2)
  ultimately show "?thesis"
    by arith
qed

declare dec_inv_1.simps[simp del]

lemma start_of_ineq1[simp]: 
  "\<lbrakk>abc_fetch as aprog = Some (Dec n e); ly = layout_of aprog\<rbrakk>
   \<Longrightarrow> (start_of ly e \<noteq> Suc (start_of ly as + 2 * n) \<and>
        start_of ly e \<noteq> Suc (Suc (start_of ly as + 2 * n)) \<and>  
        start_of ly e \<noteq> start_of ly as + 2 * n + 3 \<and> 
        start_of ly e \<noteq> start_of ly as + 2 * n + 4 \<and>
        start_of ly e \<noteq> start_of ly as + 2 * n + 5 \<and> 
        start_of ly e \<noteq> start_of ly as + 2 * n + 6 \<and> 
        start_of ly e \<noteq> start_of ly as + 2 * n + 7 \<and>
        start_of ly e \<noteq> start_of ly as + 2 * n + 8 \<and> 
        start_of ly e \<noteq> start_of ly as + 2 * n + 9 \<and> 
        start_of ly e \<noteq> start_of ly as + 2 * n + 10 \<and>
        start_of ly e \<noteq> start_of ly as + 2 * n + 11 \<and> 
        start_of ly e \<noteq> start_of ly as + 2 * n + 12 \<and> 
        start_of ly e \<noteq> start_of ly as + 2 * n + 13 \<and>
        start_of ly e \<noteq> start_of ly as + 2 * n + 14 \<and> 
        start_of ly e \<noteq> start_of ly as + 2 * n + 15)"
  using start_of_ge[of as aprog n e ly] start_of_less[of e as ly]
  apply(cases "e < as", simp)
  apply(cases "e = as", simp, simp)
  done

lemma start_of_ineq2[simp]: "\<lbrakk>abc_fetch as aprog = Some (Dec n e); ly = layout_of aprog\<rbrakk>
      \<Longrightarrow> (Suc (start_of ly as + 2 * n) \<noteq> start_of ly e \<and>
          Suc (Suc (start_of ly as + 2 * n)) \<noteq> start_of ly e \<and> 
          start_of ly as + 2 * n + 3 \<noteq> start_of ly e \<and> 
          start_of ly as + 2 * n + 4 \<noteq> start_of ly e \<and>
          start_of ly as + 2 * n + 5 \<noteq>start_of ly e \<and> 
          start_of ly as + 2 * n + 6 \<noteq> start_of ly e \<and>
          start_of ly as + 2 * n + 7 \<noteq> start_of ly e \<and> 
          start_of ly as + 2 * n + 8 \<noteq> start_of ly e \<and> 
          start_of ly as + 2 * n + 9 \<noteq> start_of ly e \<and> 
          start_of ly as + 2 * n + 10 \<noteq> start_of ly e \<and>
          start_of ly as + 2 * n + 11 \<noteq> start_of ly e \<and> 
          start_of ly as + 2 * n + 12 \<noteq> start_of ly e \<and> 
          start_of ly as + 2 * n + 13 \<noteq> start_of ly e \<and> 
          start_of ly as + 2 * n + 14 \<noteq> start_of ly e \<and> 
          start_of ly as + 2 * n + 15 \<noteq> start_of ly e)"
  using start_of_ge[of as aprog n e ly] start_of_less[of e as ly]
  apply(cases "e < as", simp, simp)
  apply(cases "e = as", simp, simp)
  done

lemma inv_locate_b_nonempty[simp]: "inv_locate_b (as, lm) (n, [], []) ires = False"
  apply(auto simp: inv_locate_b.simps in_middle.simps split: if_splits)
  done

lemma inv_locate_b_no_Bk[simp]: "inv_locate_b (as, lm) (n, [], Bk # list) ires = False"
  apply(auto simp: inv_locate_b.simps in_middle.simps split: if_splits)
  done

lemma dec_first_on_right_moving_Oc[simp]: 
  "\<lbrakk>dec_first_on_right_moving n (as, am) (s, aaa, Oc # xs) ires\<rbrakk>
   \<Longrightarrow> dec_first_on_right_moving n (as, am) (s', Oc # aaa, xs) ires"
  apply(simp only: dec_first_on_right_moving.simps)
  apply(erule exE)+
  apply(rename_tac lm1 lm2 m ml mr rn)
  apply(rule_tac x = lm1 in exI, rule_tac x = lm2 in exI, 
      rule_tac x = m in exI, rule_tac x = "Suc ml" in exI, 
      rule_tac x = "mr - 1" in exI)
  apply(case_tac [!] mr, auto)
  done

lemma dec_first_on_right_moving_Bk_nonempty[simp]: 
  "dec_first_on_right_moving n (as, am) (s, l, Bk # xs) ires \<Longrightarrow> l \<noteq> []"
  apply(auto simp: dec_first_on_right_moving.simps split: if_splits)
  done

lemma replicateE: 
  "\<lbrakk>\<not> length lm1 < length am; 
    am @ replicate (length lm1 - length am) 0 @ [0::nat] = 
                                                lm1 @ m # lm2;
    0 < m\<rbrakk>
   \<Longrightarrow> RR"
  apply(subgoal_tac "lm2 = []", simp)
  apply(drule_tac length_equal, simp)
  done

lemma dec_after_clear_Bk_strip_hd[simp]: 
  "\<lbrakk>dec_first_on_right_moving n (as, 
                   abc_lm_s am n (abc_lm_v am n)) (s, l, Bk # xs) ires\<rbrakk>
\<Longrightarrow> dec_after_clear (as, abc_lm_s am n 
                 (abc_lm_v am n - Suc 0)) (s', tl l, hd l # Bk # xs) ires"
  apply(simp only: dec_first_on_right_moving.simps 
      dec_after_clear.simps abc_lm_s.simps abc_lm_v.simps)
  apply(erule_tac exE)+
  apply(rename_tac lm1 lm2 m ml mr rn)
  apply(cases "n < length am")
  by(rule_tac x = lm1 in exI, rule_tac x = lm2 in exI, 
      rule_tac x = "m - 1" in exI, auto elim:replicateE)

lemma dec_first_on_right_moving_dec_after_clear_cases[simp]: 
  "\<lbrakk>dec_first_on_right_moving n (as, 
                   abc_lm_s am n (abc_lm_v am n)) (s, l, []) ires\<rbrakk>
\<Longrightarrow> (l = [] \<longrightarrow> dec_after_clear (as, 
             abc_lm_s am n (abc_lm_v am n - Suc 0)) (s', [], [Bk]) ires) \<and>
    (l \<noteq> [] \<longrightarrow> dec_after_clear (as, abc_lm_s am n 
                      (abc_lm_v am n - Suc 0)) (s', tl l, [hd l]) ires)"
  apply(subgoal_tac "l \<noteq> []", 
      simp only: dec_first_on_right_moving.simps 
      dec_after_clear.simps abc_lm_s.simps abc_lm_v.simps)
   apply(erule_tac exE)+
   apply(rename_tac lm1 lm2 m ml mr rn)
   apply(cases "n < length am", simp)
    apply(rule_tac x = lm1 in exI, rule_tac x = "m - 1" in exI, auto)
    apply(case_tac [1-2] m, auto)
  apply(auto simp: dec_first_on_right_moving.simps split: if_splits)
  done

lemma dec_after_clear_Bk_via_Oc[simp]: "\<lbrakk>dec_after_clear (as, am) (s, l, Oc # r) ires\<rbrakk>
                \<Longrightarrow> dec_after_clear (as, am) (s', l, Bk # r) ires"
  apply(auto simp: dec_after_clear.simps)
  done

lemma dec_right_move_Bk_via_clear_Bk[simp]: "\<lbrakk>dec_after_clear (as, am) (s, l, Bk # r) ires\<rbrakk>
                \<Longrightarrow> dec_right_move (as, am) (s', Bk # l, r) ires"
  apply(auto simp: dec_after_clear.simps dec_right_move.simps split: if_splits)
  done

lemma dec_right_move_Bk_Bk_via_clear[simp]: "\<lbrakk>dec_after_clear (as, am) (s, l, []) ires\<rbrakk>
             \<Longrightarrow> dec_right_move (as, am) (s', Bk # l, [Bk]) ires"
  apply(auto simp: dec_after_clear.simps dec_right_move.simps split: if_splits)
  done

lemma dec_right_move_no_Oc[simp]:"dec_right_move (as, am) (s, l, Oc # r) ires = False"
  apply(auto simp: dec_right_move.simps)
  done

lemma dec_right_move_2_check_right_move[simp]:
  "\<lbrakk>dec_right_move (as, am) (s, l, Bk # r) ires\<rbrakk>
      \<Longrightarrow> dec_check_right_move (as, am) (s', Bk # l, r) ires"
  apply(auto simp: dec_right_move.simps dec_check_right_move.simps split: if_splits)
  done

lemma lm_iff_empty[simp]: "(<lm::nat list> = []) = (lm = [])"
  apply(cases lm, simp_all add: tape_of_nl_cons)
  done

lemma dec_right_move_asif_Bk_singleton[simp]: 
  "dec_right_move (as, am) (s, l, []) ires= 
  dec_right_move (as, am) (s, l, [Bk]) ires"
  apply(simp add: dec_right_move.simps)
  done

lemma dec_check_right_move_nonempty[simp]: "dec_check_right_move (as, am) (s, l, r) ires\<Longrightarrow> l \<noteq> []"
  apply(auto simp: dec_check_right_move.simps split: if_splits)
  done

lemma dec_check_right_move_Oc_tail[simp]: "\<lbrakk>dec_check_right_move (as, am) (s, l, Oc # r) ires\<rbrakk>
             \<Longrightarrow> dec_after_write (as, am) (s', tl l, hd l # Oc # r) ires"
  apply(auto simp: dec_check_right_move.simps dec_after_write.simps)
  apply(rename_tac lm1 lm2 m rn)
  apply(rule_tac x = lm1 in exI, rule_tac x = lm2 in exI, rule_tac x = m in exI, auto)
  done

lemma dec_left_move_Bk_tail[simp]: "\<lbrakk>dec_check_right_move (as, am) (s, l, Bk # r) ires\<rbrakk>
                \<Longrightarrow> dec_left_move (as, am) (s', tl l, hd l # Bk # r) ires"
  apply(auto simp: dec_check_right_move.simps dec_left_move.simps inv_after_move.simps)
  apply(rename_tac lm1 lm2 m rn)
  apply(rule_tac x = lm1 in exI, rule_tac x = m in exI, auto split: if_splits)
     apply(case_tac [!] lm2, simp_all add: tape_of_nl_cons split: if_splits)
   apply(rule_tac [!] x = "(Suc rn)" in exI, simp_all)
  done

lemma dec_left_move_tail[simp]: "\<lbrakk>dec_check_right_move (as, am) (s, l, []) ires\<rbrakk>
             \<Longrightarrow> dec_left_move (as, am) (s', tl l, [hd l]) ires"
  apply(auto simp: dec_check_right_move.simps dec_left_move.simps inv_after_move.simps)
  apply(rename_tac lm1 m)
  apply(rule_tac x = lm1 in exI, rule_tac x = m in exI, auto)
  done

lemma dec_left_move_no_Oc[simp]: "dec_left_move (as, am) (s, aaa, Oc # xs) ires = False"
  apply(auto simp: dec_left_move.simps inv_after_move.simps)
  done

lemma dec_left_move_nonempty[simp]: "dec_left_move (as, am) (s, l, r) ires
             \<Longrightarrow> l \<noteq> []"
  apply(auto simp: dec_left_move.simps split: if_splits)
  done

lemma inv_on_left_moving_in_middle_B_Oc_Bk_Bks[simp]: "inv_on_left_moving_in_middle_B (as, [m])
  (s', Oc # Oc\<up>m @ Bk # Bk # ires, Bk # Bk\<up>rn) ires"
  apply(simp add: inv_on_left_moving_in_middle_B.simps)
  apply(rule_tac x = "[m]" in exI, auto)
  done


lemma inv_on_left_moving_in_middle_B_Oc_Bk_Bks_rev[simp]: "lm1 \<noteq> [] \<Longrightarrow> 
  inv_on_left_moving_in_middle_B (as, lm1 @ [m]) (s', 
  Oc # Oc\<up>m @ Bk # <rev lm1> @ Bk # Bk # ires, Bk # Bk\<up>rn) ires"
  apply(simp only: inv_on_left_moving_in_middle_B.simps)
  apply(rule_tac x = "lm1 @ [m ]" in exI, rule_tac x = "[]" in exI, simp)
  apply(simp add: tape_of_nl_cons split: if_splits)
  done

lemma inv_on_left_moving_Bk_tail[simp]: "dec_left_move (as, am) (s, l, Bk # r) ires
       \<Longrightarrow> inv_on_left_moving (as, am) (s', tl l, hd l # Bk # r) ires"
  apply(auto simp: dec_left_move.simps inv_on_left_moving.simps split: if_splits)
  done

lemma inv_on_left_moving_tail[simp]: "dec_left_move (as, am) (s, l, []) ires
             \<Longrightarrow> inv_on_left_moving (as, am) (s', tl l, [hd l]) ires"
  apply(auto simp: dec_left_move.simps inv_on_left_moving.simps split: if_splits)
  done

lemma dec_on_right_moving_Oc_mv[simp]: "dec_after_write (as, am) (s, l, Oc # r) ires
       \<Longrightarrow> dec_on_right_moving (as, am) (s', Oc # l, r) ires"
  apply(auto simp: dec_after_write.simps dec_on_right_moving.simps)
  apply(rename_tac lm1 lm2 m rn)
  apply(rule_tac x = "lm1 @ [m]" in exI, rule_tac x = "tl lm2" in exI, 
      rule_tac x = "hd lm2" in exI, simp)
  apply(rule_tac x = "Suc 0" in exI,rule_tac x =  "Suc (hd lm2)" in exI)
  apply(case_tac lm2, auto split: if_splits simp: tape_of_nl_cons)
  done

lemma dec_after_write_Oc_via_Bk[simp]: "dec_after_write (as, am) (s, l, Bk # r) ires
       \<Longrightarrow> dec_after_write (as, am) (s', l, Oc # r) ires"
  apply(auto simp: dec_after_write.simps)
  done

lemma dec_after_write_Oc_empty[simp]: "dec_after_write (as, am) (s, aaa, []) ires
             \<Longrightarrow> dec_after_write (as, am) (s', aaa, [Oc]) ires"
  apply(auto simp: dec_after_write.simps)
  done

lemma dec_on_right_moving_Oc_move[simp]: "dec_on_right_moving (as, am) (s, l, Oc # r) ires
       \<Longrightarrow> dec_on_right_moving (as, am) (s', Oc # l, r) ires"
  apply(simp only: dec_on_right_moving.simps)
  apply(erule_tac exE)+
  apply(rename_tac lm1 lm2 m ml mr rn)
  apply(erule conjE)+
  apply(rule_tac x = lm1 in exI, rule_tac x = lm2 in exI,
      rule_tac x = "m" in exI, rule_tac x = "Suc ml" in exI, 
      rule_tac x = "mr - 1" in exI, simp)
  apply(case_tac mr, auto)
  done

lemma dec_on_right_moving_nonempty[simp]: "dec_on_right_moving (as, am) (s, l, r) ires\<Longrightarrow>  l \<noteq> []"
  apply(auto simp: dec_on_right_moving.simps split: if_splits)
  done

lemma dec_after_clear_Bk_tail[simp]: "dec_on_right_moving (as, am) (s, l, Bk # r) ires
      \<Longrightarrow>  dec_after_clear (as, am) (s', tl l, hd l # Bk # r) ires"
  apply(auto simp: dec_on_right_moving.simps dec_after_clear.simps simp del:split_head_repeat)
  apply(rename_tac lm1 lm2 m ml mr rn)
  apply(case_tac mr, auto split: if_splits)
  done

lemma dec_after_clear_tail[simp]: "dec_on_right_moving (as, am) (s, l, []) ires
             \<Longrightarrow> dec_after_clear (as, am) (s', tl l, [hd l]) ires"
  apply(auto simp: dec_on_right_moving.simps dec_after_clear.simps)
  apply(simp_all split: if_splits)
  apply(rule_tac x = lm1 in exI, simp)
  done

lemma dec_false_1[simp]:
  "\<lbrakk>abc_lm_v am n = 0; inv_locate_b (as, am) (n, aaa, Oc # xs) ires\<rbrakk>
  \<Longrightarrow> False"
  apply(auto simp: inv_locate_b.simps in_middle.simps)
   apply(rename_tac lm1 lm2 m ml Mr rn)
   apply(case_tac "length lm1 \<ge> length am", auto)
    apply(subgoal_tac "lm2 = []", simp, subgoal_tac "m = 0", simp)
      apply(case_tac Mr, auto simp: )
     apply(subgoal_tac "Suc (length lm1) - length am = 
                   Suc (length lm1 - length am)", 
      simp add: exp_ind del: replicate.simps, simp)
    apply(drule_tac xs = "am @ replicate (Suc (length lm1) - length am) 0"
      and ys = "lm1 @ m # lm2" in length_equal, simp)
   apply(case_tac Mr, auto simp: abc_lm_v.simps)
  apply(rename_tac lm1 m ml Mr)
  apply(case_tac "Mr = 0", simp_all split: if_splits)
  apply(subgoal_tac "Suc (length lm1) - length am = 
                       Suc (length lm1 - length am)", 
      simp add: exp_ind del: replicate.simps, simp)
  done

lemma inv_on_left_moving_Bk_tl[simp]: 
  "\<lbrakk>inv_locate_b (as, am) (n, aaa, Bk # xs) ires; 
   abc_lm_v am n = 0\<rbrakk>
   \<Longrightarrow> inv_on_left_moving (as, abc_lm_s am n 0) 
                         (s, tl aaa, hd aaa # Bk # xs) ires"
  apply(simp add: inv_on_left_moving.simps)
  apply(simp only: inv_locate_b.simps in_middle.simps) 
  apply(erule_tac exE)+
  apply(rename_tac Lm1 Lm2 tn M ml Mr rn)
  apply(subgoal_tac "\<not> inv_on_left_moving_in_middle_B 
         (as, abc_lm_s am n 0) (s, tl aaa, hd aaa # Bk # xs) ires", simp)
   apply(simp only: inv_on_left_moving_norm.simps)
   apply(erule_tac conjE)+
   apply(rule_tac x = Lm1 in exI, rule_tac x = Lm2 in exI, 
      rule_tac x =  M in exI, rule_tac x = M in exI, 
      rule_tac x = "Suc 0" in exI, simp add: abc_lm_s.simps)
   apply(case_tac Mr, auto simp: abc_lm_v.simps)
   apply(simp only: exp_ind[THEN sym] replicate_Suc Nat.Suc_diff_le)
  apply(auto simp: inv_on_left_moving_in_middle_B.simps split: if_splits)
  done


lemma inv_on_left_moving_tl[simp]:
  "\<lbrakk>abc_lm_v am n = 0; inv_locate_b (as, am) (n, aaa, []) ires\<rbrakk>
   \<Longrightarrow> inv_on_left_moving (as, abc_lm_s am n 0) (s, tl aaa, [hd aaa]) ires"
  apply(simp add: inv_on_left_moving.simps)
  apply(simp only: inv_locate_b.simps in_middle.simps) 
  apply(erule_tac exE)+
  apply(rename_tac Lm1 Lm2 tn M ml Mr rn)
  apply(simp add: inv_on_left_moving.simps)
  apply(subgoal_tac "\<not> inv_on_left_moving_in_middle_B 
         (as, abc_lm_s am n 0) (s, tl aaa, [hd aaa]) ires", simp)
   apply(simp only: inv_on_left_moving_norm.simps)
   apply(erule_tac conjE)+
   apply(rule_tac x = Lm1 in exI, rule_tac x = Lm2 in exI, 
      rule_tac x =  M in exI, rule_tac x = M in exI, 
      rule_tac x = "Suc 0" in exI, simp add: abc_lm_s.simps)
   apply(case_tac Mr, simp_all, auto simp: abc_lm_v.simps)
    apply(simp_all only: exp_ind Nat.Suc_diff_le del: replicate_Suc, simp_all)
  apply(auto simp: inv_on_left_moving_in_middle_B.simps split: if_splits)
   apply(case_tac [!] M, simp_all)
  done

declare dec_inv_1.simps[simp del]

declare inv_locate_n_b.simps [simp del]

lemma dec_first_on_right_moving_Oc_via_inv_locate_n_b[simp]:
  "\<lbrakk>inv_locate_n_b (as, am) (n, aaa, Oc # xs) ires\<rbrakk>
 \<Longrightarrow> dec_first_on_right_moving n (as, abc_lm_s am n (abc_lm_v am n))  
                                      (s, Oc # aaa, xs) ires"
  apply(auto simp: inv_locate_n_b.simps dec_first_on_right_moving.simps 
      abc_lm_s.simps abc_lm_v.simps)
     apply(rename_tac Lm1 Lm2 m rn)
     apply(rule_tac x = Lm1 in exI, rule_tac x = Lm2 in exI, 
      rule_tac x = m in exI, simp)
     apply(rule_tac x = "Suc (Suc 0)" in exI, 
      rule_tac x = "m - 1" in exI, simp)
     apply (metis One_nat_def Suc_pred cell.distinct(1) empty_replicate list.inject list.sel(3)
      neq0_conv self_append_conv2 tl_append2 tl_replicate)
    apply(rename_tac Lm1 Lm2 m rn)
    apply(rule_tac x = Lm1 in exI, rule_tac x = Lm2 in exI, 
      rule_tac x = m in exI, 
      simp add: Suc_diff_le exp_ind del: replicate.simps)
    apply(rule_tac x = "Suc (Suc 0)" in exI, 
      rule_tac x = "m - 1" in exI, simp)
    apply (metis cell.distinct(1) empty_replicate gr_zeroI list.inject replicateE self_append_conv2)
   apply(rename_tac Lm1 m)
   apply(rule_tac x = Lm1 in exI, rule_tac x = "[]" in exI, 
      rule_tac x = m in exI, simp)
   apply(rule_tac x = "Suc (Suc 0)" in exI, 
      rule_tac x = "m - 1" in exI, simp)
   apply(case_tac m, auto)
  apply(rename_tac Lm1 m)
  apply(rule_tac x = Lm1 in exI, rule_tac x = "[]" in exI, rule_tac x = m in exI, 
      simp add: Suc_diff_le exp_ind del: replicate.simps, simp)
  done

lemma inv_on_left_moving_nonempty[simp]: "inv_on_left_moving (as, am) (s, [], r) ires 
  = False"
  apply(simp add: inv_on_left_moving.simps inv_on_left_moving_norm.simps
      inv_on_left_moving_in_middle_B.simps)
  done

lemma inv_check_left_moving_startof_nonempty[simp]: 
  "inv_check_left_moving (as, abc_lm_s am n 0)
  (start_of (layout_of aprog) as + 2 * n + 14, [], Oc # xs) ires
 = False"
  apply(simp add: inv_check_left_moving.simps inv_check_left_moving_in_middle.simps)
  done

lemma start_of_lessE[elim]: "\<lbrakk>abc_fetch as ap = Some (Dec n e);
                start_of (layout_of ap) as < start_of (layout_of ap) e; 
                start_of (layout_of ap) e \<le> Suc (start_of (layout_of ap) as + 2 * n)\<rbrakk>
       \<Longrightarrow> RR"
  using start_of_less[of e as "layout_of ap"] start_of_ge[of as ap n e "layout_of ap"]
  apply(cases "as < e", simp)
  apply(cases "as = e", simp, simp)
  done

lemma crsp_step_dec_b_e_pre':
  assumes layout: "ly = layout_of ap"
    and inv_start: "inv_locate_b (as, lm) (n, la, ra) ires"
    and fetch: "abc_fetch as ap = Some (Dec n e)"
    and dec_0: "abc_lm_v lm n = 0"
    and f: "f = (\<lambda> stp. (steps (Suc (start_of ly as) + 2 * n, la, ra) (ci ly (start_of ly as) (Dec n e), 
            start_of ly as - Suc 0) stp, start_of ly as, n))"
    and P: "P = (\<lambda> ((s, l, r), ss, x). s = start_of ly e)"
    and Q: "Q = (\<lambda> ((s, l, r), ss, x). dec_inv_1 ly x e (as, lm) (s, l, r) ires)"
  shows "\<exists> stp. P (f stp) \<and> Q (f stp)"
proof(rule_tac LE = abc_dec_1_LE in halt_lemma2)
  show "wf abc_dec_1_LE" by(intro wf_dec_le)
next
  show "Q (f 0)"
    using layout fetch
    apply(simp add: f steps.simps Q dec_inv_1.simps)
    apply(subgoal_tac "e > as \<or> e = as \<or> e < as")
     apply(auto simp: inv_start)
    done
next
  show "\<not> P (f 0)"
    using layout fetch
    apply(simp add: f steps.simps P)
    done
next
  show "\<forall>n. \<not> P (f n) \<and> Q (f n) \<longrightarrow> Q (f (Suc n)) \<and> (f (Suc n), f n) \<in> abc_dec_1_LE"
    using fetch
  proof(rule_tac allI, rule_tac impI)
    fix na
    assume "\<not> P (f na) \<and> Q (f na)"
    thus "Q (f (Suc na)) \<and> (f (Suc na), f na) \<in> abc_dec_1_LE"
      apply(simp add: f)
      apply(cases "steps (Suc (start_of ly as + 2 * n), la, ra)
        (ci ly (start_of ly as) (Dec n e), start_of ly as - Suc 0) na", simp)
    proof -
      fix a b c 
      assume "\<not> P ((a, b, c), start_of ly as, n) \<and> Q ((a, b, c), start_of ly as, n)"
      thus "Q (step (a, b, c) (ci ly (start_of ly as) (Dec n e), start_of ly as - Suc 0), start_of ly as, n) \<and>
               ((step (a, b, c) (ci ly (start_of ly as) (Dec n e), start_of ly as - Suc 0), start_of ly as, n), 
                   (a, b, c), start_of ly as, n) \<in> abc_dec_1_LE"
        apply(simp add: Q)
        apply(cases c;cases "hd c")
           apply(simp_all add: dec_inv_1.simps Let_def split: if_splits)
        using fetch layout dec_0
                        apply(auto simp: step.simps P dec_inv_1.simps Let_def abc_dec_1_LE_def
            lex_triple_def lex_pair_def)
        using dec_0
        apply(drule_tac dec_false_1, simp_all)
        done
    qed
  qed
qed

lemma crsp_step_dec_b_e_pre:
  assumes "ly = layout_of ap"
    and inv_start: "inv_locate_b (as, lm) (n, la, ra) ires"
    and dec_0: "abc_lm_v lm n  = 0"
    and fetch: "abc_fetch as ap = Some (Dec n e)"
  shows "\<exists>stp lb rb.
       steps (Suc (start_of ly as) + 2 * n, la, ra) (ci ly (start_of ly as) (Dec n e), 
       start_of ly as - Suc 0) stp = (start_of ly e, lb, rb) \<and>
       dec_inv_1 ly n e (as, lm) (start_of ly e, lb, rb) ires"
  using assms
  apply(drule_tac crsp_step_dec_b_e_pre', auto)
  apply(rename_tac stp a b)
  apply(rule_tac x = stp in exI, simp)
  done

lemma crsp_abc_step_via_stop[simp]:
  "\<lbrakk>abc_lm_v lm n = 0;
  inv_stop (as, abc_lm_s lm n (abc_lm_v lm n)) (start_of ly e, lb, rb) ires\<rbrakk>
  \<Longrightarrow> crsp ly (abc_step_l (as, lm) (Some (Dec n e))) (start_of ly e, lb, rb) ires"
  apply(auto simp: crsp.simps abc_step_l.simps inv_stop.simps)
  done

lemma crsp_step_dec_b_e:
  assumes layout: "ly = layout_of ap"
    and inv_start: "inv_locate_a (as, lm) (n, l, r) ires"
    and dec_0: "abc_lm_v lm n = 0"
    and fetch: "abc_fetch as ap = Some (Dec n e)"
  shows "\<exists>stp > 0. crsp ly (abc_step_l (as, lm) (Some (Dec n e)))
  (steps (start_of ly as + 2 * n, l, r) (ci ly (start_of ly as) (Dec n e), start_of ly as - Suc 0) stp) ires"
proof -
  let ?P = "ci ly (start_of ly as) (Dec n e)"
  let ?off = "start_of ly as - Suc 0"
  have "\<exists> stp la ra. steps (start_of ly as + 2 * n, l, r) (?P, ?off) stp = (Suc (start_of ly as) + 2*n, la, ra)
             \<and>  inv_locate_b (as, lm) (n, la, ra) ires"
    using inv_start
    apply(cases "r = [] \<or> hd r = Bk", simp_all)
    done
  from this obtain stpa la ra where a:
    "steps (start_of ly as + 2 * n, l, r) (?P, ?off) stpa = (Suc (start_of ly as) + 2*n, la, ra)
             \<and>  inv_locate_b (as, lm) (n, la, ra) ires" by blast
  have "\<exists> stp lb rb. steps (Suc (start_of ly as) + 2 * n, la, ra) (?P, ?off) stp = (start_of ly e, lb, rb)
             \<and>  dec_inv_1 ly n e (as, lm) (start_of ly e, lb, rb) ires"
    using assms a
    apply(rule_tac crsp_step_dec_b_e_pre, auto)
    done
  from this obtain stpb lb rb where b:
    "steps (Suc (start_of ly as) + 2 * n, la, ra) (?P, ?off) stpb = (start_of ly e, lb, rb)
             \<and>  dec_inv_1 ly n e (as, lm) (start_of ly e, lb, rb) ires"  by blast
  from a b show "\<exists>stp > 0. crsp ly (abc_step_l (as, lm) (Some (Dec n e))) 
    (steps (start_of ly as + 2 * n, l, r) (?P, ?off) stp) ires"
    apply(rule_tac x = "stpa + stpb" in exI)
    using dec_0
    apply(simp add: dec_inv_1.simps )
    apply(cases stpa, simp_all add: steps.simps)
    done
qed    

fun dec_inv_2 :: "layout \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> dec_inv_t"
  where
    "dec_inv_2 ly n e (as, am) (s, l, r) ires =
           (let ss = start_of ly as in
            let am' = abc_lm_s am n (abc_lm_v am n - Suc 0) in
            let am'' = abc_lm_s am n (abc_lm_v am n) in
              if s = 0 then False
              else if s = ss + 2 * n then 
                      inv_locate_a (as, am) (n, l, r) ires
              else if s = ss + 2 * n + 1 then 
                      inv_locate_n_b (as, am) (n, l, r) ires
              else if s = ss + 2 * n + 2 then 
                      dec_first_on_right_moving n (as, am'') (s, l, r) ires
              else if s = ss + 2 * n + 3 then 
                      dec_after_clear (as, am') (s, l, r) ires
              else if s = ss + 2 * n + 4 then 
                      dec_right_move (as, am') (s, l, r) ires
              else if s = ss + 2 * n + 5 then 
                      dec_check_right_move (as, am') (s, l, r) ires
              else if s = ss + 2 * n + 6 then 
                      dec_left_move (as, am') (s, l, r) ires
              else if s = ss + 2 * n + 7 then 
                      dec_after_write (as, am') (s, l, r) ires
              else if s = ss + 2 * n + 8 then 
                      dec_on_right_moving (as, am') (s, l, r) ires
              else if s = ss + 2 * n + 9 then 
                      dec_after_clear (as, am') (s, l, r) ires
              else if s = ss + 2 * n + 10 then 
                      inv_on_left_moving (as, am') (s, l, r) ires
              else if s = ss + 2 * n + 11 then 
                      inv_check_left_moving (as, am') (s, l, r) ires
              else if s = ss + 2 * n + 12 then 
                      inv_after_left_moving (as, am') (s, l, r) ires
              else if s = ss + 2 * n + 16 then 
                      inv_stop (as, am') (s, l, r) ires
              else False)"

declare dec_inv_2.simps[simp del]
fun abc_dec_2_stage1 :: "config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "abc_dec_2_stage1 (s, l, r) ss n = 
              (if s \<le> ss + 2*n + 1 then 7
               else if s = ss + 2*n + 2 then 6 
               else if s = ss + 2*n + 3 then 5
               else if s \<ge> ss + 2*n + 4 \<and> s \<le> ss + 2*n + 9 then 4
               else if s = ss + 2*n + 6 then 3
               else if s = ss + 2*n + 10 \<or> s = ss + 2*n + 11 then 2
               else if s = ss + 2*n + 12 then 1
               else 0)"

fun abc_dec_2_stage2 :: "config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "abc_dec_2_stage2 (s, l, r) ss n = 
       (if s \<le> ss + 2 * n + 1 then (ss + 2 * n + 16 - s)
        else if s = ss + 2*n + 10 then length l
        else if s = ss + 2*n + 11 then length l
        else if s = ss + 2*n + 4 then length r - 1
        else if s = ss + 2*n + 5 then length r 
        else if s = ss + 2*n + 7 then length r - 1
        else if s = ss + 2*n + 8 then  
              length r + length (takeWhile (\<lambda> a. a = Oc) l) - 1
        else if s = ss + 2*n + 9 then 
              length r + length (takeWhile (\<lambda> a. a = Oc) l) - 1
        else 0)"

fun abc_dec_2_stage3 :: "config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "abc_dec_2_stage3 (s, l, r) ss n  =
        (if s \<le> ss + 2*n + 1 then 
            if (s - ss) mod 2 = 0 then if r \<noteq> [] \<and> 
                                          hd r = Oc then 0 else 1  
            else length r
         else if s = ss + 2 * n + 10 then 
             if  r \<noteq> [] \<and> hd r = Oc then 2
             else 1
         else if s = ss + 2 * n + 11 then 
             if r \<noteq> [] \<and> hd r = Oc then 3 
             else 0 
         else (ss + 2 * n + 16 - s))"

fun abc_dec_2_stage4 :: "config \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "abc_dec_2_stage4 (s, l, r) ss n = 
          (if s = ss + 2*n + 2 then length r
           else if s = ss + 2*n + 8 then length r
           else if s = ss + 2*n + 3 then 
               if r \<noteq> [] \<and> hd r = Oc then 1
               else 0
           else if s = ss + 2*n + 7 then 
               if r \<noteq> [] \<and> hd r = Oc then 0 
               else 1
           else if s = ss + 2*n + 9 then 
               if r \<noteq> [] \<and> hd r = Oc then 1
               else 0 
           else 0)"

fun abc_dec_2_measure :: "(config \<times> nat \<times> nat) \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)"
  where
    "abc_dec_2_measure (c, ss, n) = 
  (abc_dec_2_stage1 c ss n, 
  abc_dec_2_stage2 c ss n, abc_dec_2_stage3 c ss n,  abc_dec_2_stage4 c ss n)"

definition lex_square:: 
  "((nat \<times> nat \<times> nat \<times> nat) \<times> (nat \<times> nat \<times> nat \<times> nat)) set"
  where "lex_square \<equiv> less_than <*lex*> lex_triple"

definition abc_dec_2_LE ::
  "((config \<times> nat \<times>
  nat) \<times> (config \<times> nat \<times> nat)) set"
  where "abc_dec_2_LE \<equiv> (inv_image lex_square abc_dec_2_measure)"

lemma wf_dec2_le: "wf abc_dec_2_LE"
  by(auto simp:abc_dec_2_LE_def lex_square_def lex_triple_def lex_pair_def)

lemma fix_add: "fetch ap ((x::nat) + 2*n) b = fetch ap (2*n + x) b"
  using Suc_1 add.commute by metis

lemma inv_locate_n_b_Bk_elim[elim]: 
  "\<lbrakk>0 < abc_lm_v am n; inv_locate_n_b (as, am) (n, aaa, Bk # xs) ires\<rbrakk> 
 \<Longrightarrow> RR"
  by(auto simp:gr0_conv_Suc inv_locate_n_b.simps abc_lm_v.simps split: if_splits)

lemma inv_locate_n_b_nonemptyE[elim]:
  "\<lbrakk>0 < abc_lm_v am n; inv_locate_n_b (as, am) 
                                (n, aaa, []) ires\<rbrakk> \<Longrightarrow> RR"
  apply(auto simp: inv_locate_n_b.simps abc_lm_v.simps split: if_splits)
  done

lemma no_Ocs_dec_after_write[simp]: "dec_after_write (as, am) (s, aa, r) ires
           \<Longrightarrow> takeWhile (\<lambda>a. a = Oc) aa = []"
  apply(simp only : dec_after_write.simps)
  apply(erule exE)+
  apply(erule_tac conjE)+
  apply(cases aa, simp)
  apply(cases "hd aa", simp only: takeWhile.simps , simp_all split: if_splits)
  done

lemma fewer_Ocs_dec_on_right_moving[simp]: 
  "\<lbrakk>dec_on_right_moving (as, lm) (s, aa, []) ires; 
       length (takeWhile (\<lambda>a. a = Oc) (tl aa)) 
           \<noteq> length (takeWhile (\<lambda>a. a = Oc) aa) - Suc 0\<rbrakk>
    \<Longrightarrow> length (takeWhile (\<lambda>a. a = Oc) (tl aa)) < 
                       length (takeWhile (\<lambda>a. a = Oc) aa) - Suc 0"
  apply(simp only: dec_on_right_moving.simps)
  apply(erule_tac exE)+
  apply(erule_tac conjE)+
  apply(rename_tac lm1 lm2 m ml Mr rn)
  apply(case_tac Mr, auto split: if_splits)
  done

lemma more_Ocs_dec_after_clear[simp]: 
  "dec_after_clear (as, abc_lm_s am n (abc_lm_v am n - Suc 0)) 
             (start_of (layout_of aprog) as + 2 * n + 9, aa, Bk # xs) ires
 \<Longrightarrow> length xs - Suc 0 < length xs + 
                             length (takeWhile (\<lambda>a. a = Oc) aa)"
  apply(simp only: dec_after_clear.simps)
  apply(erule_tac exE)+
  apply(erule conjE)+
  apply(simp split: if_splits )
  done

lemma more_Ocs_dec_after_clear2[simp]: 
  "\<lbrakk>dec_after_clear (as, abc_lm_s am n (abc_lm_v am n - Suc 0))
       (start_of (layout_of aprog) as + 2 * n + 9, aa, []) ires\<rbrakk>
    \<Longrightarrow> Suc 0 < length (takeWhile (\<lambda>a. a = Oc) aa)"
  apply(simp add: dec_after_clear.simps split: if_splits)
  done

lemma inv_check_left_moving_nonemptyE[elim]: 
  "inv_check_left_moving (as, lm) (s, [], Oc # xs) ires
 \<Longrightarrow> RR"
  apply(simp add: inv_check_left_moving.simps inv_check_left_moving_in_middle.simps)
  done

lemma inv_locate_n_b_Oc_via_at_begin_norm[simp]:
  "\<lbrakk>0 < abc_lm_v am n; 
  at_begin_norm (as, am) (n, aaa, Oc # xs) ires\<rbrakk>
  \<Longrightarrow> inv_locate_n_b (as, am) (n, Oc # aaa, xs) ires"
  apply(simp only: at_begin_norm.simps inv_locate_n_b.simps)
  apply(erule_tac exE)+
  apply(rename_tac lm1 lm2 rn)
  apply(rule_tac x = lm1 in exI, simp)
  apply(case_tac "length lm2", simp)
  apply(case_tac "lm2", simp, simp)
  apply(case_tac "lm2", auto simp: tape_of_nl_cons split: if_splits)
  done

lemma inv_locate_n_b_Oc_via_at_begin_fst_awtn[simp]: 
  "\<lbrakk>0 < abc_lm_v am n; 
   at_begin_fst_awtn (as, am) (n, aaa, Oc # xs) ires\<rbrakk>
 \<Longrightarrow> inv_locate_n_b (as, am) (n, Oc # aaa, xs) ires"
  apply(simp only: at_begin_fst_awtn.simps inv_locate_n_b.simps )
  apply(erule exE)+
  apply(rename_tac lm1 tn rn)
  apply(erule conjE)+
  apply(rule_tac x = lm1 in exI, rule_tac x = "[]" in exI, 
      rule_tac x = "Suc tn" in exI, rule_tac x = 0 in exI)
  apply(simp add: exp_ind del: replicate.simps)
  apply(rule conjI)+
   apply(auto)
  done

lemma inv_locate_n_b_Oc_via_inv_locate_n_a[simp]: 
  "\<lbrakk>0 < abc_lm_v am n; inv_locate_a (as, am) (n, aaa, Oc # xs) ires\<rbrakk>
 \<Longrightarrow> inv_locate_n_b (as, am) (n, Oc#aaa, xs) ires"
  apply(auto simp: inv_locate_a.simps at_begin_fst_bwtn.simps)
  done

lemma more_Oc_dec_on_right_moving[simp]: 
  "\<lbrakk>dec_on_right_moving (as, am) (s, aa, Bk # xs) ires; 
   Suc (length (takeWhile (\<lambda>a. a = Oc) (tl aa)))
   \<noteq> length (takeWhile (\<lambda>a. a = Oc) aa)\<rbrakk>
  \<Longrightarrow> Suc (length (takeWhile (\<lambda>a. a = Oc) (tl aa))) 
    < length (takeWhile (\<lambda>a. a = Oc) aa)"
  apply(simp only: dec_on_right_moving.simps)
  apply(erule exE)+
  apply(rename_tac ml mr rn)
  apply(case_tac ml, auto split: if_splits )
  done

lemma crsp_step_dec_b_suc_pre:
  assumes layout: "ly = layout_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
    and inv_start: "inv_locate_a (as, lm) (n, la, ra) ires"
    and fetch: "abc_fetch as ap = Some (Dec n e)"
    and dec_suc: "0 < abc_lm_v lm n"
    and f: "f = (\<lambda> stp. (steps (start_of ly as + 2 * n, la, ra) (ci ly (start_of ly as) (Dec n e), 
            start_of ly as - Suc 0) stp, start_of ly as, n))"
    and P: "P = (\<lambda> ((s, l, r), ss, x). s = start_of ly as + 2*n + 16)"
    and Q: "Q = (\<lambda> ((s, l, r), ss, x). dec_inv_2 ly x e (as, lm) (s, l, r) ires)"
  shows "\<exists> stp. P (f stp) \<and> Q(f stp)"
proof(rule_tac LE = abc_dec_2_LE in halt_lemma2)
  show "wf abc_dec_2_LE" by(intro wf_dec2_le)
next
  show "Q (f 0)"
    using layout fetch inv_start
    apply(simp add: f steps.simps Q)
    apply(simp only: dec_inv_2.simps)
    apply(auto simp: Let_def start_of_ge start_of_less inv_start dec_inv_2.simps)
    done
next
  show "\<not> P (f 0)"
    using layout fetch
    apply(simp add: f steps.simps P)
    done
next
  show "\<forall>n. \<not> P (f n) \<and> Q (f n) \<longrightarrow> Q (f (Suc n)) \<and> (f (Suc n), f n) \<in> abc_dec_2_LE"
    using fetch
  proof(rule_tac allI, rule_tac impI)
    fix na
    assume "\<not> P (f na) \<and> Q (f na)"
    thus "Q (f (Suc na)) \<and> (f (Suc na), f na) \<in> abc_dec_2_LE"
      apply(simp add: f)
      apply(cases "steps ((start_of ly as + 2 * n), la, ra)
        (ci ly (start_of ly as) (Dec n e), start_of ly as - Suc 0) na", simp)
    proof -
      fix a b c 
      assume "\<not> P ((a, b, c), start_of ly as, n) \<and> Q ((a, b, c), start_of ly as, n)"
      thus "Q (step (a, b, c) (ci ly (start_of ly as) (Dec n e), start_of ly as - Suc 0), start_of ly as, n) \<and>
               ((step (a, b, c) (ci ly (start_of ly as) (Dec n e), start_of ly as - Suc 0), start_of ly as, n), 
                   (a, b, c), start_of ly as, n) \<in> abc_dec_2_LE"
        apply(simp add: Q)
        apply(erule_tac conjE)
        apply(cases c; cases "hd c")
           apply(simp_all add: dec_inv_2.simps Let_def)
           apply(simp_all split: if_splits)
        using fetch layout dec_suc
                            apply(auto simp: step.simps P dec_inv_2.simps Let_def abc_dec_2_LE_def lex_triple_def lex_pair_def lex_square_def
            fix_add numeral_3_eq_3) 
        done
    qed
  qed
qed

lemma crsp_abc_step_l_start_of[simp]: 
  "\<lbrakk>inv_stop (as, abc_lm_s lm n (abc_lm_v lm n - Suc 0)) 
  (start_of (layout_of ap) as + 2 * n + 16, a, b) ires;
   abc_lm_v lm n > 0;
   abc_fetch as ap = Some (Dec n e)\<rbrakk>
  \<Longrightarrow> crsp (layout_of ap) (abc_step_l (as, lm) (Some (Dec n e))) 
  (start_of (layout_of ap) as + 2 * n + 16, a, b) ires"
  by(auto simp: inv_stop.simps crsp.simps  abc_step_l.simps startof_Suc2)

lemma crsp_step_dec_b_suc:
  assumes layout: "ly = layout_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
    and inv_start: "inv_locate_a (as, lm) (n, la, ra) ires"
    and fetch: "abc_fetch as ap = Some (Dec n e)"
    and dec_suc: "0 < abc_lm_v lm n"
  shows "\<exists>stp > 0. crsp ly (abc_step_l (as, lm) (Some (Dec n e)))
              (steps (start_of ly as + 2 * n, la, ra) (ci (layout_of ap) 
                  (start_of ly as) (Dec n e), start_of ly as - Suc 0) stp) ires"
  using assms
  apply(drule_tac crsp_step_dec_b_suc_pre, auto)
  apply(rename_tac stp a b)
  apply(rule_tac x = stp in exI)
  apply(case_tac stp, simp_all add: steps.simps dec_inv_2.simps)
  done

lemma crsp_step_dec_b:
  assumes layout: "ly = layout_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
    and inv_start: "inv_locate_a (as, lm) (n, la, ra) ires"
    and fetch: "abc_fetch as ap = Some (Dec n e)"
  shows "\<exists>stp > 0. crsp ly (abc_step_l (as, lm) (Some (Dec n e)))
  (steps (start_of ly as + 2 * n, la, ra) (ci ly (start_of ly as) (Dec n e), start_of ly as - Suc 0) stp) ires"
  using assms
  apply(cases "abc_lm_v lm n = 0")
   apply(rule_tac crsp_step_dec_b_e, simp_all)
  apply(rule_tac crsp_step_dec_b_suc, simp_all)
  done

lemma crsp_step_dec: 
  assumes layout: "ly = layout_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
    and fetch: "abc_fetch as ap = Some (Dec n e)"
  shows "\<exists>stp > 0. crsp ly (abc_step_l (as, lm) (Some (Dec n e)))
  (steps (s, l, r) (ci ly (start_of ly as) (Dec n e), start_of ly as - Suc 0) stp) ires"
proof(simp add: ci.simps)
  let ?off = "start_of ly as - Suc 0"
  let ?A = "findnth n"
  let ?B = "adjust (shift (shift tdec_b (2 * n)) ?off) (start_of ly e)"
  have "\<exists> stp la ra. steps (s, l, r) (shift ?A ?off @ ?B, ?off) stp = (start_of ly as + 2*n, la, ra)
                    \<and> inv_locate_a (as, lm) (n, la, ra) ires"
  proof -
    have "\<exists>stp l' r'. steps (Suc 0, l, r) (?A, 0) stp = (Suc (2 * n), l', r') \<and> 
                     inv_locate_a (as, lm) (n, l', r') ires"
      using assms
      apply(rule_tac findnth_correct, simp_all)
      done
    then obtain stp l' r' where a: 
      "steps (Suc 0, l, r) (?A, 0) stp = (Suc (2 * n), l', r') \<and> 
      inv_locate_a (as, lm) (n, l', r') ires" by blast
    then have "steps (Suc 0 + ?off, l, r) (shift ?A ?off, ?off) stp = (Suc (2 * n) + ?off, l', r')"
      apply(rule_tac tm_shift_eq_steps, simp_all)
      done
    moreover have "s = start_of ly as"
      using crsp
      apply(auto simp: crsp.simps)
      done
    ultimately show "\<exists> stp la ra. steps (s, l, r) (shift ?A ?off @ ?B, ?off) stp = (start_of ly as + 2*n, la, ra)
                    \<and> inv_locate_a (as, lm) (n, la, ra) ires"
      using a
      apply(drule_tac B = ?B in tm_append_first_steps_eq, auto)
      apply(rule_tac x = stp in exI, simp)
      done
  qed
  from this obtain stpa la ra where a: 
    "steps (s, l, r) (shift ?A ?off @ ?B, ?off) stpa = (start_of ly as + 2*n, la, ra)
                    \<and> inv_locate_a (as, lm) (n, la, ra) ires" by blast
  have "\<exists>stp. crsp ly (abc_step_l (as, lm) (Some (Dec n e)))
           (steps (start_of ly as + 2*n, la, ra) (shift ?A ?off @ ?B, ?off) stp) ires \<and> stp > 0"
    using assms a
    apply(drule_tac crsp_step_dec_b, auto)
    apply(rename_tac stp)
    apply(rule_tac x = stp in exI, simp add: ci.simps)
    done
  then obtain stpb where b: 
    "crsp ly (abc_step_l (as, lm) (Some (Dec n e)))
    (steps (start_of ly as + 2*n, la, ra) (shift ?A ?off @ ?B, ?off) stpb) ires \<and> stpb > 0" ..
  from a b show "\<exists> stp>0. crsp ly (abc_step_l (as, lm) (Some (Dec n e)))
    (steps (s, l, r) (shift ?A ?off @ ?B, ?off) stp) ires"
    apply(rule_tac x = "stpa + stpb" in exI)
    apply(simp)
    done
qed    

subsection\<open>Crsp of Goto\<close>

lemma crsp_step_goto:
  assumes layout: "ly = layout_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
  shows "\<exists>stp>0. crsp ly (abc_step_l (as, lm) (Some (Goto n)))
  (steps (s, l, r) (ci ly (start_of ly as) (Goto n), 
            start_of ly as - Suc 0) stp) ires"
  using crsp
  apply(rule_tac x = "Suc 0" in exI)
  apply(cases r;cases "hd r")
     apply(simp_all add: ci.simps steps.simps step.simps crsp.simps fetch.simps abc_step_l.simps)
  done

lemma crsp_step_in:
  assumes layout: "ly = layout_of ap"
    and compile: "tp = tm_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
    and fetch: "abc_fetch as ap = Some ins"
  shows "\<exists> stp>0. crsp ly (abc_step_l (as, lm) (Some ins))
                      (steps (s, l, r) (ci ly (start_of ly as) ins, start_of ly as - 1) stp) ires"
  using assms
  apply(cases ins, simp_all)
    apply(rule crsp_step_inc, simp_all)
   apply(rule crsp_step_dec, simp_all)
  apply(rule_tac crsp_step_goto, simp_all)
  done

lemma crsp_step:
  assumes layout: "ly = layout_of ap"
    and compile: "tp = tm_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
    and fetch: "abc_fetch as ap = Some ins"
  shows "\<exists> stp>0. crsp ly (abc_step_l (as, lm) (Some ins))
                      (steps (s, l, r) (tp, 0) stp) ires"
proof -
  have "\<exists> stp>0. crsp ly (abc_step_l (as, lm) (Some ins))
                      (steps (s, l, r) (ci ly (start_of ly as) ins, start_of ly as - 1) stp) ires"
    using assms
    apply(rule_tac crsp_step_in, simp_all)
    done
  from this obtain stp where d: "stp > 0 \<and> crsp ly (abc_step_l (as, lm) (Some ins))
                      (steps (s, l, r) (ci ly (start_of ly as) ins, start_of ly as - 1) stp) ires" ..
  obtain s' l' r' where e:
    "(steps (s, l, r) (ci ly (start_of ly as) ins, start_of ly as - 1) stp) = (s', l', r')"
    apply(cases "(steps (s, l, r) (ci ly (start_of ly as) ins, start_of ly as - 1) stp)")
    by blast
  then have "steps (s, l, r) (tp, 0) stp = (s', l', r')"
    using assms d
    apply(rule_tac steps_eq_in)
         apply(simp_all)
    apply(cases "(abc_step_l (as, lm) (Some ins))", simp add: crsp.simps)
    done    
  thus " \<exists>stp>0. crsp ly (abc_step_l (as, lm) (Some ins)) (steps (s, l, r) (tp, 0) stp) ires"
    using d e
    apply(rule_tac x = stp in exI, simp)
    done
qed

lemma crsp_steps:
  assumes layout: "ly = layout_of ap"
    and compile: "tp = tm_of ap"
    and crsp: "crsp ly (as, lm) (s, l, r) ires"
  shows "\<exists> stp. crsp ly (abc_steps_l (as, lm) ap n)
                      (steps (s, l, r) (tp, 0) stp) ires"
  using crsp
proof(induct n)
  case 0
  then show ?case  apply(rule_tac x = 0 in exI) 
    by(simp add: steps.simps abc_steps_l.simps)
next
  case (Suc n)
  then obtain stp where "crsp ly (abc_steps_l (as, lm) ap n) (steps0 (s, l, r) tp stp) ires"
    by blast
  thus ?case  
    apply(cases "(abc_steps_l (as, lm) ap n)", auto)
    apply(frule_tac abc_step_red, simp)
    apply(cases "abc_fetch (fst (abc_steps_l (as, lm) ap n)) ap", simp add: abc_step_l.simps, auto)
    apply(cases "steps (s, l, r) (tp, 0) stp", simp)
    using assms
    apply(drule_tac s = "fst (steps0 (s, l, r) (tm_of ap) stp)"
        and l = "fst (snd (steps0 (s, l, r) (tm_of ap) stp))"
        and r = "snd (snd (steps0 (s, l, r) (tm_of ap) stp))" in crsp_step, auto)
    by (metis steps_add)
qed


lemma tp_correct': 
  assumes layout: "ly = layout_of ap"
    and compile: "tp = tm_of ap"
    and crsp: "crsp ly (0, lm) (Suc 0, l, r) ires"
    and abc_halt: "abc_steps_l (0, lm) ap stp = (length ap, am)"
  shows "\<exists> stp k. steps (Suc 0, l, r) (tp, 0) stp = (start_of ly (length ap), Bk # Bk # ires, <am> @ Bk\<up>k)"
  using assms
  apply(drule_tac n = stp in crsp_steps, auto)
  apply(rename_tac stpA)
  apply(rule_tac x = stpA in exI)
  apply(case_tac "steps (Suc 0, l, r) (tm_of ap, 0) stpA", simp add: crsp.simps)
  done

text\<open>The tp @ [(Nop, 0), (Nop, 0)] is nomoral turing machines, so we can use Hoare\_plus when composing with Mop machine\<close>

lemma layout_id_cons: "layout_of (ap @ [p]) = layout_of ap @ [length_of p]"
  apply(simp add: layout_of.simps)
  done

lemma map_start_of_layout[simp]:  
  "map (start_of (layout_of xs @ [length_of x])) [0..<length xs] =  (map (start_of (layout_of xs)) [0..<length xs])"
  apply(auto)
  apply(simp add: layout_of.simps start_of.simps)
  done

lemma tpairs_id_cons: 
  "tpairs_of (xs @ [x]) = tpairs_of xs @ [(start_of (layout_of (xs @ [x])) (length xs), x)]"
  apply(auto simp: tpairs_of.simps layout_id_cons )
  done

lemma map_length_ci:
  "(map (length \<circ> (\<lambda>(xa, y). ci (layout_of xs @ [length_of x]) xa y)) (tpairs_of xs)) = 
  (map (length \<circ> (\<lambda>(x, y). ci (layout_of xs) x y)) (tpairs_of xs)) "
  apply(auto simp: ci.simps adjust.simps) apply(rename_tac A B)
  apply(case_tac B, auto simp: ci.simps adjust.simps)
  done

lemma length_tp'[simp]: 
  "\<lbrakk>ly = layout_of ap; tp = tm_of ap\<rbrakk> \<Longrightarrow>
       length tp = 2 * sum_list (take (length ap) (layout_of ap))"
proof(induct ap arbitrary: ly tp rule: rev_induct)
  case Nil
  thus "?case"
    by(simp add: tms_of.simps tm_of.simps tpairs_of.simps)
next
  fix x xs ly tp
  assume ind: "\<And>ly tp. \<lbrakk>ly = layout_of xs; tp = tm_of xs\<rbrakk> \<Longrightarrow> 
    length tp = 2 * sum_list (take (length xs) (layout_of xs))"
    and layout: "ly = layout_of (xs @ [x])"
    and tp: "tp = tm_of (xs @ [x])"
  obtain ly' where a: "ly' = layout_of xs"
    by metis
  obtain tp' where b: "tp' = tm_of xs"
    by metis
  have c: "length tp' = 2 * sum_list (take (length xs) (layout_of xs))"
    using a b
    by(erule_tac ind, simp)
  thus "length tp = 2 * 
    sum_list (take (length (xs @ [x])) (layout_of (xs @ [x])))"
    using tp b
    apply(auto simp: layout_id_cons tm_of.simps tms_of.simps length_concat tpairs_id_cons map_length_ci)
    apply(cases x)
      apply(auto simp: ci.simps tinc_b_def tdec_b_def length_findnth adjust.simps length_of.simps
        split: abc_inst.splits)
    done
qed

lemma length_tp:
  "\<lbrakk>ly = layout_of ap; tp = tm_of ap\<rbrakk> \<Longrightarrow> 
  start_of ly (length ap) = Suc (length tp div 2)"
  apply(frule_tac length_tp', simp_all)
  apply(simp add: start_of.simps)
  done

lemma compile_correct_halt: 
  assumes layout: "ly = layout_of ap"
    and compile: "tp = tm_of ap"
    and crsp: "crsp ly (0, lm) (Suc 0, l, r) ires"
    and abc_halt: "abc_steps_l (0, lm) ap stp = (length ap, am)"
    and rs_loc: "n < length am"
    and rs: "abc_lm_v am n = rs"
    and off: "off = length tp div 2"
  shows "\<exists> stp i j. steps (Suc 0, l, r) (tp @ shift (mopup n) off, 0) stp = (0, Bk\<up>i @ Bk # Bk # ires, Oc\<up>Suc rs @ Bk\<up>j)"
proof -
  have "\<exists> stp k. steps (Suc 0, l, r) (tp, 0) stp = (Suc off, Bk # Bk # ires, <am> @ Bk\<up>k)"
    using assms tp_correct'[of ly ap tp lm l r ires stp am]
    by(simp add: length_tp)
  then obtain stp k where "steps (Suc 0, l, r) (tp, 0) stp = (Suc off, Bk # Bk # ires, <am> @ Bk\<up>k)"
    by blast
  then have a: "steps (Suc 0, l, r) (tp@shift (mopup n) off , 0) stp = (Suc off, Bk # Bk # ires, <am> @ Bk\<up>k)"
    using assms
    by(auto intro: tm_append_first_steps_eq)
  have "\<exists> stp i j. (steps (Suc 0, Bk # Bk # ires, <am> @ Bk \<up> k) (mopup_a n @ shift mopup_b (2 * n), 0) stp)
    = (0, Bk\<up>i @ Bk # Bk # ires, Oc # Oc\<up> rs @ Bk\<up>j)"
    using assms
    by(rule_tac mopup_correct, auto simp: abc_lm_v.simps)
  then obtain stpb i j where 
    "steps (Suc 0, Bk # Bk # ires, <am> @ Bk \<up> k) (mopup_a n @ shift mopup_b (2 * n), 0) stpb
    = (0, Bk\<up>i @ Bk # Bk # ires, Oc # Oc\<up> rs @ Bk\<up>j)" by blast
  then have b: "steps (Suc 0 + off, Bk # Bk # ires, <am> @ Bk \<up> k) (tp @ shift (mopup n) off, 0) stpb
    = (0, Bk\<up>i @ Bk # Bk # ires, Oc # Oc\<up> rs @ Bk\<up>j)"
    using assms wf_mopup
    apply(drule_tac tm_append_second_halt_eq, auto)
    done
  from a b show "?thesis"
    by(rule_tac x = "stp + stpb" in exI, simp add: steps_add)
qed

declare mopup.simps[simp del]
lemma abc_step_red2:
  "abc_steps_l (s, lm) p (Suc n) = (let (as', am') = abc_steps_l (s, lm) p n in
                                    abc_step_l (as', am') (abc_fetch as' p))"
  apply(cases "abc_steps_l (s, lm) p n", simp)
  apply(drule_tac abc_step_red, simp)
  done

lemma crsp_steps2:
  assumes 
    layout: "ly = layout_of ap"
    and compile: "tp = tm_of ap"
    and crsp: "crsp ly (0, lm) (Suc 0, l, r) ires"
    and nothalt: "as < length ap"
    and aexec: "abc_steps_l (0, lm) ap stp = (as, am)"
  shows "\<exists>stpa\<ge>stp. crsp ly (as, am) (steps (Suc 0, l, r) (tp, 0) stpa) ires"
  using nothalt aexec
proof(induct stp arbitrary: as am)
  case 0
  thus "?case"
    using crsp
    by(rule_tac x = 0 in exI, auto simp: abc_steps_l.simps steps.simps crsp)
next
  case (Suc stp as am)
  have ind: 
    "\<And> as am.  \<lbrakk>as < length ap; abc_steps_l (0, lm) ap stp = (as, am)\<rbrakk> 
    \<Longrightarrow> \<exists>stpa\<ge>stp. crsp ly (as, am) (steps (Suc 0, l, r) (tp, 0) stpa) ires" by fact
  have a: "as < length ap" by fact
  have b: "abc_steps_l (0, lm) ap (Suc stp) = (as, am)" by fact
  obtain as' am' where c: "abc_steps_l (0, lm) ap stp = (as', am')" 
    by(cases "abc_steps_l (0, lm) ap stp", auto)
  then have d: "as' < length ap"
    using a b
    by(simp add: abc_step_red2, cases "as' < length ap", simp,
        simp add: abc_fetch.simps abc_steps_l.simps abc_step_l.simps)
  have "\<exists>stpa\<ge>stp. crsp ly (as', am') (steps (Suc 0, l, r) (tp, 0) stpa) ires"
    using d c ind by simp
  from this obtain stpa where e: 
    "stpa \<ge> stp \<and>  crsp ly (as', am') (steps (Suc 0, l, r) (tp, 0) stpa) ires"
    by blast
  obtain s' l' r' where f: "steps (Suc 0, l, r) (tp, 0) stpa = (s', l', r')"
    by(cases "steps (Suc 0, l, r) (tp, 0) stpa", auto)
  obtain ins where g: "abc_fetch as' ap = Some ins" using d 
    by(cases "abc_fetch as' ap",auto simp: abc_fetch.simps)
  then have "\<exists>stp> (0::nat). crsp ly (abc_step_l (as', am') (Some ins)) 
    (steps (s', l', r') (tp, 0) stp) ires "
    using layout compile e f 
    by(rule_tac crsp_step, simp_all)
  then obtain stpb where "stpb > 0 \<and> crsp ly (abc_step_l (as', am') (Some ins)) 
    (steps (s', l', r') (tp, 0) stpb) ires" ..
  from this show "?case" using b e g f c
    by(rule_tac x = "stpa + stpb" in exI, simp add: steps_add abc_step_red2)
qed

lemma compile_correct_unhalt: 
  assumes layout: "ly = layout_of ap"
    and compile: "tp = tm_of ap"
    and crsp: "crsp ly (0, lm) (1, l, r) ires"
    and off: "off = length tp div 2"
    and abc_unhalt: "\<forall> stp. (\<lambda> (as, am). as < length ap) (abc_steps_l (0, lm) ap stp)"
  shows "\<forall> stp.\<not> is_final (steps (1, l, r) (tp @ shift (mopup n) off, 0) stp)"
  using assms
proof(rule_tac allI, rule_tac notI)
  fix stp
  assume h: "is_final (steps (1, l, r) (tp @ shift (mopup n) off, 0) stp)"
  obtain as am where a: "abc_steps_l (0, lm) ap stp = (as, am)"
    by(cases "abc_steps_l (0, lm) ap stp", auto)
  then have b: "as < length ap"
    using abc_unhalt
    by(erule_tac x = stp in allE, simp)
  have "\<exists> stpa\<ge>stp. crsp ly (as, am) (steps (1, l, r) (tp, 0) stpa) ires "
    using assms b a
    apply(simp add: numeral)
    apply(rule_tac crsp_steps2)
        apply(simp_all)
    done
  then obtain stpa where 
    "stpa\<ge>stp \<and> crsp ly (as, am) (steps (1, l, r) (tp, 0) stpa) ires" ..
  then obtain s' l' r' where b: "(steps (1, l, r) (tp, 0) stpa) = (s', l', r') \<and> 
       stpa\<ge>stp \<and> crsp ly (as, am) (s', l', r') ires"
    by(cases "steps (1, l, r) (tp, 0) stpa", auto)
  hence c:
    "(steps (1, l, r) (tp @ shift (mopup n) off, 0) stpa) = (s', l', r')"
    by(rule_tac tm_append_first_steps_eq, simp_all add: crsp.simps)
  from b have d: "s' > 0 \<and> stpa \<ge> stp"
    by(simp add: crsp.simps)
  then obtain diff where e: "stpa = stp + diff" by (metis le_iff_add)
  obtain s'' l'' r'' where f:
    "steps (1, l, r) (tp @ shift (mopup n) off, 0) stp = (s'', l'', r'') \<and> is_final (s'', l'', r'')"
    using h
    by(cases "steps (1, l, r) (tp @ shift (mopup n) off, 0) stp", auto)

  then have "is_final (steps (s'', l'', r'') (tp @ shift (mopup n) off, 0) diff)"
    by(auto intro: after_is_final)
  then have "is_final (steps (1, l, r) (tp @ shift (mopup n) off, 0) stpa)"
    using e f by simp
  from this and c d show "False" by simp
qed

end

