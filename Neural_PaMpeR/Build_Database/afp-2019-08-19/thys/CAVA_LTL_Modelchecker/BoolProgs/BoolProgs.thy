section \<open>Boolean Programs\<close>
theory BoolProgs
imports 
  CAVA_Base.CAVA_Base
begin

subsection \<open>Syntax and Semantics\<close>

datatype bexp = TT | FF | V nat | Not bexp | And bexp bexp | Or bexp bexp

type_synonym state = "bitset"

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval TT s = True" |
"bval FF s = False" |
"bval (V n) s = bs_mem n s" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b\<^sub>1 b\<^sub>2) s = (bval b\<^sub>1 s & bval b\<^sub>2 s)" |
"bval (Or b\<^sub>1 b\<^sub>2) s = (bval b\<^sub>1 s | bval b\<^sub>2 s)"

datatype instr =
  AssI "nat list" "bexp list" |
  TestI bexp int |
  ChoiceI "(bexp * int) list" |
  GotoI int

type_synonym config = "nat * state"
type_synonym bprog = "instr array"

text \<open>
  Semantics Notice:
  To be equivalent in semantics with SPIN, there is no such thing as a
  finite run:
  \begin{itemize}
    \item Deadlocks (i.e. empty Choice) are self-loops
    \item program termination is self-loop
  \end{itemize}
\<close>

fun exec :: "instr \<Rightarrow> config \<Rightarrow> config list" where
"exec instr (pc,s) = (case instr of
  AssI ns bs \<Rightarrow> let bvs = zip ns (map (\<lambda>b. bval b s) bs) in
               [(pc + 1, foldl (\<lambda>s (n,bv). set_bit s n bv) s bvs)] |
  TestI b d \<Rightarrow> [if bval b s then (pc+1, s) else (nat(int(pc+1)+d), s)] |
  ChoiceI bis \<Rightarrow> let succs = [(nat(int(pc+1)+i), s) . (b,i) <- bis, bval b s] 
                in if succs = [] then [(pc,s)] else succs |
  GotoI d \<Rightarrow> [(nat(int(pc+1)+d),s)])"

(* exec' is merely a stuttering optimization. It summarizes chains of choices
  or jumps, as long as they go forward in the program. The forward-condition is
  to ensure termination. 

  TODO: Make this explicit, and prove stuttering equivalence!
*)
function exec' :: "bprog \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> nat list" where
"exec' ins s pc = (
  if pc < array_length ins then (
    case (array_get ins pc) of
      AssI ns bs \<Rightarrow> [pc] |
      TestI b d \<Rightarrow> (
        if bval b s then exec' ins s (pc+1) 
        else let pc'=(nat(int(pc+1)+d)) in if pc'>pc then exec' ins s pc'
        else [pc']
      ) |
      ChoiceI bis \<Rightarrow> let succs = [(nat(int(pc+1)+i)) . (b,i) <- bis, bval b s]
                    in if succs = [] then [pc] else concat (map (\<lambda>pc'. if pc'>pc then exec' ins s pc' else [pc']) succs) |
      GotoI d \<Rightarrow> let pc' = nat(int(pc+1)+d) in (if pc'>pc then exec' ins s pc' else [pc'])
  ) else [pc]
)"
by pat_completeness auto
termination 
  apply (relation "measure (%(ins,s,pc). array_length ins - pc)")
  apply auto
  done

fun nexts1 :: "bprog \<Rightarrow> config \<Rightarrow> config list" where
"nexts1 ins (pc,s) = (
  if pc < array_length ins then 
    exec (array_get ins pc) (pc,s) 
  else 
    [(pc,s)])"

fun nexts :: "bprog \<Rightarrow> config \<Rightarrow> config list" where
  "nexts ins (pc,s) = concat (
    map 
      (\<lambda>(pc,s). map (\<lambda>pc. (pc,s)) (exec' ins s pc)) 
      (nexts1 ins (pc,s))
  )"

declare nexts.simps [simp del]

datatype
  com = SKIP
      | Assign "nat list" "bexp list"    
      | Seq    com  com         
      | GC  "(bexp * com)list"  
      | IfTE  bexp com com      
      | While  bexp com         

locale BoolProg_Syntax begin
  notation 
        Assign       ("_ ::= _" [999, 61] 61)
    and Seq          ("_;/ _"  [60, 61] 60)
    and GC           ("IF _ FI")
    and IfTE         ("(IF _/ THEN _/ ELSE _)"  [0, 61, 61] 61)
    and While        ("(WHILE _/ DO _)"  [0, 61] 61)
end

context begin interpretation BoolProg_Syntax .
fun comp' :: "com \<Rightarrow> instr list" where
"comp' SKIP = []" |
"comp' (Assign n b) = [AssI n b]" |
"comp' (c1;c2) = comp' c1 @ comp' c2" |
"comp' (IF gcs FI) =
  (let cgcs = map (\<lambda>(b,c). (b,comp' c)) gcs in
   let addbc = (\<lambda>(b,cc) (bis,ins).
         let cc' = cc @ (if ins = [] then [] else [GotoI (int(length ins))]) in
         let bis' = map (\<lambda>(b,i). (b, i + int(length cc'))) bis
         in ((b,0)#bis', cc' @ ins)) in
   let (bis,ins) = foldr addbc cgcs ([],[])
   in ChoiceI bis # ins)" |
"comp' (IF b THEN c1 ELSE c2) =
  (let ins1 = comp' c1 in let ins2 = comp' c2 in
   let i1 = int(length ins1 + 1) in let i2 = int(length ins2)
   in TestI b i1 # ins1 @ GotoI i2 # ins2)" |
"comp' (WHILE b DO c) =
  (let ins = comp' c in
   let i = int(length ins + 1)
   in TestI b i # ins @ [GotoI (-(i+1))])"

(* a test: *)
value "comp' (IF [(V 0, [1,0] ::= [TT, FF]), (V 1, [0] ::= [TT])] FI)"

end

definition comp :: "com \<Rightarrow> bprog" where
  "comp = array_of_list \<circ> comp'"

(* 
  Optimization

- Gotos: Resolve Goto-Chains: If a Goto referres to another Goto -- add the second offset to the first one. 
                              If a Goto has a negative offset ignore it, to avoid problems with loops.

*)

fun opt' where
  "opt' (GotoI d) ys = (let next = \<lambda>i. (case i of GotoI d \<Rightarrow> d + 1 | _ \<Rightarrow> 0)
                        in if d < 0 \<or> nat d \<ge> length ys then (GotoI d)#ys
                           else let d' = d + next (ys ! nat d)
                           in (GotoI d' # ys))"
| "opt' x ys = x#ys"

definition opt :: "instr list \<Rightarrow> instr list" where
  "opt instr = foldr opt' instr []"

definition optcomp :: "com \<Rightarrow> bprog" where
  "optcomp \<equiv> array_of_list \<circ> opt \<circ> comp'"

subsection \<open>Finiteness of reachable configurations\<close>

inductive_set reachable_configs
  for bp :: bprog
  and c\<^sub>s :: config \<comment> \<open>start configuration\<close>
where
"c\<^sub>s \<in> reachable_configs bp c\<^sub>s" |
"c \<in> reachable_configs bp c\<^sub>s \<Longrightarrow> x \<in> set (nexts bp c) \<Longrightarrow> x \<in> reachable_configs bp c\<^sub>s"

lemmas reachable_configs_induct = reachable_configs.induct[split_format(complete),case_names 0 1]

fun offsets :: "instr \<Rightarrow> int set" where
"offsets (AssI _ _) = {0}" |
"offsets (TestI _ i) = {0,i}" |
"offsets (ChoiceI bis) = set(map snd bis) \<union> {0}" |
"offsets (GotoI i) = {i}"

definition offsets_is :: "instr list \<Rightarrow> int set" where
"offsets_is ins = (UN instr : set ins. offsets instr)"

definition max_next_pcs :: "instr list \<Rightarrow> nat set" where
"max_next_pcs ins = {nat(int(length ins + 1) + i) |i. i : offsets_is ins}"


lemma finite_max_next_pcs: "finite(max_next_pcs bp)"
proof-
  { fix instr have "finite (offsets instr)" by(cases instr) auto }
  moreover
  { fix ins have "max_next_pcs ins = (UN i : offsets_is ins. {nat(int(length ins + 1) + i)})"
    by(auto simp add: max_next_pcs_def) }
  ultimately show ?thesis by(auto simp add: offsets_is_def)
qed

(* TODO: Move *)
lemma (in linorder) le_Max_insertI1: "\<lbrakk> finite A; x \<le> b \<rbrakk> \<Longrightarrow> x \<le> Max (insert b A)"
by (metis Max_ge finite.insertI insert_iff order_trans)
lemma (in linorder) le_Max_insertI2: "\<lbrakk> finite A; A \<noteq> {}; x \<le> Max A \<rbrakk> \<Longrightarrow> x \<le> Max (insert b A)"
by(auto simp add: max_def not_le simp del: Max_less_iff)

lemma max_next_pcs_not_empty:
  "pc<length bp \<Longrightarrow> x : set (exec (bp!pc) (pc,s)) \<Longrightarrow> max_next_pcs bp \<noteq> {}"
apply(drule nth_mem)
apply(fastforce simp: max_next_pcs_def offsets_is_def split: instr.splits)
done

lemma Max_lem2: 
  assumes "pc < length bp" 
  and "(pc', s') \<in> set (exec (bp!pc) (pc, s))"
  shows "pc' \<le> Max (max_next_pcs bp)"
using assms
proof (cases "bp ! pc")
  case (ChoiceI l)
  show ?thesis
  proof (cases "pc' = pc")
    case True with assms ChoiceI show ?thesis
      by (auto simp: Max_ge_iff max_next_pcs_not_empty finite_max_next_pcs) 
         (force simp add: max_next_pcs_def offsets_is_def dest: nth_mem)
  next
    case False with ChoiceI assms obtain b i where 
      bi: "bval b s" "(b,i) \<in> set l" "pc' = nat(int(pc+1)+i)"
      by (auto split: if_split_asm)
    with ChoiceI assms have "i \<in> \<Union>(offsets ` (set bp))" by (force dest: nth_mem)
    with bi assms have "\<exists>a. (a \<in> max_next_pcs bp \<and> pc' \<le> a)"
      unfolding max_next_pcs_def offsets_is_def by force
    thus ?thesis 
      by (auto simp: Max_ge_iff max_next_pcs_not_empty[OF assms] finite_max_next_pcs) 
    qed
qed (auto simp: Max_ge_iff max_next_pcs_not_empty finite_max_next_pcs,
     (force simp add: max_next_pcs_def offsets_is_def dest: nth_mem split: if_split_asm)+)

lemma Max_lem1: "\<lbrakk> pc < length bp; (pc', s') \<in> set (exec (bp ! pc) (pc, s))\<rbrakk>
    \<Longrightarrow> pc' \<le> Max (insert x (max_next_pcs bp))"
  apply(rule le_Max_insertI2)
  apply (simp add: finite_max_next_pcs)
  apply(simp add: max_next_pcs_not_empty)
  apply(auto intro!: Max_lem2 simp del:exec.simps)
  done

definition "pc_bound bp \<equiv> max 
    (Max (max_next_pcs (list_of_array bp)) + 1)
    (array_length bp + 1)"

declare exec'.simps[simp del]

lemma [simp]: "length (list_of_array a) = array_length a" by (cases a) auto

lemma aux2: 
  assumes A: "pc < array_length ins" 
  assumes B: "ofs \<in> offsets_is (list_of_array ins)"
  shows "nat (1 + int pc + ofs) < pc_bound ins"
proof -
  have "nat (int (1 + array_length ins) + ofs) 
    \<in> max_next_pcs (list_of_array ins)"
    using B unfolding max_next_pcs_def
    by auto
  with A show ?thesis
    unfolding pc_bound_def
    apply -
    apply (rule max.strict_coboundedI1)
    apply auto
    apply (drule Max_ge[OF finite_max_next_pcs])
    apply simp
    done
qed

lemma array_idx_in_set: 
  "\<lbrakk> pc < array_length ins; array_get ins pc = x \<rbrakk> 
  \<Longrightarrow> x \<in> set (list_of_array ins)"
  by (induct ins) auto

lemma rcs_aux: 
  assumes "pc < pc_bound bp"    
  assumes "pc'\<in>set (exec' bp s pc)"
  shows "pc' < pc_bound bp"
  using assms
proof (induction bp s pc arbitrary: pc' rule: exec'.induct[case_names C])
  case (C ins s pc pc')
  from C.prems show ?case
    apply (subst (asm) exec'.simps)
    apply (split if_split_asm instr.split_asm)+
    apply (simp add: pc_bound_def)

    apply (simp split: if_split_asm add: Let_def)
    apply (frule (2) C.IH(1), auto) []
    apply (auto simp: pc_bound_def) []
    apply (frule (2) C.IH(2), auto) []
    apply (rename_tac bexp int)
    apply (subgoal_tac "int \<in> offsets_is (list_of_array ins)")
    apply (blast intro: aux2)
    apply (auto simp: offsets_is_def) []
    apply (rule_tac x="TestI bexp int" in bexI, auto simp: array_idx_in_set) []

    apply (rename_tac list)
    apply (clarsimp split: if_split_asm simp add: Let_def)
    apply (elim disjE conjE, auto) []
    apply (frule (1) C.IH(3), auto) []
    apply (force)
    apply (force)
    apply (subgoal_tac "ba \<in> offsets_is (list_of_array ins)")
    apply (blast intro: aux2)
    apply (auto simp: offsets_is_def) []
    apply (rule_tac x="ChoiceI list" in bexI, auto simp: array_idx_in_set) []

    apply (rename_tac int)
    apply (simp split: if_split_asm add: Let_def)
    apply (frule (1) C.IH(4), auto) []
    apply (subgoal_tac "int \<in> offsets_is (list_of_array ins)")
    apply (blast intro: aux2)
    apply (auto simp: offsets_is_def) []
    apply (rule_tac x="GotoI int" in bexI, auto simp: array_idx_in_set) []
    
    apply simp
    done
qed


primrec bexp_vars :: "bexp \<Rightarrow> nat set" where
  "bexp_vars TT = {}"
| "bexp_vars FF = {}"
| "bexp_vars (V n) = {n}"
| "bexp_vars (Not b) = bexp_vars b"
| "bexp_vars (And b1 b2) = bexp_vars b1 \<union> bexp_vars b2"
| "bexp_vars (Or b1 b2) = bexp_vars b1 \<union> bexp_vars b2"

primrec instr_vars :: "instr \<Rightarrow> nat set" where
  "instr_vars (AssI xs bs) = set xs \<union> \<Union>(bexp_vars`set bs)"
| "instr_vars (TestI b _) = bexp_vars b"
| "instr_vars (ChoiceI cs) = \<Union>(bexp_vars`fst`set cs)"
| "instr_vars (GotoI _) = {}"

find_consts "'a array \<Rightarrow> 'a list"

definition bprog_vars :: "bprog \<Rightarrow> nat set" where 
  "bprog_vars bp = \<Union>(instr_vars`set (list_of_array bp))"


definition "state_bound bp s0 
  \<equiv> {s. bs_\<alpha> s - bprog_vars bp = bs_\<alpha> s0 - bprog_vars bp}"
abbreviation "config_bound bp s0 \<equiv> {0..< pc_bound bp} \<times> state_bound bp s0"

lemma exec_bound:
  assumes PCB: "pc < array_length bp"
  assumes SB: "s \<in> state_bound bp s0"
  shows "set (exec (array_get bp pc) (pc,s)) \<subseteq> config_bound bp s0"
proof (clarsimp simp del: exec.simps, intro conjI)
 
  obtain instrs where BP_eq[simp]: "bp = Array instrs" by (cases bp)
  from PCB have PCB'[simp]: "pc < length instrs" by simp

  fix pc' s'
  assume STEP: "(pc',s') \<in> set (exec (array_get bp pc) (pc,s))"
  hence STEP': "(pc',s') \<in> set (exec (instrs!pc) (pc,s))" by simp

  show "pc' < pc_bound bp"
    using Max_lem2[OF PCB' STEP']
    unfolding pc_bound_def by simp

  show "s' \<in> state_bound bp s0"
    using STEP' SB
  proof (cases "instrs!pc")
    case (AssI xs vs)

    have "set xs \<subseteq> instr_vars (instrs!pc)"
      by (simp add: AssI)
    also have "\<dots> \<subseteq> bprog_vars bp"
      apply (simp add: bprog_vars_def)
      by (metis PCB' UN_upper nth_mem)
    finally have XSB: "set xs \<subseteq> bprog_vars bp" .


    { 
      fix x s v
      assume A: "x \<in> bprog_vars bp" "s \<in> state_bound bp s0"

      have SB_CNV: "bs_\<alpha> (set_bit s x v) 
        = (if v then (insert x (bs_\<alpha> s)) else (bs_\<alpha> s - {x}))"
        apply (cases v)
        apply simp_all
        apply (fold bs_insert_def bs_delete_def)
        apply (simp_all add: bs_correct)
        done

      from A have "set_bit s x v \<in> state_bound bp s0"
        unfolding state_bound_def
        by (auto simp: SB_CNV)
    } note aux=this

    {
      fix vs
      have "foldl (\<lambda>s (x, y). set_bit s x y) s (zip xs vs) 
        \<in> state_bound (Array instrs) s0"
        using SB XSB
        apply (induct xs arbitrary: vs s)
        apply simp
        apply (case_tac vs)
        apply simp
        using aux
        apply (auto)
        done
    } note aux2=this

    thus ?thesis using STEP'
      by (simp add: AssI)
  qed (auto split: if_split_asm)
qed

lemma in_bound_step: 
  notes [simp del] = exec.simps
  assumes BOUND: "c \<in> config_bound bp s0"
  assumes STEP: "c'\<in>set (nexts bp c)"
  shows "c' \<in> config_bound bp s0"
  using BOUND STEP
  apply (cases c)
  apply (auto 
    simp add: nexts.simps 
    split: if_split_asm)
  apply (frule (2) exec_bound[THEN subsetD])
  apply clarsimp
  apply (frule (1) rcs_aux)
  apply simp

  apply (frule (2) exec_bound[THEN subsetD])
  apply clarsimp
  
  apply (frule (1) rcs_aux)
  apply simp
  done

lemma reachable_configs_in_bound:
  "c \<in> config_bound bp s0 \<Longrightarrow> reachable_configs bp c \<subseteq> config_bound bp s0"
proof 
  fix c'
  assume "c' \<in> reachable_configs bp c" "c \<in> config_bound bp s0" 
  thus "c' \<in> config_bound bp s0"
    apply induction
    apply simp
    by (rule in_bound_step)
qed
    
lemma reachable_configs_out_of_bound: "(pc',s')\<in>reachable_configs bp (pc,s) 
  \<Longrightarrow> \<not> pc < pc_bound bp \<Longrightarrow> (pc',s') = (pc,s)"
proof (induct rule: reachable_configs_induct)
  case (1 pc' s' pc'' s'')
  hence [simp]: "pc'=pc" "s'=s" by auto
  from 1(4) have "\<not> pc < array_length bp" unfolding pc_bound_def by auto
  with 1(3) show ?case
    by (auto simp add: nexts.simps exec'.simps)
qed auto

lemma finite_bexp_vars[simp, intro!]: "finite (bexp_vars be)"
  by (induction be) auto

lemma finite_instr_vars[simp, intro!]: "finite (instr_vars ins)"
  by (cases ins) auto

lemma finite_bprog_vars[simp, intro!]: "finite (bprog_vars bp)"
  unfolding bprog_vars_def by simp

lemma finite_state_bound[simp, intro!]: "finite (state_bound bp s0)"
  unfolding state_bound_def
  apply (rule finite_imageD[where f=bs_\<alpha>])
  apply (rule finite_subset[where 
    B = "{s. s - bprog_vars bp = bs_\<alpha> s0 - bprog_vars bp}"])
  apply auto []
  apply (rule finite_if_eq_beyond_finite)
  apply simp

  apply (rule inj_onI)
  apply (fold bs_eq_def)
  apply (auto simp: bs_eq_correct)
  done

lemma finite_config_bound[simp, intro!]: "finite (config_bound bp s0)"
  by blast

lemma reachable_configs_finite[simp, intro!]: 
  "finite (reachable_configs bp c)"
proof (cases c, clarsimp)
  fix pc s
  show "finite (reachable_configs bp (pc, s))"
  proof (cases "pc < pc_bound bp")
    case False from reachable_configs_out_of_bound[OF _ False, where s=s]
    have "reachable_configs bp (pc, s) \<subseteq> {(pc,s)}" by auto
    thus ?thesis by (rule finite_subset) auto
  next
    case True
    hence "(pc,s) \<in> config_bound bp s"
      by (simp add: state_bound_def)
    thus ?thesis
      by (rule finite_subset[OF reachable_configs_in_bound]) simp
  qed
qed

definition "bpc_is_run bpc r \<equiv> let (bp,c)=bpc in r 0 = c \<and> (\<forall>i. r (Suc i) \<in> set (BoolProgs.nexts bp (r i)))"
definition "bpc_props c \<equiv> bs_\<alpha> (snd c)"
definition "bpc_lang bpc \<equiv> {bpc_props o r | r. bpc_is_run bpc r}"

(* Printing *)
(*definition print_list where
  "print_list f sep s = (let f' = (\<lambda>str s. if str = [] then f s
                                       else str @ sep @ f s)
                     in ''['' @ (foldl f' [] s) @ '']'')"

fun bool_list_to_prop_list where
  "bool_list_to_prop_list _ [] props = props"
| "bool_list_to_prop_list n (x#xs) props = (let props' = if x then n#props else props 
                                            in bool_list_to_prop_list (Suc n) xs props')"
*)

fun print_config :: 
  "(nat \<Rightarrow> string) \<Rightarrow> (bitset \<Rightarrow> string) \<Rightarrow> config \<Rightarrow> string" where
  "print_config f fx (p,s) = f p @ '' '' @ fx s"

end
