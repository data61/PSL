section \<open>Concrete example\<close>

theory Refinement_Example
imports Refinement
begin

text \<open>In this section, we present a concrete example ofthe use of our environment.
We define two Circus processes FIG and DFIG, using our syntax. we give the proof of refinement 
(simulation) of the first processby the second one using the simulation function $Sim$.\<close>

subsection \<open>Process definitions\<close>

circus_process FIG =
  alphabet = [v::nat, x::nat]
  state = [idS::"nat set"]
  channel = [out nat , req , ret nat]
  schema Init = "idS' = {}"
  schema Out = "\<exists> a. v' = a \<and> a \<notin> idS \<and> idS' = idS \<union> {v'}"
  schema Remove = "x \<in> idS \<and> idS' = idS - {x}"
  where "var v \<bullet> (Schema FIG.Init`;`
         \<mu> X \<bullet> (((((req \<rightarrow> (Schema FIG.Out))`;` out`!`(hd o v) \<rightarrow> Skip))
               \<box> (ret`?`x \<rightarrow> (Schema FIG.Remove)))`;` X))"


circus_process DFIG =
  alphabet = [v::nat, x::nat]
  state = [retidS::"nat set", max::nat]
  channel = FIG_channels
  schema Init = "retidS' = {} \<and> max' = 0"
  schema Out = "v' = max \<and> max' = (max + 1) \<and> retidS' = retidS - {v'}"
  schema Remove = "x < max \<and> retidS' = retidS \<union> {x} \<and> max' = max"
  where "var v \<bullet> (Schema DFIG.Init`;`
         \<mu> X \<bullet> ((((req \<rightarrow> (Schema DFIG.Out))`;` (out`!`(hd o v) \<rightarrow> Skip))
               \<box> (ret`?`x \<rightarrow> (Schema DFIG.Remove)))`;` X))"


definition Sim where
  "Sim A = FIG_alphabet.make (DFIG_alphabet.v A) (DFIG_alphabet.x A)
   ({a. a < (DFIG_alphabet.max A) \<and> a \<notin> (DFIG_alphabet.retidS A)})"

subsection \<open>Simulation proofs\<close>

text \<open>For the simulation proof, we give first proofs for simulation over the schema expressions.
The proof is then given over the main actions of the processes.\<close>

lemma SimInit: "(Schema FIG.Init) \<preceq>Sim (Schema DFIG.Init)"
  apply (auto simp: Sim_def Pre_def design_defs DFIG.Init_def FIG.Init_def rp_defs  alpha_rp.defs
                    DFIG_alphabet.defs FIG_alphabet.defs intro!: Schema_Sim)
  apply (rule_tac x="A\<lparr>max := 0, retidS := {}\<rparr>" in exI, simp)
done

lemma SimOut: "(Schema FIG.Out) \<preceq>Sim (Schema DFIG.Out)"
  apply (rule Schema_Sim)
  apply (auto simp: Pre_def DFIG_alphabet.defs FIG_alphabet.defs
                     alpha_rp.defs Sim_def FIG.Out_def DFIG.Out_def)
  apply (rule_tac x="a\<lparr>v := [DFIG_alphabet.max a], max := (Suc (DFIG_alphabet.max a)), 
                     retidS := retidS a - {DFIG_alphabet.max a}\<rparr>" in exI, simp)
  apply (rule_tac x="a\<lparr>v := [DFIG_alphabet.max a], max := (Suc (DFIG_alphabet.max a)), 
                     retidS := retidS a - {DFIG_alphabet.max a}\<rparr>" in exI, simp)
done

lemma SimRemove: "(Schema FIG.Remove) \<preceq>Sim (Schema DFIG.Remove)"
  apply (rule Schema_Sim)
  apply (auto simp: Pre_def DFIG_alphabet.defs FIG_alphabet.defs alpha_rp.defs Sim_def)
  apply (clarsimp simp add: DFIG.Remove_def FIG.Remove_def)
  apply (rule_tac x="a\<lparr>retidS := insert (hd (DFIG_alphabet.x a)) (retidS a)\<rparr>" in exI, simp)
  apply (auto simp add: DFIG.Remove_def FIG.Remove_def)
done

lemma "FIG.FIG \<preceq>Sim DFIG.DFIG"
by (auto simp: DFIG.DFIG_def FIG.FIG_def mono_Seq SimRemove SimOut SimInit Sim_def FIG_alphabet.defs
         intro!:Var_Sim Seq_Sim Mu_Sim Det_Sim Write0_Sim Write_Sim Read_Sim Skip_Sim)

end
