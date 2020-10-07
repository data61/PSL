(*  Title:      Presburger-Automata/Exec.thy
    Author:     Stefan Berghofer, TU Muenchen, 2008-2009
*)

theory Exec
imports Presburger_Automata "HOL-Library.Code_Target_Numeral"
begin

declare gen_dfs_simps [code]

lemma [code_unfold]: "(\<longrightarrow>) = (\<lambda>P. (\<or>) (\<not> P))"
  by (simp add: fun_eq_iff)

lemma "\<forall>x. (\<exists>xa. int xa - int x = 5) \<or> (\<forall>xa xb. \<not> 6 \<le> int xb \<longrightarrow> int xb + (6 * int xa - int x) = 0 \<longrightarrow> int xa = 1)"
proof -
  have "?thesis = eval_pf (Forall (Exist (Or (Eq [1, -1] 5)
    (Forall (Forall (Imp (Neg (Le [-1, 0] (- 6))) (Imp (Eq [1, 6, 0, -1] 0) (Eq [0, 1] 1)))))))) []"
    (is "_ = eval_pf ?P []")
    by simp
  also have "\<dots> = dfa_accepts (dfa_of_pf 0 ?P) []"
    by (simp add: dfa_of_pf_correctness del: dfa_of_pf.simps)
  also have "\<dots>" by eval
  finally show ?thesis .
qed

lemma "\<forall>x xa xb. \<not> 2 \<le> int xb \<longrightarrow> int xb + (2 * int xa - int x) = 1 \<longrightarrow>
  (\<forall>xb xc. \<not> 2 \<le> int xc \<longrightarrow> int xc + (2 * int xb - int x) = 0 \<longrightarrow> (\<exists>xa. 2 * int xa = int x) \<longrightarrow> xb = xa)"
proof -
  have "?thesis = eval_pf (Forall (Forall (Forall (Imp (Neg (Le [-1] (- 2)))
    (Imp (Eq [1, 2, -1] 1) (Forall (Forall (Imp (Neg (Le [-1] (- 2)))
      (Imp (Eq [1, 2, 0, 0, -1] 0) (Imp (Exist (Eq [2, 0, 0, 0, 0, -1] 0)) (Eq [0, 1, 0, -1] 0))))))))))) []"
    (is "_ = eval_pf ?P []")
    by simp
  also have "\<dots> = dfa_accepts (dfa_of_pf 0 ?P) []"
    by (simp add: dfa_of_pf_correctness del: dfa_of_pf.simps)
  also have "\<dots>" by eval
  finally show ?thesis .
qed

definition "mk_dfa = dfa_of_pf 0"

definition "stamp = Forall (Imp (Le [-1] (- 8)) (Exist (Exist (Eq [5, 3, -1] 0))))"
definition "stamp_false = Forall (Imp (Le [-1] (- 7)) (Exist (Exist (Eq [5, 3, -1] 0))))"
definition "example = Forall (Exist (Or (Eq [1, -1] 5)
  (Forall (Forall (Imp (Neg (Le [-1, 0] (- 6))) (Imp (Eq [1, 6, 0, -1] 0) (Eq [0, 1] 1)))))))"
definition "example2 = Forall (Forall (Forall (Imp (Neg (Le [-1] (- 2)))
  (Imp (Eq [1, 2, -1] 1) (Forall (Forall (Imp (Neg (Le [-1] (- 2)))
    (Imp (Eq [1, 2, 0, 0, -1] 0) (Imp (Exist (Eq [2, 0, 0, 0, 0, -1] 0)) (Eq [0, 1, 0, -1] 0))))))))))"
definition "example2_false = Forall (Forall (Forall (Imp (Neg (Le [-1] (- 2)))
  (Imp (Eq [1, 2, -1] 1) (Forall (Forall (Imp (Neg (Le [-1] (- 2)))
    (Imp (Eq [1, 2, 0, 0, -1] 0) (Imp (Exist (Eq [3, 0, 0, 0, 0, -1] 0)) (Eq [0, 1, 0, -1] 0))))))))))"
definition "harrison1 = Exist (Forall (Imp (Le [-1, 1] 0) (Exist (Exist
  (And (Le [0, -1] 0) (And (Le [-1] 0) (Eq [8, 3, -1] 0)))))))"
definition "harrison2 = Exist (Forall (Imp (Le [-1, 1] 0) (Exist (Exist
  (And (Le [0, -1] 0) (And (Le [-1] 0) (Eq [8, 7, -1] 0)))))))"

value "mk_dfa stamp"
value "min_dfa (mk_dfa stamp)"
value "mk_dfa stamp_false"
value "mk_dfa example"
value "mk_dfa example2"
value "mk_dfa example2_false"
value "mk_dfa harrison1"
value "mk_dfa harrison2"

end
