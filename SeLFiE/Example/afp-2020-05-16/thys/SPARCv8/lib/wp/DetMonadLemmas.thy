(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

(* Zhe Hou: I removed the lemmas related to the definitions which are 
*  removed from DetMonad. That is, only those lemmas for deterministic
*  monads are kept here. 
*)

theory DetMonadLemmas
imports DetMonad
begin

section "General Lemmas Regarding the Deterministic State Monad"

subsection "Congruence Rules for the Function Package"

lemma bind_cong[fundef_cong]:
  "\<lbrakk> f = f'; \<And>v s s'. (v, s') = fst (f' s) \<Longrightarrow> g v s' = g' v s' \<rbrakk> \<Longrightarrow> f >>= g = f' >>= g'"
  apply (rule ext) 
  apply (auto simp: bind_def h1_def h2_def Let_def split_def intro: rev_image_eqI)
  done

lemma bind_apply_cong [fundef_cong]:
  "\<lbrakk> f s = f' s'; \<And>rv st. (rv, st) = fst (f' s') \<Longrightarrow> g rv st = g' rv st \<rbrakk>
       \<Longrightarrow> (f >>= g) s = (f' >>= g') s'"
  apply (simp add: bind_def h1_def h2_def)
  apply (auto simp: split_def intro: SUP_cong [OF refl] intro: rev_image_eqI)
  done

lemma bindE_cong[fundef_cong]:
  "\<lbrakk> M = M' ; \<And>v s s'. (Inr v, s') = fst (M' s) \<Longrightarrow> N v s' = N' v s' \<rbrakk> \<Longrightarrow> bindE M N = bindE M' N'"
  apply (simp add: bindE_def)
  apply (rule bind_cong)
   apply (rule refl)
  apply (unfold lift_def)
  apply (case_tac v, simp_all)
  done

lemma bindE_apply_cong[fundef_cong]:
  "\<lbrakk> f s = f' s'; \<And>rv st. (Inr rv, st) = fst (f' s') \<Longrightarrow> g rv st = g' rv st \<rbrakk> 
  \<Longrightarrow> (f >>=E g) s = (f' >>=E g') s'"
  apply (simp add: bindE_def)
  apply (rule bind_apply_cong)
   apply assumption
  apply (case_tac rv, simp_all add: lift_def)
  done

lemma K_bind_apply_cong[fundef_cong]:
  "\<lbrakk> f st = f' st' \<rbrakk> \<Longrightarrow> K_bind f arg st = K_bind f' arg' st'"
  by simp

lemma when_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> whenE C m s = whenE C' m' s'"
  by (simp add: whenE_def)

lemma unless_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; \<not> C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> unlessE C m s = unlessE C' m' s'"
  by (simp add: unlessE_def)

lemma whenE_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> whenE C m s = whenE C' m' s'"
  by (simp add: whenE_def)

lemma unlessE_apply_cong[fundef_cong]:
  "\<lbrakk> C = C'; s = s'; \<not> C' \<Longrightarrow> m s' = m' s' \<rbrakk> \<Longrightarrow> unlessE C m s = unlessE C' m' s'"
  by (simp add: unlessE_def)

subsection "Simplifying Monads"

lemma nested_bind [simp]:
  "do x \<leftarrow> do y \<leftarrow> f; return (g y) od; h x od =
   do y \<leftarrow> f; h (g y) od"
  apply (clarsimp simp add: bind_def h1_def h2_def)
  apply (rule ext)
  apply (clarsimp simp add: Let_def split_def return_def)
  done

lemma assert_True [simp]:
  "assert True >>= f = f ()"
  by (simp add: assert_def)

lemma when_True_bind [simp]:
  "when1 True g >>= f = g >>= f"
  by (simp add: when1_def bind_def return_def)

lemma whenE_False_bind [simp]:
  "whenE False g >>=E f = f ()"
  by (simp add: whenE_def bindE_def returnOk_def lift_def)

lemma whenE_True_bind [simp]:
  "whenE True g >>=E f = g >>=E f"
  by (simp add: whenE_def bindE_def returnOk_def lift_def)

lemma when_True [simp]: "when1 True X = X"
  by (clarsimp simp: when1_def)

lemma when_False [simp]: "when1 False X = return ()"
  by (clarsimp simp: when1_def)

lemma unless_False [simp]: "unless False X = X"
  by (clarsimp simp: unless_def)

lemma unless_True [simp]: "unless True X = return ()"
  by (clarsimp simp: unless_def)

lemma unlessE_whenE:
  "unlessE P = whenE (~P)"
  by (rule ext)+ (simp add: unlessE_def whenE_def)

lemma unless_when:
  "unless P = when1 (~P)"
  by (rule ext)+ (simp add: unless_def when1_def)

lemma gets_to_return [simp]: "gets (\<lambda>s. v) = return v"
  by (clarsimp simp: gets_def put_def get_def bind_def h1_def h2_def return_def)

lemma liftE_handleE' [simp]: "((liftE a) <handle2> b) = liftE a"
  apply (clarsimp simp: liftE_def handleE'_def)
  done

lemma liftE_handleE [simp]: "((liftE a) <handle> b) = liftE a"
  apply (unfold handleE_def)
  apply simp
  done

lemma condition_split:
  "P (condition C a b s) = ((((C s) \<longrightarrow> P (a s)) \<and> (\<not> (C s) \<longrightarrow> P (b s))))"
  apply (clarsimp simp: condition_def)
  done

lemma condition_split_asm:
  "P (condition C a b s) = (\<not> (C s \<and> \<not> P (a s) \<or> \<not> C s \<and> \<not> P (b s)))"
  apply (clarsimp simp: condition_def)
  done

lemmas condition_splits = condition_split condition_split_asm

lemma condition_true_triv [simp]:
  "condition (\<lambda>_. True) A B = A"
  apply (rule ext)
  apply (clarsimp split: condition_splits)
  done

lemma condition_false_triv [simp]:
  "condition (\<lambda>_. False) A B = B"
  apply (rule ext)
  apply (clarsimp split: condition_splits)
  done

lemma condition_true: "\<lbrakk> P s \<rbrakk> \<Longrightarrow> condition P A B s = A s"
  apply (clarsimp simp: condition_def)
  done

lemma condition_false: "\<lbrakk> \<not> P s \<rbrakk> \<Longrightarrow> condition P A B s = B s"
  apply (clarsimp simp: condition_def)
  done

section "Low-level monadic reasoning"

lemma valid_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>"
  by (auto simp add: valid_def no_fail_def split: prod.splits)

lemma validNF_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>!) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>!"
  by (auto simp add: valid_def validNF_def no_fail_def split: prod.splits)

lemma validE_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>, \<lbrace> \<lambda>rv s. E s0 rv s \<rbrace>) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s')
        \<and> (\<forall>rv s'. E s0 rv s' \<longrightarrow> E' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>, \<lbrace> E' \<rbrace>"
  by (auto simp add: validE_def valid_def no_fail_def split: prod.splits sum.splits)

lemma validE_NF_make_schematic_post:
  "(\<forall>s0. \<lbrace> \<lambda>s. P s0 s \<rbrace> f \<lbrace> \<lambda>rv s. Q s0 rv s \<rbrace>, \<lbrace> \<lambda>rv s. E s0 rv s \<rbrace>!) \<Longrightarrow>
   \<lbrace> \<lambda>s. \<exists>s0. P s0 s \<and> (\<forall>rv s'. Q s0 rv s' \<longrightarrow> Q' rv s')
        \<and> (\<forall>rv s'. E s0 rv s' \<longrightarrow> E' rv s') \<rbrace> f \<lbrace> Q' \<rbrace>, \<lbrace> E' \<rbrace>!"
  by (auto simp add: validE_NF_def validE_def valid_def no_fail_def split: prod.splits sum.splits)

lemma validNF_conjD1: "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv s. Q rv s \<and> Q' rv s \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q \<rbrace>!"
  by (fastforce simp: validNF_def valid_def no_fail_def)

lemma validNF_conjD2: "\<lbrace> P \<rbrace> f \<lbrace> \<lambda>rv s. Q rv s \<and> Q' rv s \<rbrace>! \<Longrightarrow> \<lbrace> P \<rbrace> f \<lbrace> Q' \<rbrace>!"
  by (fastforce simp: validNF_def valid_def no_fail_def)

lemma exec_gets:
  "(gets f >>= m) s = m (f s) s"
  by (simp add: simpler_gets_def bind_def h1_def h2_def)

lemma in_gets:
  "(r, s') = fst (gets f s) = (r = f s \<and> s' = s)"
  by (simp add: simpler_gets_def)

end
