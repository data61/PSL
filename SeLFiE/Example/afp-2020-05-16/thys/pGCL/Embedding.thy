(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section "A Shallow Embedding of pGCL in HOL"

theory Embedding imports Misc Induction begin

subsection \<open>Core Primitives and Syntax\<close>

text_raw \<open>\label{s:syntax}\<close>

text \<open>A pGCL program is embedded directly as its strict or liberal transformer.  This is
achieved with an additional parameter, specifying which semantics should be obeyed.\<close>

type_synonym 's prog = "bool \<Rightarrow> ('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real)"

text \<open>@{term Abort} either always fails, @{term "\<lambda>P s. 0"}, or always succeeds,
@{term "\<lambda>P s. 1"}.\<close>
definition Abort :: "'s prog"
where     "Abort \<equiv> \<lambda>ab P s. if ab then 0 else 1"

text \<open>@{term Skip} does nothing at all.\<close>
definition Skip :: "'s prog"
where     "Skip \<equiv> \<lambda>ab P. P"

text \<open>@{term Apply} lifts a state transformer into the space of programs.\<close>
definition Apply :: "('s \<Rightarrow> 's) \<Rightarrow> 's prog"
where     "Apply f \<equiv> \<lambda>ab P s. P (f s)"

text \<open>@{term Seq} is sequential composition.\<close>
definition Seq :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog"
                 (infixl ";;" 59)
where     "Seq a b \<equiv> (\<lambda>ab. a ab o b ab)"

text \<open>@{term PC} is \emph{probabilistic} choice between programs.\<close>
definition PC :: "'s prog \<Rightarrow> ('s \<Rightarrow> real) \<Rightarrow> 's prog \<Rightarrow> 's prog"
                 ("_ \<^bsub>_\<^esub>\<oplus> _" [58,57,57] 57)
where     "PC a P b \<equiv> \<lambda>ab Q s. P s * a ab Q s + (1 - P s) * b ab Q s" 

text \<open>@{term DC} is \emph{demonic} choice between programs.\<close>
definition DC :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog" ("_ \<Sqinter> _" [58,57] 57)
where     "DC a b \<equiv> \<lambda>ab Q s. min (a ab Q s) (b ab Q s)"

text \<open>@{term AC} is \emph{angelic} choice between programs.\<close>
definition AC :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog" ("_ \<Squnion> _" [58,57] 57)
where     "AC a b \<equiv> \<lambda>ab Q s. max (a ab Q s) (b ab Q s)"

text \<open>@{term Embed} allows any expectation transformer to be treated
  syntactically as a program, by ignoring the failure flag.\<close>
definition Embed :: "'s trans \<Rightarrow> 's prog"
where     "Embed t = (\<lambda>ab. t)"

text \<open>@{term Mu} is the recursive primitive, and is either then
  least or greatest fixed point.\<close>
definition Mu :: "('s prog \<Rightarrow> 's prog) \<Rightarrow> 's prog" (binder "\<mu>" 50)
where     "Mu(T) \<equiv> (\<lambda>ab. if ab then lfp_trans (\<lambda>t. T (Embed t) ab)
                               else gfp_trans (\<lambda>t. T (Embed t) ab))"

text \<open>@{term repeat} expresses finite repetition\<close>
primrec
  repeat :: "nat \<Rightarrow> 'a prog \<Rightarrow> 'a prog"
where
  "repeat 0 p = Skip" |
  "repeat (Suc n) p = p ;; repeat n p"

text \<open>@{term SetDC} is demonic choice between a set of alternatives,
  which may depend on the state.\<close>
definition SetDC :: "('a \<Rightarrow> 's prog) \<Rightarrow> ('s \<Rightarrow> 'a set) \<Rightarrow> 's prog"
  where "SetDC f S \<equiv> \<lambda>ab P s. Inf ((\<lambda>a. f a ab P s) ` S s)"

syntax "_SetDC" :: "pttrn => ('s => 'a set) => 's prog => 's prog"
                   ("\<Sqinter>_\<in>_./ _" 100)
translations "\<Sqinter>x\<in>S. p" == "CONST SetDC (%x. p) S"

text \<open>The above syntax allows us to write @{term "\<Sqinter>x\<in>S. Apply f"}\<close>

text \<open>@{term SetPC} is \emph{probabilistic} choice from a set.  Note that this is only
meaningful for distributions of finite support.\<close>
definition
  SetPC :: "('a \<Rightarrow> 's prog) \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 's prog"
where
  "SetPC f p \<equiv> \<lambda>ab P s. \<Sum>a\<in>supp (p s). p s a * f a ab P s"

text \<open>@{term Bind} allows us to name an expression in the current state, and re-use it later.\<close>
definition
  Bind :: "('s \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 's prog) \<Rightarrow> 's prog"
where
  "Bind g f ab \<equiv> \<lambda>P s. let a = g s in f a ab P s"

text \<open>This gives us something like let syntax\<close>
syntax "_Bind" :: "pttrn => ('s => 'a) => 's prog => 's prog"
       ("_ is _ in _" [55,55,55]55)
translations "x is f in a" => "CONST Bind f (%x. a)"

definition flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c"
where [simp]: "flip f = (\<lambda>b a. f a b)"

text \<open>The following pair of translations introduce let-style syntax
  for @{term SetPC} and @{term SetDC}, respectively.\<close>
syntax "_PBind" :: "pttrn => ('s => real) => 's prog => 's prog"
                   ("bind _ at _ in _" [55,55,55]55)
translations "bind x at p in a" => "CONST SetPC (%x. a) (CONST flip (%x. p))"

syntax "_DBind" :: "pttrn => ('s => 'a set) \<Rightarrow> 's prog => 's prog"
                   ("bind _ from _ in _" [55,55,55]55)
translations "bind x from S in a" => "CONST SetDC (%x. a) S"

text \<open>The following syntax translations are for convenience when
  using a record as the state type.\<close>
syntax
  "_assign" :: "ident => 'a => 's prog" ("_ := _" [1000,900]900)
ML \<open>
  fun assign_tr _ [Const (name,_), arg] =
      Const ("Embedding.Apply", dummyT) $
      Abs ("s", dummyT,
           Syntax.const (suffix Record.updateN name) $
           Abs (Name.uu_, dummyT, arg $ Bound 1) $ Bound 0)
    | assign_tr _ ts = raise TERM ("assign_tr", ts)
\<close>
parse_translation \<open>[(@{syntax_const "_assign"}, assign_tr)]\<close>

syntax
  "_SetPC" :: "ident => ('s => 'a => real) => 's prog"
              ("choose _ at _" [66,66]66)
ML \<open>
  fun set_pc_tr _ [Const (f,_), P] =
      Const ("SetPC", dummyT) $
      Abs ("v", dummyT,
           (Const ("Embedding.Apply", dummyT) $
            Abs ("s", dummyT,
                 Syntax.const (suffix Record.updateN f) $
                 Abs (Name.uu_, dummyT, Bound 2) $ Bound 0))) $
      P
    | set_pc_tr _ ts = raise TERM ("set_pc_tr", ts)
\<close>
parse_translation \<open>[(@{syntax_const "_SetPC"}, set_pc_tr)]\<close>

syntax
  "_set_dc" :: "ident => ('s => 'a set) => 's prog" ("_ :\<in> _" [66,66]66)
ML \<open>
  fun set_dc_tr _ [Const (f,_), S] =
      Const ("SetDC", dummyT) $
      Abs ("v", dummyT,
           (Const ("Embedding.Apply", dummyT) $
            Abs ("s", dummyT,
                 Syntax.const (suffix Record.updateN f) $
                 Abs (Name.uu_, dummyT, Bound 2) $ Bound 0))) $
      S
    | set_dc_tr _ ts = raise TERM ("set_dc_tr", ts)
\<close>
parse_translation \<open>[(@{syntax_const "_set_dc"}, set_dc_tr)]\<close>

text \<open>These definitions instantiate the embedding as either
        weakest precondition (True) or weakest liberal precondition
        (False).\<close>

syntax
  "_set_dc_UNIV" :: "ident => 's prog" ("any _" [66]66)

translations
  "_set_dc_UNIV x" => "_set_dc x (%_. CONST UNIV)"

definition
  wp :: "'s prog \<Rightarrow> 's trans"
where
  "wp pr \<equiv> pr True"

definition
  wlp :: "'s prog \<Rightarrow> 's trans"
where
  "wlp pr \<equiv> pr False"

text \<open>If-Then-Else as a degenerate probabilistic choice.\<close>
abbreviation(input)
  if_then_else :: "['s \<Rightarrow> bool, 's prog, 's prog] \<Rightarrow> 's prog"
      ("If _ Then _ Else _" 58)
where
  "If P Then a Else b == a \<^bsub>\<guillemotleft>P\<guillemotright>\<^esub>\<oplus> b"

text \<open>Syntax for loops\<close>
abbreviation
  do_while :: "['s \<Rightarrow> bool, 's prog] \<Rightarrow> 's prog"
              ("do _ \<longrightarrow>// (4 _) //od")
where
  "do_while P a \<equiv> \<mu> x. If P Then a ;; x Else Skip"

subsection \<open>Unfolding rules for non-recursive primitives\<close>

lemma eval_wp_Abort:
  "wp Abort P = (\<lambda>s. 0)"
  unfolding wp_def Abort_def by(simp)

lemma eval_wlp_Abort:
  "wlp Abort P = (\<lambda>s. 1)"
  unfolding wlp_def Abort_def by(simp)

lemma eval_wp_Skip:
  "wp Skip P = P"
  unfolding wp_def Skip_def by(simp)

lemma eval_wlp_Skip:
  "wlp Skip P = P"
  unfolding wlp_def Skip_def by(simp)

lemma eval_wp_Apply:
  "wp (Apply f) P = P o f"
  unfolding wp_def Apply_def by(simp add:o_def)

lemma eval_wlp_Apply:
  "wlp (Apply f) P = P o f"
  unfolding wlp_def Apply_def by(simp add:o_def)

lemma eval_wp_Seq:
  "wp (a ;; b) P = (wp a o wp b) P"
  unfolding wp_def Seq_def by(simp)

lemma eval_wlp_Seq:
  "wlp (a ;; b) P = (wlp a o wlp b) P"
  unfolding wlp_def Seq_def by(simp)

lemma eval_wp_PC:
  "wp (a \<^bsub>Q\<^esub>\<oplus> b) P = (\<lambda>s. Q s * wp a P s + (1 - Q s) * wp b P s)"
  unfolding wp_def PC_def by(simp)

lemma eval_wlp_PC:
  "wlp (a \<^bsub>Q\<^esub>\<oplus> b) P = (\<lambda>s. Q s * wlp a P s + (1 - Q s) * wlp b P s)"
  unfolding wlp_def PC_def by(simp)

lemma eval_wp_DC:
  "wp (a \<Sqinter> b) P = (\<lambda>s. min (wp a P s) (wp b P s))"
  unfolding wp_def DC_def by(simp)

lemma eval_wlp_DC:
  "wlp (a \<Sqinter> b) P = (\<lambda>s. min (wlp a P s) (wlp b P s))"
  unfolding wlp_def DC_def by(simp)

lemma eval_wp_AC:
  "wp (a \<Squnion> b) P = (\<lambda>s. max (wp a P s) (wp b P s))"
  unfolding wp_def AC_def by(simp)

lemma eval_wlp_AC:
  "wlp (a \<Squnion> b) P = (\<lambda>s. max (wlp a P s) (wlp b P s))"
  unfolding wlp_def AC_def by(simp)

lemma eval_wp_Embed:
  "wp (Embed t) = t"
  unfolding wp_def Embed_def by(simp)

lemma eval_wlp_Embed:
  "wlp (Embed t) = t"
  unfolding wlp_def Embed_def by(simp)

lemma eval_wp_SetDC:
  "wp (SetDC p S) R s = Inf ((\<lambda>a. wp (p a) R s) ` S s)"
  unfolding wp_def SetDC_def by(simp)

lemma eval_wlp_SetDC:
  "wlp (SetDC p S) R s = Inf ((\<lambda>a. wlp (p a) R s) ` S s)"
  unfolding wlp_def SetDC_def by(simp)

lemma eval_wp_SetPC:
  "wp (SetPC f p) P = (\<lambda>s. \<Sum>a\<in>supp (p s). p s a * wp (f a) P s)"
  unfolding wp_def SetPC_def by(simp)

lemma eval_wlp_SetPC:
  "wlp (SetPC f p) P = (\<lambda>s. \<Sum>a\<in>supp (p s). p s a * wlp (f a) P s)"
  unfolding wlp_def SetPC_def by(simp)

lemma eval_wp_Mu:
  "wp (\<mu> t. T t) = lfp_trans (\<lambda>t. wp (T (Embed t)))"
  unfolding wp_def Mu_def by(simp)

lemma eval_wlp_Mu:
  "wlp (\<mu> t. T t) = gfp_trans (\<lambda>t. wlp (T (Embed t)))"
  unfolding wlp_def Mu_def by(simp)

lemma eval_wp_Bind:
  "wp (Bind g f) = (\<lambda>P s. wp (f (g s)) P s)"
  unfolding Bind_def wp_def Let_def by(simp)

lemma eval_wlp_Bind:
  "wlp (Bind g f) = (\<lambda>P s. wlp (f (g s)) P s)"
  unfolding Bind_def wlp_def Let_def by(simp)

text \<open>Use simp add:wp\_eval to fully unfold a program fragment\<close>
lemmas wp_eval = eval_wp_Abort eval_wlp_Abort eval_wp_Skip eval_wlp_Skip
                 eval_wp_Apply eval_wlp_Apply eval_wp_Seq eval_wlp_Seq
                 eval_wp_PC eval_wlp_PC eval_wp_DC eval_wlp_DC
                 eval_wp_AC eval_wlp_AC
                 eval_wp_Embed eval_wlp_Embed eval_wp_SetDC eval_wlp_SetDC
                 eval_wp_SetPC eval_wlp_SetPC eval_wp_Mu eval_wlp_Mu
                 eval_wp_Bind eval_wlp_Bind

lemma Skip_Seq:
  "Skip ;; A = A"
  unfolding Skip_def Seq_def o_def by(rule refl)

lemma Seq_Skip:
  "A ;; Skip = A"
  unfolding Skip_def Seq_def o_def by(rule refl)

text \<open>Use these as simp rules to clear out Skips\<close>
lemmas skip_simps = Skip_Seq Seq_Skip

end
