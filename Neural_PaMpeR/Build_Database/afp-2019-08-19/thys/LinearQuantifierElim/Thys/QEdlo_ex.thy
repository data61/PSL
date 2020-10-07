(*  Author:     Tobias Nipkow, 2007  *)

theory QEdlo_ex imports QEdlo
begin

(* tweaking the reflection setup *)

definition "interpret" :: "atom fm \<Rightarrow> 'a::dlo list \<Rightarrow> bool" where
"interpret = Logic.interpret I\<^sub>d\<^sub>l\<^sub>o"

lemma interpret_Atoms:
  "interpret (Atom (Eq i j)) xs = (xs!i = xs!j)" 
  "interpret (Atom (Less i j)) xs = (xs!i < xs!j)"
by(simp_all add:interpret_def)

lemma interpret_others:
  "interpret (Neg(ExQ (Neg f))) xs = (\<forall>x. interpret f (x#xs))"
  "interpret (Or (Neg f1) f2) xs = (interpret f1 xs \<longrightarrow> interpret f2 xs)"
by(simp_all add:interpret_def)

lemmas reify_eqs =
  Logic.interpret.simps(1,2,4-7)[of I\<^sub>d\<^sub>l\<^sub>o, folded interpret_def]
  interpret_others interpret_Atoms

method_setup dlo_reify = \<open>
  Scan.succeed
  (fn ctxt =>
    Method.SIMPLE_METHOD' (Reification.tac ctxt @{thms reify_eqs} NONE
     THEN' simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm"interpret_def"}])))
\<close> "dlo reification"

(* leave just enough equations in to convert back to True/False by eval *)
declare I\<^sub>d\<^sub>l\<^sub>o.simps(1)[code]
declare Logic.interpret.simps[code del]
declare Logic.interpret.simps(1-2)[code]

subsection\<open>Examples\<close>

lemma "\<forall>x::real. \<not> x < x"
apply dlo_reify
apply (subst I_qe_dlo [symmetric])
by eval

lemma "\<forall>x y::real. \<exists>z. x < y \<longrightarrow> x < z \<and> z < y"
apply dlo_reify
apply (subst I_qe_dlo [symmetric])
by eval

lemma "\<exists> x::real. a+b < x \<and> x < c*d"
apply dlo_reify
apply (subst I_qe_dlo [symmetric])
apply normalization
oops

lemma "\<forall>x::real. \<not> x < x"
apply dlo_reify
apply (subst I_qe_dlo [symmetric])
by eval

lemma "\<forall>x y::real. \<exists>z. x < y \<longrightarrow> x < z \<and> z < y"
apply dlo_reify
apply (subst I_qe_dlo [symmetric])
by eval

(* 160 secs *)
lemma "\<not>(\<exists>x y z. \<forall>u::real. x < x \<or> \<not> x<u \<or> x<y \<and> y<z \<and> \<not> x<z)"
apply dlo_reify
apply (subst I_qe_dlo [symmetric])
by eval

lemma "qe_dlo(AllQ (Imp (Atom(Less 0 1)) (Atom(Less 1 0)))) = FalseF"
by eval

lemma "qe_dlo(AllQ(AllQ (Imp (Atom(Less 0 1)) (Atom(Less 0 1))))) = TrueF"
by eval

lemma
  "qe_dlo(AllQ(ExQ(AllQ (And (Atom(Less 2 1)) (Atom(Less 1 0)))))) = FalseF"
by eval

lemma "qe_dlo(AllQ(ExQ(ExQ (And (Atom(Less 1 2)) (Atom(Less 2 0)))))) = TrueF"
by eval

lemma
  "qe_dlo(AllQ(AllQ(ExQ (And (Atom(Less 1 0)) (Atom(Less 0 2)))))) = FalseF"
by eval

lemma "qe_dlo(AllQ(AllQ(ExQ (Imp (Atom(Less 1 2)) (And (Atom(Less 1 0)) (Atom(Less 0 2))))))) = TrueF"
by eval

value "qe_dlo(AllQ (Imp (Atom(Less 0 1)) (Atom(Less 0 2))))"

end
