section \<open>Compiler Between Static Representations\<close>

theory Compiler
  imports Language Simulation
begin

definition option_comp :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('c \<Rightarrow> 'a option) \<Rightarrow> 'c \<Rightarrow> 'b option" (infix "\<Lleftarrow>" 50) where
  "(f \<Lleftarrow> g) x \<equiv> Option.bind (g x) f"

context
  fixes f :: "('a \<Rightarrow> 'a option)"
begin

fun option_comp_pow :: "nat \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "option_comp_pow 0 = (\<lambda>_. None)" |
  "option_comp_pow (Suc 0) = f" |
  "option_comp_pow (Suc n) = (option_comp_pow n \<Lleftarrow> f)"

end

locale compiler =
  L1: language step1 final1 load1 +
  L2: language step2 final2 load2 +
  backward_simulation step1 step2 final1 final2 order match
  for
    step1 and step2 and
    final1 and final2 and
    load1 :: "'prog1 \<Rightarrow> 'state1 option" and
    load2 :: "'prog2 \<Rightarrow> 'state2 option" and
    order :: "'index \<Rightarrow> 'index \<Rightarrow> bool" and
    match +
  fixes
    compile :: "'prog1 \<Rightarrow> 'prog2 option"
  assumes
    compile_load:
      "compile p1 = Some p2 \<Longrightarrow> load1 p1 = Some s1 \<Longrightarrow> \<exists>s2 i. load2 p2 = Some s2 \<and> match i s1 s2"
begin

text \<open>
The @{locale compiler} locale relates two languages, L1 and L2, by a backward simulation and provides a @{term compile} partial function from a concrete program in L1 to a concrete program in L2.
The only assumption is that a successful compilation results in a program which, when loaded, is equivalent to the loaded initial program.
\<close>


subsection \<open>Preservation of behaviour\<close>

corollary behaviour_preservation:
  assumes
    compiles: "compile p1 = Some p2" and
    loads: "load1 p1 = Some s1" "load2 p2 = Some s2" and
    behaves: "L2.behaves s2 b2" and
    not_wrong: "\<not> is_wrong b2"
  shows "\<exists>b1 i. L1.behaves s1 b1 \<and> rel_behaviour (match i) b1 b2"
proof -
  obtain i where "match i s1 s2"
    using compile_load[OF compiles] loads by auto
  then show ?thesis
    using simulation_behaviour[OF behaves not_wrong]
    by simp
qed

end

subsection \<open>Composition of compilers\<close>

lemma compiler_composition:
  assumes
    "compiler step1 step2 final1 final2 load1 load2 order1 match1 compile1" and
    "compiler step2 step3 final2 final3 load2 load3 order2 match2 compile2"
  shows "compiler step1 step3 final1 final3 load1 load3
    (lex_prodp order1\<^sup>+\<^sup>+ order2) (rel_comp match1 match2) (compile2 \<Lleftarrow> compile1)"
proof (rule compiler.intro) 
  show "language step1 final1"
    using assms(1)[THEN compiler.axioms(1)] .
next
  show "language step3 final3"
    using assms(2)[THEN compiler.axioms(2)] .
next
  show "backward_simulation step1 step3 final1 final3
     (lex_prodp order1\<^sup>+\<^sup>+ order2) (rel_comp match1 match2)"
    using backward_simulation_composition[OF assms[THEN compiler.axioms(3)]] .
next
  show "compiler_axioms load1 load3 (rel_comp match1 match2) (compile2 \<Lleftarrow> compile1)"
  proof unfold_locales
    fix p1 p3 s1
    assume
      compile: "(compile2 \<Lleftarrow> compile1) p1 = Some p3" and
      load: "load1 p1 = Some s1"
    obtain p2 where "compile1 p1 = Some p2" and "compile2 p2 = Some p3"
      using compile by (auto simp: bind_eq_Some_conv option_comp_def)
    then obtain s2 i where "load2 p2 = Some s2" and "match1 i s1 s2"
      using assms(1)[THEN compiler.compile_load] load
      by blast
    moreover obtain s3 i' where "load3 p3 = Some s3" and "match2 i' s2 s3"
      using assms(2)[THEN compiler.compile_load, OF \<open>compile2 p2 = Some p3\<close> \<open>load2 p2 = Some s2\<close>]
      by auto
    ultimately show "\<exists>s3 i. load3 p3 = Some s3 \<and> rel_comp match1 match2 i s1 s3"
      unfolding rel_comp_def by auto
  qed
qed

lemma compiler_composition_pow:
  assumes
    "compiler step step final final load load order match compile"
  shows "compiler step step final final load load
    (lexp order\<^sup>+\<^sup>+) (rel_comp_pow match) (option_comp_pow compile n)"
proof (induction n rule: option_comp_pow.induct)
  case 1
  show ?case
    using assms
    by (auto intro: compiler.axioms compiler.intro compiler_axioms.intro backward_simulation_pow)
next
  case 2
  show ?case
  proof (rule compiler.intro)
    show "compiler_axioms load load (rel_comp_pow match) (option_comp_pow compile (Suc 0))"
    proof unfold_locales
      fix p1 p2 s1
      assume
        "option_comp_pow compile (Suc 0) p1 = Some p2" and
        "load p1 = Some s1"
      thus "\<exists>s2 i. load p2 = Some s2 \<and> rel_comp_pow match i s1 s2"
        using compiler.compile_load[OF assms(1)]
        by (metis option_comp_pow.simps(2) rel_comp_pow.simps(2))
    qed
  qed (auto intro: assms compiler.axioms backward_simulation_pow)
next
  case (3 n')
  show ?case
  proof (rule compiler.intro)
    show "compiler_axioms load load (rel_comp_pow match) (option_comp_pow compile (Suc (Suc n')))"
    proof unfold_locales
      fix p1 p3 s1
      assume
        "option_comp_pow compile  (Suc (Suc n')) p1 = Some p3" and
        "load p1 = Some s1"
      then obtain p2 where
        comp: "compile p1 = Some p2" and
        comp_IH: "option_comp_pow compile (Suc n') p2 = Some p3"
        by (auto simp: option_comp_def bind_eq_Some_conv)
      then obtain s2 i where "load p2 = Some s2" and "match i s1 s2"
        using compiler.compile_load[OF assms(1) _ \<open>load p1 = Some s1\<close>] by blast
      then obtain s3 i' where "load p3 = Some s3" and "rel_comp_pow match i' s2 s3"
        using compiler.compile_load[OF "3.IH" comp_IH] by blast
      moreover have "rel_comp_pow match (i # i') s1 s3"
        using \<open>match i s1 s2\<close> \<open>rel_comp_pow match i' s2 s3\<close>
        using rel_comp_pow.elims(2) by fastforce
      ultimately show "\<exists>s3 i. load p3 = Some s3 \<and> rel_comp_pow match i s1 s3"
        by auto
    qed
  qed (auto intro: assms compiler.axioms backward_simulation_pow)
qed

end