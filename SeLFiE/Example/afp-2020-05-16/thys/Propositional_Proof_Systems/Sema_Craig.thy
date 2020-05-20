subsection\<open>Craig Interpolation using Semantics\<close>

theory Sema_Craig
imports Substitution_Sema
begin

text\<open>Semantic proof of Craig interpolation following Harrison~\cite{harrison2009handbook}.\<close>
  
(* we don't really need this lemma, sledgehammer would find a proof anyway. But it would be massively ugly. *)
lemma subst_true_false:
  assumes "\<A> \<Turnstile> F"
  shows "\<A> \<Turnstile> ((F[\<top> / n]) \<^bold>\<or> (F[\<bottom> / n]))"
using assms by(cases "\<A> n"; simp add: substitution_lemma fun_upd_idem)

theorem interpolation:
  assumes "\<Turnstile> \<Gamma> \<^bold>\<rightarrow> \<Delta>"
  obtains \<rho> where
    "\<Turnstile> \<Gamma> \<^bold>\<rightarrow> \<rho>" "\<Turnstile> \<rho> \<^bold>\<rightarrow> \<Delta>"
    "atoms \<rho> \<subseteq> atoms \<Gamma>"
    "atoms \<rho> \<subseteq> atoms \<Delta>"
proof(goal_cases)
  let ?as = "atoms \<Gamma> - atoms \<Delta>"
  have fas: "finite ?as" by simp
  from fas assms have "\<exists>\<rho>. ((\<Turnstile> \<Gamma> \<^bold>\<rightarrow> \<rho>) \<and> (\<Turnstile> \<rho> \<^bold>\<rightarrow> \<Delta>) \<and> (atoms \<rho> \<subseteq> atoms \<Gamma>) \<and> (atoms \<rho> \<subseteq> atoms \<Delta>))"
  proof(induction ?as arbitrary: \<Gamma> rule: finite_induct)
    case empty
    from \<open>{} = atoms \<Gamma> - atoms \<Delta>\<close> have "atoms \<Gamma> \<subseteq> atoms \<Delta>" by blast
    with \<open>\<Turnstile> \<Gamma> \<^bold>\<rightarrow> \<Delta>\<close> show ?case by(intro exI[where x=\<Gamma>]) simp
  next
    case (insert a A)
    hence e: "a \<in> atoms \<Gamma>" "a \<notin> atoms \<Delta>" by auto
    define \<Gamma>' where "\<Gamma>' = (\<Gamma>[\<top> / a]) \<^bold>\<or> (\<Gamma>[\<bottom> / a])"
    have su: "atoms \<Gamma>' \<subseteq> atoms \<Gamma>" unfolding \<Gamma>'_def by(cases "a \<in> atoms \<Gamma>"; simp add: subst_atoms)
    from \<open>\<Turnstile> \<Gamma> \<^bold>\<rightarrow> \<Delta>\<close> e have "\<Turnstile> \<Gamma>' \<^bold>\<rightarrow> \<Delta>" by (auto simp add: substitution_lemma \<Gamma>'_def)
    from \<open>a \<triangleright> A = atoms \<Gamma> - atoms \<Delta>\<close> \<open>a \<notin> A\<close> e have "A = atoms \<Gamma>' - atoms \<Delta>" by(simp add: subst_atoms \<Gamma>'_def) blast
    from insert.hyps(3)[OF this \<open>\<Turnstile> \<Gamma>' \<^bold>\<rightarrow> \<Delta>\<close>] obtain \<rho> where \<rho>: "\<Turnstile> \<Gamma>' \<^bold>\<rightarrow> \<rho>" "\<Turnstile> \<rho> \<^bold>\<rightarrow> \<Delta>" "atoms \<rho> \<subseteq> atoms \<Gamma>'" "atoms \<rho> \<subseteq> atoms \<Delta>" by clarify
    have "\<Turnstile> \<Gamma> \<^bold>\<rightarrow> \<rho>" using \<rho>(1) subst_true_false unfolding \<Gamma>'_def by fastforce
    with \<rho> su show ?case by(intro exI[where x=\<rho>]) simp
  qed
  moreover case 1
  ultimately show thesis by blast
qed
  
text\<open>The above proof is constructive, and it is actually very easy to write a procedure down.\<close>
function interpolate where
"interpolate F H = (
let K = atoms F - atoms H in
  if K = {}
  then F
  else (
    let k = Min K
    in interpolate ((F[\<top> / k]) \<^bold>\<or> (F[\<bottom> / k])) H
  )
)" by pat_completeness simp
(* I tried Inf instead of Min first. Only has downsides. *)

text\<open>Showing termination is slightly technical\dots\<close>
termination interpolate
  apply(relation "measure (\<lambda>(F,H). card (atoms F - atoms H))") 
              (* "measure (\<lambda>(F,H). card (atoms F))" also works, but doesn't make things more beautiful *)
   subgoal by simp
  apply (simp add: subst_atoms_simp)
  apply(intro conjI impI)
   apply(intro psubset_card_mono)
    subgoal by simp
   apply(subgoal_tac "Min (atoms F - atoms H) \<notin> atoms H")
    subgoal by blast
   apply (meson atoms_finite Diff_eq_empty_iff Diff_iff Min_in finite_Diff)+
done

text\<open>Surprisingly, @{const interpolate} is even executable,
  despite all the set operations involving @{const atoms}\<close>
lemma "interpolate (And (Atom (0::nat)) (Atom 1)) (Or (Atom 1) (Atom 2)) = 
  (\<top> \<^bold>\<and> Atom 1) \<^bold>\<or> (\<bottom> \<^bold>\<and> Atom 1)" by simp
value[code] "simplify_consts (interpolate (And (Atom (0::nat)) (Atom 1)) (Or (Atom 1) (Atom 2)))"
(* and the wikipedia example: *)
lemma "let P = Atom (0 :: nat); Q = Atom 1; R = Atom 2; T = Atom 3;
\<phi> = (\<^bold>\<not>(P \<^bold>\<and> Q)) \<^bold>\<rightarrow> (\<^bold>\<not>R \<^bold>\<and> Q);
\<psi> = (T \<^bold>\<rightarrow> P) \<^bold>\<or> (T \<^bold>\<rightarrow> (\<^bold>\<not>R));
I = interpolate \<phi> \<psi> in
(size I) = 23 \<and> simplify_consts I = Atom 2 \<^bold>\<rightarrow> Atom 0"
  by code_simp

theorem nonexistential_interpolation:
  assumes "\<Turnstile> F \<^bold>\<rightarrow> H"
  shows
    "\<Turnstile> F \<^bold>\<rightarrow> interpolate F H" (is "?t1") "\<Turnstile> interpolate F H \<^bold>\<rightarrow> H" (is "?t2")
    "atoms (interpolate F H) \<subseteq> atoms F \<inter> atoms H" (is "?s")
proof -
  let ?as = "atoms F - atoms H"
  have fas: "finite ?as" by simp
  hence "?t1 \<and> ?t2 \<and> ?s" using assms
  proof(induction "card ?as" arbitrary: F H)
    case (Suc n)
    let ?inf = "Min (atoms F - atoms H)"
    define G where "G = (F[\<top> / ?inf]) \<^bold>\<or> (F[\<bottom> / ?inf])"
    have e: "Min (atoms F - atoms H) \<in> atoms F - atoms H" by (metis Min_in Suc.hyps(2) Suc.prems(1) card_empty nat.simps(3))
    with Suc(2) have "n = card (atoms G - atoms H)" unfolding G_def subst_atoms_simp
    proof -
      assume a1: "Suc n = card (atoms F - atoms H)"
      assume "Min (atoms F - atoms H) \<in> atoms F - atoms H"
      hence a2: "Min (atoms F - atoms H) \<in> atoms F \<and> Min (atoms F - atoms H) \<notin> atoms H" by simp
      have "n = card (atoms F - atoms H) - 1"
        using a1 by presburger
      hence "n = card (atoms (F[\<top> / Min (atoms F - atoms H)]) \<union> atoms (F[\<bottom> / Min (atoms F - atoms H)]) - atoms H)"
        using a2 by (metis (full_types) formula.set(2) Diff_insert Diff_insert2 Suc.prems(1) Un_absorb Un_empty_right card_Diff_singleton e subst_atoms top_atoms_simp)
        (* you need to tell sledgehammer about formula.set if you want it to find a proof here\<dots> *)
      thus "n = card (atoms ((F[\<top> / Min (atoms F - atoms H)]) \<^bold>\<or> (F[\<bottom> / Min (atoms F - atoms H)])) - atoms H)" by simp
    qed
    moreover have "finite (atoms G - atoms H)" "\<Turnstile> G \<^bold>\<rightarrow> H" using Suc(3-) e
      by(auto simp: G_def substitution_lemma)
    ultimately have IH: "\<Turnstile> G \<^bold>\<rightarrow> interpolate G H" "\<Turnstile> interpolate G H \<^bold>\<rightarrow> H" 
        "atoms (interpolate G H) \<subseteq> atoms G \<inter> atoms H" using Suc by blast+
    moreover have "\<Turnstile> F \<^bold>\<rightarrow> G" unfolding G_def 
      using subst_true_false by fastforce
    moreover { (* sledgehammer\<dots> *)
        assume a1: "atoms (interpolate ((F[\<top>/Min (atoms F - atoms H)]) \<^bold>\<or> (F[\<bottom>/Min (atoms F - atoms H)])) H) \<subseteq> atoms (F[\<top>/Min (atoms F - atoms H)]) \<union> atoms (F[\<bottom>/Min (atoms F - atoms H)]) \<and> atoms (interpolate ((F[\<top>/Min (atoms F - atoms H)]) \<^bold>\<or> (F[\<bottom>/Min (atoms F - atoms H)])) H) \<subseteq> atoms H"
        have f2: "atoms ((\<bottom>::'a formula) \<^bold>\<rightarrow> \<bottom>) = atoms \<bottom>"
          by simp
        then have f3: "atoms F - {Min (atoms F - atoms H)} = atoms (F[\<top>/Min (atoms F - atoms H)])"
          by (metis (no_types) DiffD1 Top_def Un_empty_right e formula.simps(91) subst_atoms)
        have "atoms (F[\<bottom>/Min (atoms F - atoms H)]) = atoms (F[\<top>/Min (atoms F - atoms H)])"
          using f2 by (metis (no_types) DiffD1 Top_def e subst_atoms)
        then have "\<not> atoms F \<subseteq> atoms H \<longrightarrow> atoms (interpolate ((F[\<top>/Min (atoms F - atoms H)]) \<^bold>\<or> (F[\<bottom>/Min (atoms F - atoms H)])) H) \<subseteq> atoms F"
          using f3 a1 by blast
    } ultimately show ?case
      by (intro conjI; subst interpolate.simps; simp del: interpolate.simps add: Let_def G_def; blast?)
  qed auto
  thus "?t1" "?t2" "?s" by simp_all
qed
text\<open>So no, the proof is by no means easier this way.
  Admittedly, part of the fuzz is due to @{const Min},
  but replacing atoms with something that returns lists doesn't make it better.\<close>
    

end
