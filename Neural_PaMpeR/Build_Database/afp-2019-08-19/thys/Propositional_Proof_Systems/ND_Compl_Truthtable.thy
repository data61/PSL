theory ND_Compl_Truthtable
imports ND_Sound
begin

text\<open>This proof is inspired by Huth and Ryan~\cite{huth2004logic}.\<close>
  
definition "turn_true \<A> F \<equiv> if \<A> \<Turnstile> F then F else (Not F)"
lemma lemma0[simp,intro!]: "\<A> \<Turnstile> turn_true \<A> F" unfolding turn_true_def by simp

lemma turn_true_simps[simp]: 
  "\<A> \<Turnstile> F \<Longrightarrow> turn_true \<A> F = F"
  "\<not> \<A> \<Turnstile> F \<Longrightarrow> turn_true \<A> F = \<^bold>\<not> F"
unfolding turn_true_def by simp_all
(* often more sensible than to unfold everything *)

definition line_assm :: "'a valuation \<Rightarrow> 'a set \<Rightarrow> 'a formula set" where
"line_assm \<A> \<equiv> (`) (\<lambda>k. turn_true \<A> (Atom k))"
definition line_suitable :: "'a set \<Rightarrow> 'a formula \<Rightarrow> bool" where
"line_suitable Z F \<equiv> (atoms F \<subseteq> Z)"
lemma line_suitable_junctors[simp]:
  "line_suitable \<A> (Not F) = line_suitable \<A> F"
  "line_suitable \<A> (And F G) = (line_suitable \<A> F \<and> line_suitable \<A> G)"
  "line_suitable \<A> (Or F G) = (line_suitable \<A> F \<and> line_suitable \<A> G)"
  "line_suitable \<A> (Imp F G) = (line_suitable \<A> F \<and> line_suitable \<A> G)"
unfolding line_suitable_def by(clarsimp; linarith)+

lemma line_assm_Cons[simp]: "line_assm \<A> (k\<triangleright>ks) = (if \<A> k then Atom k else Not (Atom k)) \<triangleright> line_assm \<A> ks"
unfolding line_assm_def by simp

lemma NotD: "\<Gamma> \<turnstile> \<^bold>\<not> F \<Longrightarrow> F\<triangleright>\<Gamma> \<turnstile> \<bottom>" by (meson Not2I NotE Weaken subset_insertI)

lemma truthline_ND_proof:
  fixes F :: "'a formula"
  assumes "line_suitable Z F"
  shows "line_assm \<A> Z \<turnstile> turn_true \<A> F"
using assms proof(induction F)
  case (Atom k) thus ?case using Ax[where 'a='a] by (simp add: line_suitable_def line_assm_def)
next
  case Bot
  have "turn_true \<A> \<bottom> = Not Bot" unfolding turn_true_def by simp
  thus ?case by (simp add: Ax NotI) (* the theorems from ND/BigFormulas would be useful here. but\<dots> nah. *)
next
  have [simp]: "\<Gamma> \<turnstile> \<^bold>\<not> (\<^bold>\<not> F) \<longleftrightarrow> \<Gamma> \<turnstile> F" for F :: "'a formula" and \<Gamma> by (metis NDtrans Not2E Not2I)
  case (Not F)
  hence "line_assm \<A> Z \<turnstile> turn_true \<A> F" by simp
  thus ?case by(cases "\<A> \<Turnstile> F"; simp)
next
  have [simp]: "\<lbrakk>line_assm \<A> Z \<turnstile> \<^bold>\<not> F; \<not> \<A> \<Turnstile> F\<rbrakk> \<Longrightarrow> F \<^bold>\<and> G\<triangleright> line_assm \<A> Z \<turnstile> \<bottom>" for F G by(blast intro!: NotE[where F=F] intro: AndE1[OF Ax] Weaken[OF _ subset_insertI])
  have [simp]: "\<lbrakk>line_assm \<A> Z \<turnstile> \<^bold>\<not> G; \<not> \<A> \<Turnstile> G\<rbrakk> \<Longrightarrow> F \<^bold>\<and> G\<triangleright> line_assm \<A> Z \<turnstile> \<bottom>" for F G by(blast intro!: NotE[where F=G] intro: AndE2[OF Ax] Weaken[OF _ subset_insertI]) 
    (* (meson AndL_sim Not2I NotE Weaken subset_insertI) *)
  case (And F G)
  thus ?case by(cases "\<A> \<Turnstile> F"; cases "\<A> \<Turnstile> G"; simp; intro ND.NotI AndI; simp) 
next
  case (Or F G)
  thus ?case by(cases "\<A> \<Turnstile> F"; cases "\<A> \<Turnstile> G"; simp; (elim ND.OrI1 ND.OrI2)?) (force intro!: NotI dest!: NotD dest: OrL_sim)
next
  case (Imp F G)
  hence mIH: "line_assm \<A> Z \<turnstile> turn_true \<A> F" "line_assm \<A> Z \<turnstile> turn_true \<A> G" by simp+
  thus ?case by(cases "\<A> \<Turnstile> F"; cases "\<A> \<Turnstile> G"; simp; intro ImpI NotI ImpL_sim; simp add: Weaken[OF _ subset_insertI] NotSwap NotD NotD[THEN BotE])
qed
thm NotD[THEN BotE]

lemma deconstruct_assm_set:
  assumes IH: "\<And>\<A>. line_assm \<A> (k\<triangleright>Z) \<turnstile> F"
  shows "\<And>\<A>. line_assm \<A> Z \<turnstile> F"
proof cases
  assume "k \<in> Z" with IH show "?thesis \<A>" for \<A> by (simp add: insert_absorb)
next
  assume "k \<notin> Z"
  fix \<A>
  text\<open>Since we require the IH for arbitrary @{term \<A>}, we use a modified @{term \<A>} from the conclusion like this:\<close>
  from IH have av: "line_assm (\<A>(k := v)) (k\<triangleright>Z) \<turnstile> F" for v by blast
  text\<open>However, that modification is only relevant for @{term "k\<triangleright>Z"}, nothing from @{term Z} gets touched.\<close>
  from \<open>k \<notin> Z\<close> have "line_assm (\<A>(k := v)) Z = line_assm \<A> Z" for v unfolding line_assm_def turn_true_def by force
  text\<open>That means we can rewrite the modified @{const line_assm} like this:\<close>
  hence "line_assm (\<A>(k := v)) (k\<triangleright>Z) = 
      (if v then Atom k else Not (Atom k)) \<triangleright> line_assm \<A> Z" for v by simp
  text\<open>Inserting @{const True} and @{const False} for \<open>v\<close> yields the two alternatives.\<close>
  with av have "Atom k \<triangleright> line_assm \<A> Z \<turnstile> F" "Not (Atom k) \<triangleright> line_assm \<A> Z \<turnstile> F"
    by(metis (full_types))+
  with ND_caseDistinction show "line_assm \<A> Z \<turnstile> F" .
qed

theorem ND_complete:
  assumes taut: "\<Turnstile> F"
  shows "{} \<turnstile> F"
proof -
  have [simp]: "turn_true Z F = F" for Z using taut by simp
  (* \<up> too fast for you? read \<down> *)
  have "line_assm \<A> {} \<turnstile> F" for \<A>
  proof(induction arbitrary: \<A> rule: finite_empty_induct)
    show fat: "finite (atoms F)" by (fact atoms_finite)
  next
    have su: "line_suitable (atoms F) F" unfolding line_suitable_def by simp
    with truthline_ND_proof[OF su] show base: "line_assm \<A> (atoms F) \<turnstile> F" for \<A> by simp
  next
    case (3 k Z)
    from \<open>k \<in> Z\<close> have *: \<open>k \<triangleright> Z - {k} = Z\<close> by blast
    from \<open>\<And>\<A>. line_assm \<A> Z \<turnstile> F\<close>
    show \<open>line_assm \<A> (Z - {k}) \<turnstile> F\<close>
      using deconstruct_assm_set[of k "Z - {k}" F \<A>]
      unfolding * by argo
  qed
  (* could have done that more efficiently\<dots>
  have "line_assm \<A> {} \<turnstile> F" for \<A>
    using deconstruct_assm_set[OF spec[where P="\<lambda>\<A>. line_assm \<A> (_ \<triangleright> _) \<turnstile> F"]]
    using finite_empty_induct[OF fat, where P="\<lambda>Z. \<forall>\<A>. line_assm \<A> Z \<turnstile> F",
        OF base[THEN allI[where P="\<lambda>\<A>. line_assm \<A> (atoms F) \<turnstile> F"]]]
    by (metis (full_types) insert_Diff_single insert_absorb)*)
  thus ?thesis unfolding line_assm_def by simp
qed

corollary ND_sound_complete: "{} \<turnstile> F \<longleftrightarrow> \<Turnstile> F"
  using ND_sound[of "{}" F] ND_complete[of F] unfolding entailment_def by blast

end
