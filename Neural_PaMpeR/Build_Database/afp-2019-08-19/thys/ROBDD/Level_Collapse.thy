section\<open>Collapsing the levels\<close>
theory Level_Collapse
imports Conc_Impl
begin
text\<open>
The theory up to this point is implemented in a way that separated the different aspects into different levels.
This is highly beneficial for us, since it allows us to tackle the difficulties arising in small chunks.
However, exporting this to the user would be highly impractical.
Thus, this theory collapses all the different levels (i.e. refinement steps) and relates the computations in the heap monad to
@{type boolfunc}.
\<close>

definition "bddmi_rel cs \<equiv> {(a,c)|a b c. (a,b) \<in> bf_ifex_rel \<and> (c,b) \<in> Rmi cs}"
definition bdd_relator :: "(nat boolfunc \<times> nat) set \<Rightarrow> bddi \<Rightarrow> assn" where
"bdd_relator p s \<equiv> \<exists>\<^sub>Acs. is_bdd_impl cs s * \<up>(p \<subseteq> (bddmi_rel cs) \<and> bdd_sane cs) * true"

text\<open>
The @{type assn} predicate @{term bdd_relator} is the interface that is exposed to the user.
(The contents of the definition are not exposed.)
\<close>

lemma bdd_relator_mono[intro!]: "q \<subseteq> p \<Longrightarrow> bdd_relator p s \<Longrightarrow>\<^sub>A bdd_relator q s" unfolding bdd_relator_def by sep_auto

lemma bdd_relator_absorb_true[simp]: "bdd_relator p s * true = bdd_relator p s" unfolding bdd_relator_def by simp

thm bdd_relator_def[unfolded bddmi_rel_def, simplified]
lemma join_hlp1: "is_bdd_impl a s * is_bdd_impl b s \<Longrightarrow>\<^sub>A is_bdd_impl a s * is_bdd_impl b s * \<up>(a = b)"
  apply clarsimp
  apply(rule preciseD[where p=s and R="is_bdd_impl" and F="is_bdd_impl b s" and F'="is_bdd_impl a s"])
   apply(rule is_bdd_impl_prec)
  apply(unfold mod_and_dist)
  apply(rule conjI)
   apply assumption
  apply(simp add: star_aci(2))
done

lemma join_hlp: "is_bdd_impl a s * is_bdd_impl b s = is_bdd_impl b s * is_bdd_impl a s * \<up>(a = b)"
  apply(rule ent_iffI[rotated])
   apply(simp; fail)
  apply(rule ent_trans)
   apply(rule join_hlp1)
  apply(simp; fail)
  done

lemma add_true_asm:
  assumes "<b * true> p <a>\<^sub>t"
  shows "<b> p <a>\<^sub>t"
  apply(rule cons_pre_rule)
   prefer 2
   apply(rule assms)
  apply(simp add: ent_true_drop)
  done

lemma add_anything:
  assumes "<b> p <a>"
  shows "<b * x> p <\<lambda>r. a r * x>\<^sub>t"
proof -
  note [sep_heap_rules] = assms
  show ?thesis by sep_auto
qed

lemma add_true:
  assumes "<b> p <a>\<^sub>t"
  shows "<b * true> p <a>\<^sub>t"
  using assms add_anything[where x=true] by force


definition node_relator where "node_relator x y \<longleftrightarrow> x \<in> y"
text \<open>\<open>sep_auto\<close> behaves sub-optimal when having @{term "(bf,bdd) \<in> computed_pointer_relation"} as assumption in our cases. Using @{const node_relator} instead fixes this behavior with a custom solver for \<open>simp\<close>.\<close>

lemma node_relatorI: "x \<in> y \<Longrightarrow> node_relator x y" unfolding node_relator_def .
lemma node_relatorD: "node_relator x y \<Longrightarrow> x \<in> y" unfolding node_relator_def .

ML\<open>fun TRY' tac = tac ORELSE' K all_tac\<close>

setup \<open>map_theory_simpset (fn ctxt =>
  ctxt addSolver (Simplifier.mk_solver "node_relator"
    (fn ctxt => fn n =>
      let
        val tac =
          resolve_tac ctxt @{thms node_relatorI} THEN'
          REPEAT_ALL_NEW (resolve_tac ctxt @{thms Set.insertI1 Set.insertI2}) THEN'
          TRY' (dresolve_tac ctxt @{thms node_relatorD} THEN' assume_tac ctxt)
      in
        SOLVED' tac n
      end))
)\<close>

text\<open>
This is the general form one wants to work with:
if a function on the bdd is called with a set of already existing and valid pointers, the arguments to the function have to be in that set.
The result is that one more pointer is the set of existing and valid pointers.
\<close>

thm iteci_rule[THEN mp] mi.ite_impl_R ifex_ite_rel_bf

lemma iteci_rule[sep_heap_rules]: "
\<lbrakk>node_relator (ib, ic)  rp; node_relator (tb, tc) rp; node_relator (eb, ec) rp\<rbrakk> \<Longrightarrow>
<bdd_relator rp s> 
  iteci_lu ic tc ec s
<\<lambda>(r,s'). bdd_relator (insert (bf_ite ib tb eb,r) rp) s'>"
  apply(unfold bdd_relator_def node_relator_def)
  apply(intro norm_pre_ex_rule)
  apply(clarsimp)
  apply(unfold bddmi_rel_def)
  apply(drule (1) rev_subsetD)+
  apply(clarsimp)
  apply(drule (3) mi.ite_impl_lu_R[where ii=ic and ti=tc and ei=ec, unfolded in_rel_def])
  apply(drule ospecD2)
  apply(clarsimp simp del: ifex_ite.simps)
  apply(rule cons_post_rule)
   apply(rule cons_pre_rule[rotated])
    apply(rule iteci_lu_rule[THEN mp, THEN add_true])
    apply(assumption)
   apply(sep_auto; fail)
  apply(clarsimp simp del: ifex_ite.simps)
  apply(rule ent_ex_postI)
  apply(subst ent_pure_post_iff)
  apply(rule conjI[rotated])
   apply(sep_auto; fail)
  apply(clarsimp simp del: ifex_ite.simps)
  apply(rule conjI[rotated])
   apply(force simp add: mi.les_def)
  apply(rule exI)
  apply(rule conjI)
   apply(erule (2) ifex_ite_opt_rel_bf[unfolded in_rel_def]) 
  apply assumption
done

lemma tci_rule[sep_heap_rules]:
"<bdd_relator rp s> 
  tci s
<\<lambda>(r,s'). bdd_relator (insert (bf_True,r) rp) s'>"
  apply(unfold bdd_relator_def)
  apply(intro norm_pre_ex_rule)
  apply(clarsimp)
  apply(frule mi.Timpl_rule)
  apply(drule ospecD2)
  apply(clarify)
  apply(sep_auto)
   apply(unfold bddmi_rel_def)
   apply(clarsimp)
  apply(force simp add: mi.les_def)
done

lemma fci_rule[sep_heap_rules]:
"<bdd_relator rp s> 
  fci s
<\<lambda>(r,s'). bdd_relator (insert (bf_False,r) rp) s'>"
  apply(unfold bdd_relator_def)
  apply(intro norm_pre_ex_rule)
  apply(clarsimp)
  apply(frule mi.Fimpl_rule)
  apply(drule ospecD2)
  apply(clarify)
  apply(sep_auto)
   apply(unfold bddmi_rel_def)
   apply(clarsimp)
  apply(force simp add: mi.les_def)
done

text\<open>IFC/ifmi/ifci require that the variable order is ensured by the user. 
Instead of using ifci, a combination of litci and iteci has to be used.\<close>
lemma [sep_heap_rules]:
"\<lbrakk>(tb, tc) \<in> rp; (eb, ec) \<in> rp\<rbrakk> \<Longrightarrow>
<bdd_relator rp s> 
  ifci v tc ec s
<\<lambda>(r,s'). bdd_relator (insert (bf_if v tb eb,r) rp) s'>"
text\<open>This probably doesn't hold.\<close>
oops

lemma notci_rule[sep_heap_rules]:
  assumes "node_relator (tb, tc) rp"
  shows "<bdd_relator rp s> notci tc s <\<lambda>(r,s'). bdd_relator (insert (bf_not tb,r) rp) s'>"
using assms
by(sep_auto simp: notci_def)

lemma cirules1[sep_heap_rules]:
  assumes "node_relator (tb, tc) rp" "node_relator (eb, ec) rp"
  shows
    "<bdd_relator rp s> andci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_and tb eb,r) rp) s'>"
    "<bdd_relator rp s> orci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_or tb eb,r) rp) s'>"
    "<bdd_relator rp s> biimpci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_biimp tb eb,r) rp) s'>"
    "<bdd_relator rp s> xorci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_xor tb eb,r) rp) s'>"
(* actually, these functions would allow for more insert. I think that would be inconvenient though. *)
using assms
by (sep_auto simp: andci_def orci_def biimpci_def xorci_def)+

lemma cirules2[sep_heap_rules]:
  assumes "node_relator (tb, tc) rp" "node_relator (eb, ec) rp"
  shows
    "<bdd_relator rp s> nandci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_nand tb eb,r) rp) s'>"
    "<bdd_relator rp s> norci tc ec s <\<lambda>(r,s'). bdd_relator (insert (bf_nor tb eb,r) rp) s'>"
  using assms
  by(sep_auto simp: nandci_def norci_def)+

lemma litci_rule[sep_heap_rules]:
  "<bdd_relator rp s> litci v s <\<lambda>(r,s'). bdd_relator (insert (bf_lit v,r) rp) s'>"
  apply(unfold litci_def)
  apply(subgoal_tac \<open>\<And>t ab bb. \<comment> \<open>introducing some vars \dots\<close>
         <bdd_relator (insert (bf_False, ab) (insert (bf_True, t) rp)) bb * true> 
           ifci v t ab bb
         <\<lambda>r. case r of (r, x) \<Rightarrow> bdd_relator (insert (bf_lit v, r) rp) x>\<close>)
   apply(sep_auto; fail)
  apply(rename_tac tc fc sc)
  apply(unfold bdd_relator_def[abs_def])
  apply(clarsimp)
  apply(intro norm_pre_ex_rule)
  apply(clarsimp)
  apply(unfold bddmi_rel_def)
  apply(clarsimp simp only: bf_ifex_rel_consts_ensured)
  apply(frule mi.IFimpl_rule)
    apply(rename_tac tc fc sc sm a aa b ba fm tm)
    apply(thin_tac "(fm, Falseif) \<in> Rmi sm") 
    apply(assumption) (* hack: instantiate the first premise of mi.IFimpl_rule with the second assumption that matches. The other way around would be fine, too. *)
   apply(assumption)
  apply(clarsimp)
  apply(drule ospecD2)
  apply(clarify)
  apply(sep_auto)
  apply(force simp add: mi.les_def)
done

lemma tautci_rule[sep_heap_rules]:
  shows "node_relator (tb, tc) rp \<Longrightarrow> <bdd_relator rp s> tautci tc s <\<lambda>r. bdd_relator rp s * \<up>(r \<longleftrightarrow> tb = bf_True)>"
  apply(unfold node_relator_def)
  apply(unfold tautci_def)
  apply(unfold bdd_relator_def)
  apply(intro norm_pre_ex_rule; clarsimp)
  apply(unfold bddmi_rel_def)
  apply(drule (1) rev_subsetD)
  apply(clarsimp)
  apply(rename_tac sm ti)
  apply(frule (1) mi.DESTRimpl_rule; drule ospecD2; clarify)
  apply(sep_auto split: ifex.splits)
done

lemma emptyci_rule[sep_heap_rules]:
  shows "<emp> emptyci <\<lambda>r. bdd_relator {} r>"
by(sep_auto simp: bdd_relator_def)

(* TODO: make sure that emptyci_rule and firends don't appear duplicate, once concrete-impl style, once level-collapsed. *)

lemmas [simp] = bf_ite_def

text\<open>Efficient comparison of two nodes.\<close>

definition "eqci a b \<equiv> return (a = b)" (* wrapping definition so sep_auto does not run into nowhere *)

lemma iteeq_rule[sep_heap_rules]: "
\<lbrakk>node_relator (xb, xc)  rp; node_relator (yb, yc) rp\<rbrakk> \<Longrightarrow>
<bdd_relator rp s>
  eqci xc yc
<\<lambda>r. \<up>(r \<longleftrightarrow> xb = yb)>\<^sub>t"
  apply(unfold bdd_relator_def node_relator_def eqci_def)
  apply(intro norm_pre_ex_rule)
  apply(clarsimp)
  apply(unfold bddmi_rel_def)
  apply(drule (1) rev_subsetD)+
  apply(rule return_cons_rule)
  apply(clarsimp)
  apply(rule iffI)
   using bf_ifex_eq mi.cmp_rule_eq apply(blast)
  using bf_ifex_eq mi.cmp_rule_eq apply(blast)
done

end
