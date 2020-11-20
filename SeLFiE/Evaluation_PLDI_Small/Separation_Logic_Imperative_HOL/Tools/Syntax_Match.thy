section \<open>Syntactic Matching in the Simplifier\<close>
theory Syntax_Match
imports Main
begin

subsection \<open>Non-Matching\<close>

text \<open>
  We define the predicates \<open>syntax_nomatch\<close> 
  and \<open>syntax_fo_nomatch\<close>. The expression 
  \<open>syntax_nomatch pattern object\<close> is simplified to true only if 
  the term \<open>pattern\<close> syntactically matches the term \<open>object\<close>. 
  Note that, semantically, \<open>syntax_nomatch pattern object\<close> is always
  true. While \<open>syntax_nomatch\<close> does higher-order matching, 
  \<open>syntax_fo_nomatch\<close> does first-order matching.

  The intended application of these predicates are as guards for simplification
  rules, enforcing additional syntactic restrictions on the applicability of
  the simplification rule.
\<close>
definition syntax_nomatch :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  where syntax_nomatch_def: "syntax_nomatch pat obj \<equiv> True"
definition syntax_fo_nomatch :: "'a \<Rightarrow> 'b \<Rightarrow> bool" 
  where syntax_fo_nomatch_def: "syntax_fo_nomatch pat obj \<equiv> True"

(* Prevent simplifier to simplify inside syntax_xx predicates *)
lemma [cong]: "syntax_fo_nomatch x y = syntax_fo_nomatch x y" by simp
lemma [cong]: "syntax_nomatch x y = syntax_nomatch x y" by simp

ML \<open>
structure Syntax_Match = struct
  val nomatch_thm = @{thm syntax_nomatch_def};
  val fo_nomatch_thm = @{thm syntax_fo_nomatch_def};

  fun fo_nomatch_simproc ctxt credex = let
    (*val ctxt = Simplifier.the_context ss;*)
    val thy = Proof_Context.theory_of ctxt;

    val redex = Thm.term_of credex;
    val (_,[pat,obj]) = strip_comb redex;

    fun fo_matches po = (Pattern.first_order_match 
      thy po (Vartab.empty, Vartab.empty); true) handle Pattern.MATCH => false;
  in
    if fo_matches (pat,obj) then NONE else SOME fo_nomatch_thm
  end

  fun nomatch_simproc ctxt credex = let
    (*val ctxt = Simplifier.the_context ss;*)
    val thy = Proof_Context.theory_of ctxt;

    val redex = Thm.term_of credex;
    val (_,[pat,obj]) = strip_comb redex;
  in
    if Pattern.matches thy (pat,obj) then NONE else SOME nomatch_thm
  end
end
\<close>
simproc_setup nomatch ("syntax_nomatch pat obj") 
  = \<open>K Syntax_Match.nomatch_simproc\<close>
simproc_setup fo_nomatch ("syntax_fo_nomatch pat obj") 
  = \<open>K Syntax_Match.fo_nomatch_simproc\<close>


subsection \<open>Examples\<close>
subsubsection \<open>Ordering AC-structures\<close>
text \<open>
  Currently, the simplifier rules for ac-rewriting only work when
  associativity groups to the right. Here, we define rules that work for
  associativity grouping to the left. They are useful for operators where 
  syntax is parsed (and pretty-printed) left-associative.
\<close>

locale ac_operator =
  fixes f
  assumes right_assoc: "f (f a b) c = f a (f b c)"
  assumes commute: "f a b = f b a"
begin
  lemmas left_assoc = right_assoc[symmetric]
  lemma left_commute: "f a (f b c) = f b (f a c)"
    apply (simp add: left_assoc)
    apply (simp add: commute)
    done

  lemmas right_ac = right_assoc left_commute commute

  lemma right_commute: "f (f a b) c = f (f a c) b"
    by (simp add: right_ac)

  lemma safe_commute: "syntax_fo_nomatch (f x y) a \<Longrightarrow> f a b = f b a"
    by (simp add: right_ac)

  lemmas left_ac = left_assoc right_commute safe_commute
end

interpretation mult: ac_operator "(*) ::'a::ab_semigroup_mult \<Rightarrow> _ \<Rightarrow> _"
  apply unfold_locales
  apply (simp_all add: ac_simps)
  done

interpretation add: ac_operator "(+) ::'a::ab_semigroup_add \<Rightarrow> _ \<Rightarrow> _"
  apply unfold_locales
  apply (simp_all add: ac_simps)
  done

text \<open>Attention: \<open>conj_assoc\<close> is in standard simpset, it has to be 
  removed when using \<open>conj.left_ac\<close> !\<close>
interpretation conj: ac_operator "(\<and>)"
  by unfold_locales auto
interpretation disj: ac_operator "(\<or>)"
  by unfold_locales auto

end
