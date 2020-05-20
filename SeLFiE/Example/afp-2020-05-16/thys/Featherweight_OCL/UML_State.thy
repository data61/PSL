(*****************************************************************************
 * Featherweight-OCL --- A Formal Semantics for UML-OCL Version OCL 2.5
 *                       for the OMG Standard.
 *                       http://www.brucker.ch/projects/hol-testgen/
 *
 * UML_State.thy --- State Operations and Objects.
 * This file is part of HOL-TestGen.
 *
 * Copyright (c) 2012-2015 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2015 IRT SystemX, France
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

chapter\<open>Formalization III:  UML/OCL constructs: State Operations and Objects\<close>

theory  UML_State
imports UML_Library
begin

no_notation None ("\<bottom>")
section\<open>Introduction: States over Typed Object Universes\<close>

text\<open>\label{sec:universe}
  In the following, we will refine the concepts of a user-defined
  data-model (implied by a class-diagram) as well as the notion of
  $\state{}$ used in the previous section to much more detail.
  Surprisingly, even without a concrete notion of an objects and a
  universe of object representation, the generic infrastructure of
  state-related operations is fairly rich.
\<close>



subsection\<open>Fundamental Properties on Objects: Core Referential Equality\<close>
subsubsection\<open>Definition\<close>

text\<open>Generic referential equality - to be used for instantiations
 with concrete object types ...\<close>
definition  StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t :: "('\<AA>,'a::{object,null})val \<Rightarrow> ('\<AA>,'a)val \<Rightarrow> ('\<AA>)Boolean"
where      "StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y
            \<equiv> \<lambda> \<tau>. if (\<upsilon> x) \<tau> = true \<tau> \<and> (\<upsilon> y) \<tau> = true \<tau>
                    then if x \<tau> = null \<or> y \<tau> = null
                         then \<lfloor>\<lfloor>x \<tau> = null \<and> y \<tau> = null\<rfloor>\<rfloor>
                         else \<lfloor>\<lfloor>(oid_of (x \<tau>)) = (oid_of (y \<tau>)) \<rfloor>\<rfloor>
                    else invalid \<tau>"

subsubsection\<open>Strictness and context passing\<close>

lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_strict1[simp,code_unfold] :
"(StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x invalid) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def true_def false_def)

lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_strict2[simp,code_unfold] :
"(StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t invalid x) = invalid"
by(rule ext, simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def true_def false_def)


lemma cp_StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t:
"(StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y \<tau>) = (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t (\<lambda>_. x \<tau>) (\<lambda>_. y \<tau>)) \<tau>"
by(auto simp: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def cp_valid[symmetric])

text_raw\<open>\isatagafp\<close>
lemmas cp0_StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t= cp_StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t[THEN allI[THEN allI[THEN allI[THEN cpI2]],
             of "StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t"]]

lemmas cp_intro''[intro!,simp,code_unfold] =
       cp_intro''
       cp_StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t[THEN allI[THEN allI[THEN allI[THEN cpI2]],
             of "StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t"]]

text_raw\<open>\endisatagafp\<close>

subsection\<open>Logic and Algebraic Layer on Object\<close>
subsubsection\<open>Validity and Definedness Properties\<close>

text\<open>We derive the usual laws on definedness for (generic) object equality:\<close>
lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_defargs:
"\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x (y::('\<AA>,'a::{null,object})val))\<Longrightarrow> (\<tau> \<Turnstile>(\<upsilon> x)) \<and> (\<tau> \<Turnstile>(\<upsilon> y))"
by(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def true_def invalid_def bot_option_def
        split: bool.split_asm HOL.if_split_asm)

lemma defined_StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_I:
 assumes val_x : "\<tau> \<Turnstile> \<upsilon> x"
 assumes val_x : "\<tau> \<Turnstile> \<upsilon> y"
 shows "\<tau> \<Turnstile> \<delta> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y)"
 apply(insert assms, simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def)
by(subst cp_defined, simp add: true_def)

lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def_homo :
"\<delta>(StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x (y::('\<AA>,'a::{null,object})val)) = ((\<upsilon> x) and (\<upsilon> y))"
oops (* sorry *)

subsubsection\<open>Symmetry\<close>

lemma StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_sym :
assumes x_val : "\<tau> \<Turnstile> \<upsilon> x"
shows "\<tau> \<Turnstile> StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x x"
by(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def true_def OclValid_def
             x_val[simplified OclValid_def])


subsubsection\<open>Behavior vs StrongEq\<close>

text\<open>It remains to clarify the role of the state invariant
$\inv_\sigma(\sigma)$ mentioned above that states the condition that
there is a ``one-to-one'' correspondence between object
representations and $\oid$'s: $\forall \mathit{oid} \in \dom\ap
\sigma\spot oid = \HolOclOidOf\ap \drop{\sigma(\mathit{oid})}$.  This
condition is also mentioned in~\cite[Annex A]{omg:ocl:2012} and goes
back to \citet{richters:precise:2002}; however, we state this
condition as an invariant on states rather than a global axiom. It
can, therefore, not be taken for granted that an $\oid$ makes sense
both in pre- and post-states of OCL expressions.
\<close>

text\<open>We capture this invariant in the predicate WFF :\<close>

definition WFF :: "('\<AA>::object)st \<Rightarrow> bool"
where "WFF \<tau> = ((\<forall> x \<in> ran(heap(fst \<tau>)). \<lceil>heap(fst \<tau>) (oid_of x)\<rceil> = x) \<and>
                (\<forall> x \<in> ran(heap(snd \<tau>)). \<lceil>heap(snd \<tau>) (oid_of x)\<rceil> = x))"

text\<open>It turns out that WFF is a key-concept for linking strict referential equality to
logical equality: in well-formed states (i.e. those states where the self (oid-of) field contains
the pointer to which the object is associated to in the state), referential equality coincides
with logical equality.\<close>


text\<open>We turn now to the generic definition of referential equality on objects:
Equality on objects in a state is reduced to equality on the
references to these objects. As in HOL-OCL~\cite{brucker.ea:hol-ocl:2008,brucker.ea:hol-ocl-book:2006},
we will store the reference of an object inside the object in a (ghost) field.
By establishing certain invariants (``consistent state''), it can
be assured that there is a ``one-to-one-correspondence'' of objects
to their references---and therefore the definition below
behaves as we expect.\<close>
text\<open>Generic Referential Equality enjoys the usual properties:
(quasi) reflexivity, symmetry, transitivity, substitutivity for
defined values. For type-technical reasons, for each concrete
object type, the equality \<open>\<doteq>\<close> is defined by generic referential
equality.\<close>

theorem StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq:
assumes WFF: "WFF \<tau>"
and valid_x: "\<tau> \<Turnstile>(\<upsilon> x)"
and valid_y: "\<tau> \<Turnstile>(\<upsilon> y)"
and x_present_pre: "x \<tau> \<in> ran (heap(fst \<tau>))"
and y_present_pre: "y \<tau> \<in> ran (heap(fst \<tau>))"
and x_present_post:"x \<tau> \<in> ran (heap(snd \<tau>))"
and y_present_post:"y \<tau> \<in> ran (heap(snd \<tau>))"
 (* x and y must be object representations that exist in either the pre or post state *)
shows "(\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
apply(insert WFF valid_x valid_y x_present_pre y_present_pre x_present_post y_present_post)
apply(auto simp: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def WFF_def StrongEq_def true_def Ball_def)
apply(erule_tac x="x \<tau>" in allE', simp_all)
done

theorem StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq':
assumes WFF: "WFF \<tau>"
and valid_x: "\<tau> \<Turnstile>(\<upsilon> (x :: ('\<AA>::object,'\<alpha>::{null,object})val))"
and valid_y: "\<tau> \<Turnstile>(\<upsilon> y)"
and oid_preserve: "\<And>x. x \<in> ran (heap(fst \<tau>)) \<or> x \<in> ran (heap(snd \<tau>)) \<Longrightarrow>
                        H x \<noteq> \<bottom> \<Longrightarrow> oid_of (H x) = oid_of x"
and xy_together: "x \<tau> \<in> H ` ran (heap(fst \<tau>)) \<and> y \<tau> \<in> H ` ran (heap(fst \<tau>)) \<or>
                  x \<tau> \<in> H ` ran (heap(snd \<tau>)) \<and> y \<tau> \<in> H ` ran (heap(snd \<tau>))"
 (* x and y must be object representations that exist in either the pre or post state *)
shows "(\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
 apply(insert WFF valid_x valid_y xy_together)
 apply(simp add: WFF_def)
 apply(auto simp: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def OclValid_def WFF_def StrongEq_def true_def Ball_def)
by (metis foundation18' oid_preserve valid_x valid_y)+

text\<open>So, if two object descriptions live in the same state (both pre or post), the referential
equality on objects implies in a WFF state the logical equality.\<close>

section\<open>Operations on Object\<close>
subsection\<open>Initial States (for testing and code generation)\<close>

definition \<tau>\<^sub>0 :: "('\<AA>)st"
where     "\<tau>\<^sub>0 \<equiv> (\<lparr>heap=Map.empty, assocs = Map.empty\<rparr>,
                 \<lparr>heap=Map.empty, assocs = Map.empty\<rparr>)"

subsection\<open>OclAllInstances\<close>

text\<open>To denote OCL types occurring in OCL expressions syntactically---as, for example,
as ``argument'' of \inlineocl{oclAllInstances()}---we use the inverses of the injection functions into the object
universes; we show that this is a sufficient ``characterization.''\<close>

definition OclAllInstances_generic :: "(('\<AA>::object) st \<Rightarrow> '\<AA> state) \<Rightarrow> ('\<AA>::object \<rightharpoonup> '\<alpha>) \<Rightarrow>
                                       ('\<AA>, '\<alpha> option option) Set"
where "OclAllInstances_generic fst_snd H =
                    (\<lambda>\<tau>. Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor> Some ` ((H ` ran (heap (fst_snd \<tau>))) - { None }) \<rfloor>\<rfloor>)"

lemma OclAllInstances_generic_defined: "\<tau> \<Turnstile> \<delta> (OclAllInstances_generic pre_post H)"
 apply(simp add: defined_def OclValid_def OclAllInstances_generic_def false_def true_def
                 bot_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_fun_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
 apply(rule conjI)
 apply(rule notI, subst (asm) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject, simp,
       (rule disjI2)+,
       metis bot_option_def option.distinct(1),
       (simp add: bot_option_def null_option_def)+)+
done

lemma OclAllInstances_generic_init_empty:
 assumes [simp]: "\<And>x. pre_post (x, x) = x"
 shows "\<tau>\<^sub>0 \<Turnstile> OclAllInstances_generic pre_post H \<triangleq> Set{}"
by(simp add: StrongEq_def OclAllInstances_generic_def OclValid_def \<tau>\<^sub>0_def mtSet_def)

lemma represented_generic_objects_nonnull:
assumes A: "\<tau> \<Turnstile> ((OclAllInstances_generic pre_post (H::('\<AA>::object \<rightharpoonup> '\<alpha>))) ->includes\<^sub>S\<^sub>e\<^sub>t(x))"
shows      "\<tau> \<Turnstile> not(x \<triangleq> null)"
proof -
    have B: "\<tau> \<Turnstile> \<delta> (OclAllInstances_generic pre_post H)"
         by (simp add: OclAllInstances_generic_defined)
    have C: "\<tau> \<Turnstile> \<upsilon> x"
         by (metis OclIncludes.def_valid_then_def
                   OclIncludes_valid_args_valid A foundation6)
    show ?thesis
    apply(insert A)
    apply(simp add: StrongEq_def  OclValid_def
                    OclNot_def null_def true_def OclIncludes_def B[simplified OclValid_def]
                                                                 C[simplified OclValid_def])
    apply(simp add:OclAllInstances_generic_def)
    apply(erule contrapos_pn)
    apply(subst Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse,
          auto simp: null_fun_def null_option_def bot_option_def)
    done
qed


lemma represented_generic_objects_defined:
assumes A: "\<tau> \<Turnstile> ((OclAllInstances_generic pre_post (H::('\<AA>::object \<rightharpoonup> '\<alpha>))) ->includes\<^sub>S\<^sub>e\<^sub>t(x))"
shows      "\<tau> \<Turnstile> \<delta> (OclAllInstances_generic pre_post H) \<and> \<tau> \<Turnstile> \<delta> x"
by (metis OclAllInstances_generic_defined
          A[THEN represented_generic_objects_nonnull] OclIncludes.defined_args_valid
          A foundation16' foundation18 foundation24 foundation6)


text\<open>One way to establish the actual presence of an object representation in a state is:\<close>

definition "is_represented_in_state fst_snd x H \<tau> = (x \<tau> \<in> (Some o H) ` ran (heap (fst_snd \<tau>)))"

lemma represented_generic_objects_in_state:
assumes A: "\<tau> \<Turnstile> (OclAllInstances_generic pre_post H)->includes\<^sub>S\<^sub>e\<^sub>t(x)"
shows      "is_represented_in_state pre_post x H \<tau>"
proof -
   have B: "(\<delta> (OclAllInstances_generic pre_post H)) \<tau> = true \<tau>"
           by(simp add: OclValid_def[symmetric] OclAllInstances_generic_defined)
   have C: "(\<upsilon> x) \<tau> = true \<tau>"
           by (metis OclValid_def UML_Set.OclIncludes_def assms bot_option_def option.distinct(1) true_def)
   have F: "Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>Some ` (H ` ran (heap (pre_post \<tau>)) - {None})\<rfloor>\<rfloor>) =
            \<lfloor>\<lfloor>Some ` (H ` ran (heap (pre_post \<tau>)) - {None})\<rfloor>\<rfloor>"
           by(subst Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse,simp_all add: bot_option_def)
   show ?thesis
    apply(insert A)
    apply(simp add: is_represented_in_state_def OclIncludes_def OclValid_def ran_def B C image_def true_def)
    apply(simp add: OclAllInstances_generic_def)
    apply(simp add: F)
    apply(simp add: ran_def)
   by(fastforce)
qed


lemma state_update_vs_allInstances_generic_empty:
assumes [simp]: "\<And>a. pre_post (mk a) = a"
shows   "(mk \<lparr>heap=Map.empty, assocs=A\<rparr>) \<Turnstile> OclAllInstances_generic pre_post Type \<doteq> Set{}"
proof -
 have state_update_vs_allInstances_empty:
  "(OclAllInstances_generic pre_post Type) (mk \<lparr>heap=Map.empty, assocs=A\<rparr>) =
   Set{} (mk \<lparr>heap=Map.empty, assocs=A\<rparr>)"
 by(simp add: OclAllInstances_generic_def mtSet_def)
 show ?thesis
  apply(simp only: OclValid_def, subst StrictRefEq\<^sub>S\<^sub>e\<^sub>t.cp0,
        simp only: state_update_vs_allInstances_empty StrictRefEq\<^sub>S\<^sub>e\<^sub>t.refl_ext)
  apply(simp add: OclIf_def valid_def mtSet_def defined_def
                  bot_fun_def null_fun_def null_option_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
 by(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject, (simp add: bot_option_def true_def)+)
qed

text\<open>Here comes a couple of operational rules that allow to infer the value
of \inlineisar+oclAllInstances+ from the context $\tau$. These rules are a special-case
in the sense that they are the only rules that relate statements with \emph{different}
$\tau$'s. For that reason, new concepts like ``constant contexts P'' are necessary
(for which we do not elaborate an own theory for reasons of space limitations;
 in examples, we will prove resulting constraints straight forward by hand).\<close>


lemma state_update_vs_allInstances_generic_including':
assumes [simp]: "\<And>a. pre_post (mk a) = a"
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
  shows "(OclAllInstances_generic pre_post Type)
         (mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>)
         =
         ((OclAllInstances_generic pre_post Type)->including\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (mk \<lparr>heap=\<sigma>',assocs=A\<rparr>)"
proof -
 have drop_none : "\<And>x. x \<noteq> None \<Longrightarrow> \<lfloor>\<lceil>x\<rceil>\<rfloor> = x"
 by(case_tac x, simp+)

 have insert_diff : "\<And>x S. insert \<lfloor>x\<rfloor> (S - {None}) = (insert \<lfloor>x\<rfloor> S) - {None}"
 by (metis insert_Diff_if option.distinct(1) singletonE)

 show ?thesis
  apply(simp add: UML_Set.OclIncluding_def OclAllInstances_generic_defined[simplified OclValid_def],
        simp add: OclAllInstances_generic_def)
  apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp add: bot_option_def, simp add: comp_def,
        subst image_insert[symmetric],
        subst drop_none, simp add: assms)
  apply(case_tac "Type Object", simp add: assms, simp only:,
        subst insert_diff, drule sym, simp)
  apply(subgoal_tac "ran (\<sigma>'(oid \<mapsto> Object)) = insert Object (ran \<sigma>')", simp)
  apply(case_tac "\<not> (\<exists>x. \<sigma>' oid = Some x)")
   apply(rule ran_map_upd, simp)
  apply(simp, erule exE, frule assms, simp)
  apply(subgoal_tac "Object \<in> ran \<sigma>'") prefer 2
   apply(rule ranI, simp)
 by(subst insert_absorb, simp, metis fun_upd_apply)

qed


lemma state_update_vs_allInstances_generic_including:
assumes [simp]: "\<And>a. pre_post (mk a) = a"
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
shows   "(OclAllInstances_generic pre_post Type)
         (mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>)
         =
         ((\<lambda>_. (OclAllInstances_generic pre_post Type)
                 (mk \<lparr>heap=\<sigma>', assocs=A\<rparr>))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>)"
 apply(subst state_update_vs_allInstances_generic_including', (simp add: assms)+,
       subst UML_Set.OclIncluding.cp0,
       simp add: UML_Set.OclIncluding_def)
 apply(subst (1 3) cp_defined[symmetric],
       simp add: OclAllInstances_generic_defined[simplified OclValid_def])

 apply(simp add: defined_def OclValid_def OclAllInstances_generic_def invalid_def
                 bot_fun_def null_fun_def bot_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def null_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_def)
 apply(subst (1 3) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inject)
by(simp add: bot_option_def null_option_def)+



lemma state_update_vs_allInstances_generic_noincluding':
assumes [simp]: "\<And>a. pre_post (mk a) = a"
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object = None"
  shows "(OclAllInstances_generic pre_post Type)
         (mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>)
         =
         (OclAllInstances_generic pre_post Type)
         (mk \<lparr>heap=\<sigma>', assocs=A\<rparr>)"
proof -
 have drop_none : "\<And>x. x \<noteq> None \<Longrightarrow> \<lfloor>\<lceil>x\<rceil>\<rfloor> = x"
 by(case_tac x, simp+)

 have insert_diff : "\<And>x S. insert \<lfloor>x\<rfloor> (S - {None}) = (insert \<lfloor>x\<rfloor> S) - {None}"
 by (metis insert_Diff_if option.distinct(1) singletonE)

 show ?thesis
  apply(simp add: OclIncluding_def OclAllInstances_generic_defined[simplified OclValid_def]
                  OclAllInstances_generic_def)
  apply(subgoal_tac "ran (\<sigma>'(oid \<mapsto> Object)) = insert Object (ran \<sigma>')", simp add: assms)
  apply(case_tac "\<not> (\<exists>x. \<sigma>' oid = Some x)")
   apply(rule ran_map_upd, simp)
  apply(simp, erule exE, frule assms, simp)
  apply(subgoal_tac "Object \<in> ran \<sigma>'") prefer 2
   apply(rule ranI, simp)
  apply(subst insert_absorb, simp)
 by (metis fun_upd_apply)
qed

theorem state_update_vs_allInstances_generic_ntc:
assumes [simp]: "\<And>a. pre_post (mk a) = a"
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  non_type_conform: "Type Object = None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<And>X. const X \<Longrightarrow> const (P X)"
shows "(mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs=A\<rparr> \<Turnstile> P (OclAllInstances_generic pre_post Type)) =
       (mk \<lparr>heap=\<sigma>', assocs=A\<rparr>            \<Turnstile> P (OclAllInstances_generic pre_post Type))"
      (is "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> P ?\<phi>)")
proof -
 have P_cp  : "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>"
             by (metis (full_types) cp_ctxt cp_def)
 have A     : "const (P (\<lambda>_. ?\<phi> ?\<tau>))"
             by(simp add: const_ctxt const_ss)
 have       "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau> \<Turnstile> \<lambda>_. P ?\<phi> ?\<tau>)"
             by(subst foundation23, rule refl)
 also have  "... = (?\<tau> \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>)"
             by(subst P_cp, rule refl)
 also have  "... = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             apply(simp add: OclValid_def)
             by(subst A[simplified const_def], subst const_true[simplified const_def], simp)
 finally have X: "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             by simp
 show ?thesis
 apply(subst X) apply(subst foundation23[symmetric])
 apply(rule StrongEq_L_subst3[OF cp_ctxt])
 apply(simp add: OclValid_def StrongEq_def true_def)
 apply(rule state_update_vs_allInstances_generic_noincluding')
 by(insert oid_def, auto simp: non_type_conform)
qed

theorem state_update_vs_allInstances_generic_tc:
assumes [simp]: "\<And>a. pre_post (mk a) = a"
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  type_conform: "Type Object \<noteq> None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<And>X. const X \<Longrightarrow> const (P X)"
shows "(mk \<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs=A\<rparr> \<Turnstile> P (OclAllInstances_generic pre_post Type)) =
       (mk \<lparr>heap=\<sigma>', assocs=A\<rparr>            \<Turnstile> P ((OclAllInstances_generic pre_post Type)
                                                                ->including\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. \<lfloor>(Type Object)\<rfloor>)))"
       (is "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> P ?\<phi>')")
proof -
 have P_cp  : "\<And>x \<tau>. P x \<tau> = P (\<lambda>_. x \<tau>) \<tau>"
             by (metis (full_types) cp_ctxt cp_def)
 have A     : "const (P (\<lambda>_. ?\<phi> ?\<tau>))"
             by(simp add: const_ctxt const_ss)
 have       "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau> \<Turnstile> \<lambda>_. P ?\<phi> ?\<tau>)"
             by(subst foundation23, rule refl)
 also have  "... = (?\<tau> \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>)"
             by(subst P_cp, rule refl)
 also have  "... = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             apply(simp add: OclValid_def)
             by(subst A[simplified const_def], subst const_true[simplified const_def], simp)
 finally have X: "(?\<tau> \<Turnstile> P ?\<phi>) = (?\<tau>' \<Turnstile> \<lambda>_. P (\<lambda>_. ?\<phi> ?\<tau>)  ?\<tau>')"
             by simp
 let         ?allInstances = "OclAllInstances_generic pre_post Type"
 have        "?allInstances ?\<tau> = \<lambda>_. ?allInstances ?\<tau>'->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_.\<lfloor>\<lfloor>\<lceil>Type Object\<rceil>\<rfloor>\<rfloor>) ?\<tau>"
             apply(rule state_update_vs_allInstances_generic_including)
             by(insert oid_def, auto simp: type_conform)
 also have   "... = ((\<lambda>_. ?allInstances ?\<tau>')->including\<^sub>S\<^sub>e\<^sub>t(\<lambda>_. (\<lambda>_.\<lfloor>\<lfloor>\<lceil>Type Object\<rceil>\<rfloor>\<rfloor>) ?\<tau>') ?\<tau>')"
             by(subst const_OclIncluding[simplified const_def], simp+)
 also have   "... = (?allInstances->including\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. \<lfloor>Type Object\<rfloor>) ?\<tau>')"
             apply(subst UML_Set.OclIncluding.cp0[symmetric])
             by(insert type_conform, auto)
 finally have Y : "?allInstances ?\<tau> = (?allInstances->including\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. \<lfloor>Type Object\<rfloor>) ?\<tau>')"
             by auto
 show ?thesis
      apply(subst X) apply(subst foundation23[symmetric])
      apply(rule StrongEq_L_subst3[OF cp_ctxt])
      apply(simp add: OclValid_def StrongEq_def Y true_def)
 done
qed

declare OclAllInstances_generic_def [simp]

subsubsection\<open>OclAllInstances (@post)\<close>

definition OclAllInstances_at_post :: "('\<AA> :: object \<rightharpoonup> '\<alpha>) \<Rightarrow> ('\<AA>, '\<alpha> option option) Set"
                           ("_ .allInstances'(')")
where  "OclAllInstances_at_post =  OclAllInstances_generic snd"

lemma OclAllInstances_at_post_defined: "\<tau> \<Turnstile> \<delta> (H .allInstances())"
unfolding OclAllInstances_at_post_def
by(rule OclAllInstances_generic_defined)

lemma "\<tau>\<^sub>0 \<Turnstile> H .allInstances() \<triangleq> Set{}"
unfolding OclAllInstances_at_post_def
by(rule OclAllInstances_generic_init_empty, simp)


lemma represented_at_post_objects_nonnull:
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances()) ->includes\<^sub>S\<^sub>e\<^sub>t(x))"
shows      "\<tau> \<Turnstile> not(x \<triangleq> null)"
by(rule represented_generic_objects_nonnull[OF A[simplified OclAllInstances_at_post_def]])


lemma represented_at_post_objects_defined:
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances()) ->includes\<^sub>S\<^sub>e\<^sub>t(x))"
shows      "\<tau> \<Turnstile> \<delta> (H .allInstances()) \<and> \<tau> \<Turnstile> \<delta> x"
unfolding OclAllInstances_at_post_def
by(rule represented_generic_objects_defined[OF A[simplified OclAllInstances_at_post_def]])


text\<open>One way to establish the actual presence of an object representation in a state is:\<close>

lemma
assumes A: "\<tau> \<Turnstile> H .allInstances()->includes\<^sub>S\<^sub>e\<^sub>t(x)"
shows      "is_represented_in_state snd x H \<tau>"
by(rule represented_generic_objects_in_state[OF A[simplified OclAllInstances_at_post_def]])

lemma state_update_vs_allInstances_at_post_empty:
shows   "(\<sigma>, \<lparr>heap=Map.empty, assocs=A\<rparr>) \<Turnstile> Type .allInstances() \<doteq> Set{}"
unfolding OclAllInstances_at_post_def
by(rule state_update_vs_allInstances_generic_empty[OF snd_conv])

text\<open>Here comes a couple of operational rules that allow to infer the value
of \inlineisar+oclAllInstances+ from the context $\tau$. These rules are a special-case
in the sense that they are the only rules that relate statements with \emph{different}
$\tau$'s. For that reason, new concepts like ``constant contexts P'' are necessary
(for which we do not elaborate an own theory for reasons of space limitations;
 in examples, we will prove resulting constraints straight forward by hand).\<close>


lemma state_update_vs_allInstances_at_post_including':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
  shows "(Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>)
         =
         ((Type .allInstances())->including\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<sigma>, \<lparr>heap=\<sigma>',assocs=A\<rparr>)"
unfolding OclAllInstances_at_post_def
by(rule state_update_vs_allInstances_generic_including'[OF snd_conv], insert assms)


lemma state_update_vs_allInstances_at_post_including:
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
shows   "(Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>)
         =
         ((\<lambda>_. (Type .allInstances())
                 (\<sigma>, \<lparr>heap=\<sigma>', assocs=A\<rparr>))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>)"
unfolding OclAllInstances_at_post_def
by(rule state_update_vs_allInstances_generic_including[OF snd_conv], insert assms)



lemma state_update_vs_allInstances_at_post_noincluding':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object = None"
  shows "(Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>)
         =
         (Type .allInstances())
         (\<sigma>, \<lparr>heap=\<sigma>', assocs=A\<rparr>)"
unfolding OclAllInstances_at_post_def
by(rule state_update_vs_allInstances_generic_noincluding'[OF snd_conv], insert assms)

theorem state_update_vs_allInstances_at_post_ntc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  non_type_conform: "Type Object = None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<And>X. const X \<Longrightarrow> const (P X)"
shows   "((\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs=A\<rparr>) \<Turnstile> (P(Type .allInstances()))) =
         ((\<sigma>, \<lparr>heap=\<sigma>', assocs=A\<rparr>)            \<Turnstile> (P(Type .allInstances())))"
unfolding OclAllInstances_at_post_def
by(rule state_update_vs_allInstances_generic_ntc[OF snd_conv], insert assms)

theorem state_update_vs_allInstances_at_post_tc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  type_conform: "Type Object \<noteq> None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<And>X. const X \<Longrightarrow> const (P X)"
shows   "((\<sigma>, \<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs=A\<rparr>) \<Turnstile> (P(Type .allInstances()))) =
         ((\<sigma>, \<lparr>heap=\<sigma>', assocs=A\<rparr>)            \<Turnstile> (P((Type .allInstances())
                                                               ->including\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. \<lfloor>(Type Object)\<rfloor>))))"
unfolding OclAllInstances_at_post_def
by(rule state_update_vs_allInstances_generic_tc[OF snd_conv], insert assms)

subsubsection\<open>OclAllInstances (@pre)\<close>

definition OclAllInstances_at_pre :: "('\<AA> :: object \<rightharpoonup> '\<alpha>) \<Rightarrow> ('\<AA>, '\<alpha> option option) Set"
                           ("_ .allInstances@pre'(')")
where  "OclAllInstances_at_pre = OclAllInstances_generic fst"

lemma OclAllInstances_at_pre_defined: "\<tau> \<Turnstile> \<delta> (H .allInstances@pre())"
unfolding OclAllInstances_at_pre_def
by(rule OclAllInstances_generic_defined)

lemma "\<tau>\<^sub>0 \<Turnstile> H .allInstances@pre() \<triangleq> Set{}"
unfolding OclAllInstances_at_pre_def
by(rule OclAllInstances_generic_init_empty, simp)


lemma represented_at_pre_objects_nonnull:
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances@pre()) ->includes\<^sub>S\<^sub>e\<^sub>t(x))"
shows      "\<tau> \<Turnstile> not(x \<triangleq> null)"
by(rule represented_generic_objects_nonnull[OF A[simplified OclAllInstances_at_pre_def]])

lemma represented_at_pre_objects_defined:
assumes A: "\<tau> \<Turnstile> (((H::('\<AA>::object \<rightharpoonup> '\<alpha>)).allInstances@pre()) ->includes\<^sub>S\<^sub>e\<^sub>t(x))"
shows      "\<tau> \<Turnstile> \<delta> (H .allInstances@pre()) \<and> \<tau> \<Turnstile> \<delta> x"
unfolding OclAllInstances_at_pre_def
by(rule represented_generic_objects_defined[OF A[simplified OclAllInstances_at_pre_def]])


text\<open>One way to establish the actual presence of an object representation in a state is:\<close>

lemma
assumes A: "\<tau> \<Turnstile> H .allInstances@pre()->includes\<^sub>S\<^sub>e\<^sub>t(x)"
shows      "is_represented_in_state fst x H \<tau>"
by(rule represented_generic_objects_in_state[OF A[simplified OclAllInstances_at_pre_def]])


lemma state_update_vs_allInstances_at_pre_empty:
shows   "(\<lparr>heap=Map.empty, assocs=A\<rparr>, \<sigma>) \<Turnstile> Type .allInstances@pre() \<doteq> Set{}"
unfolding OclAllInstances_at_pre_def
by(rule state_update_vs_allInstances_generic_empty[OF fst_conv])

text\<open>Here comes a couple of operational rules that allow to infer the value
of \inlineisar+oclAllInstances@pre+ from the context $\tau$. These rules are a special-case
in the sense that they are the only rules that relate statements with \emph{different}
$\tau$'s. For that reason, new concepts like ``constant contexts P'' are necessary
(for which we do not elaborate an own theory for reasons of space limitations;
 in examples, we will prove resulting constraints straight forward by hand).\<close>


lemma state_update_vs_allInstances_at_pre_including':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
  shows "(Type .allInstances@pre())
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>, \<sigma>)
         =
         ((Type .allInstances@pre())->including\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<lparr>heap=\<sigma>',assocs=A\<rparr>, \<sigma>)"
unfolding OclAllInstances_at_pre_def
by(rule state_update_vs_allInstances_generic_including'[OF fst_conv], insert assms)


lemma state_update_vs_allInstances_at_pre_including:
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object \<noteq> None"
shows   "(Type .allInstances@pre())
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>, \<sigma>)
         =
         ((\<lambda>_. (Type .allInstances@pre())
                 (\<lparr>heap=\<sigma>', assocs=A\<rparr>, \<sigma>))->including\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. \<lfloor>\<lfloor> drop (Type Object) \<rfloor>\<rfloor>))
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>, \<sigma>)"
unfolding OclAllInstances_at_pre_def
by(rule state_update_vs_allInstances_generic_including[OF fst_conv], insert assms)



lemma state_update_vs_allInstances_at_pre_noincluding':
assumes "\<And>x. \<sigma>' oid = Some x \<Longrightarrow> x = Object"
    and "Type Object = None"
  shows "(Type .allInstances@pre())
         (\<lparr>heap=\<sigma>'(oid\<mapsto>Object), assocs=A\<rparr>, \<sigma>)
         =
         (Type .allInstances@pre())
         (\<lparr>heap=\<sigma>', assocs=A\<rparr>, \<sigma>)"
unfolding OclAllInstances_at_pre_def
by(rule state_update_vs_allInstances_generic_noincluding'[OF fst_conv], insert assms)

theorem state_update_vs_allInstances_at_pre_ntc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  non_type_conform: "Type Object = None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<And>X. const X \<Longrightarrow> const (P X)"
shows   "((\<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs=A\<rparr>, \<sigma>) \<Turnstile> (P(Type .allInstances@pre()))) =
         ((\<lparr>heap=\<sigma>', assocs=A\<rparr>, \<sigma>)            \<Turnstile> (P(Type .allInstances@pre())))"
unfolding OclAllInstances_at_pre_def
by(rule state_update_vs_allInstances_generic_ntc[OF fst_conv], insert assms)

theorem state_update_vs_allInstances_at_pre_tc:
assumes oid_def:   "oid\<notin>dom \<sigma>'"
and  type_conform: "Type Object \<noteq> None "
and  cp_ctxt:      "cp P"
and  const_ctxt:   "\<And>X. const X \<Longrightarrow> const (P X)"
shows   "((\<lparr>heap=\<sigma>'(oid\<mapsto>Object),assocs=A\<rparr>, \<sigma>) \<Turnstile> (P(Type .allInstances@pre()))) =
         ((\<lparr>heap=\<sigma>', assocs=A\<rparr>, \<sigma>)            \<Turnstile> (P((Type .allInstances@pre())
                                                               ->including\<^sub>S\<^sub>e\<^sub>t(\<lambda> _. \<lfloor>(Type Object)\<rfloor>))))"
unfolding OclAllInstances_at_pre_def
by(rule state_update_vs_allInstances_generic_tc[OF fst_conv], insert assms)

subsubsection\<open>@post or @pre\<close>

theorem StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq'':
assumes WFF: "WFF \<tau>"
and valid_x: "\<tau> \<Turnstile>(\<upsilon> (x :: ('\<AA>::object,'\<alpha>::object option option)val))"
and valid_y: "\<tau> \<Turnstile>(\<upsilon> y)"
and oid_preserve: "\<And>x. x \<in> ran (heap(fst \<tau>)) \<or> x \<in> ran (heap(snd \<tau>)) \<Longrightarrow>
                        oid_of (H x) = oid_of x"
and xy_together: "\<tau> \<Turnstile> ((H .allInstances()->includes\<^sub>S\<^sub>e\<^sub>t(x) and H .allInstances()->includes\<^sub>S\<^sub>e\<^sub>t(y)) or
                       (H .allInstances@pre()->includes\<^sub>S\<^sub>e\<^sub>t(x) and H .allInstances@pre()->includes\<^sub>S\<^sub>e\<^sub>t(y)))"
 (* x and y must be object representations that exist in either the pre or post state *)
shows "(\<tau> \<Turnstile> (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x y)) = (\<tau> \<Turnstile> (x \<triangleq> y))"
proof -
   have at_post_def : "\<And>x. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<delta> (H .allInstances()->includes\<^sub>S\<^sub>e\<^sub>t(x))"
    apply(simp add: OclIncludes_def OclValid_def
                    OclAllInstances_at_post_defined[simplified OclValid_def])
   by(subst cp_defined, simp)
   have at_pre_def : "\<And>x. \<tau> \<Turnstile> \<upsilon> x \<Longrightarrow> \<tau> \<Turnstile> \<delta> (H .allInstances@pre()->includes\<^sub>S\<^sub>e\<^sub>t(x))"
    apply(simp add: OclIncludes_def OclValid_def
                    OclAllInstances_at_pre_defined[simplified OclValid_def])
   by(subst cp_defined, simp)
   have F: "Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>Some ` (H ` ran (heap (fst \<tau>)) - {None})\<rfloor>\<rfloor>) =
            \<lfloor>\<lfloor>Some ` (H ` ran (heap (fst \<tau>)) - {None})\<rfloor>\<rfloor>"
           by(subst Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse,simp_all add: bot_option_def)
   have F': "Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e \<lfloor>\<lfloor>Some ` (H ` ran (heap (snd \<tau>)) - {None})\<rfloor>\<rfloor>) =
            \<lfloor>\<lfloor>Some ` (H ` ran (heap (snd \<tau>)) - {None})\<rfloor>\<rfloor>"
           by(subst Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e.Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse,simp_all add: bot_option_def)
 show ?thesis
  apply(rule StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq'[OF WFF valid_x valid_y, where H = "Some o H"])
  apply(subst oid_preserve[symmetric], simp, simp add: oid_of_option_def)
  apply(insert xy_together,
        subst (asm) foundation11,
        metis at_post_def defined_and_I valid_x valid_y,
        metis at_pre_def defined_and_I valid_x valid_y)
  apply(erule disjE)
 by(drule foundation5,
    simp add: OclAllInstances_at_pre_def OclAllInstances_at_post_def
              OclValid_def OclIncludes_def true_def F F'
              valid_x[simplified OclValid_def] valid_y[simplified OclValid_def] bot_option_def
         split: if_split_asm,
    simp add: comp_def image_def, fastforce)+
qed

subsection\<open>OclIsNew, OclIsDeleted, OclIsMaintained, OclIsAbsent\<close>

definition OclIsNew:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsNew'(')")
where "X .oclIsNew() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<notin> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<in> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

text\<open>The following predicates --- which are not part of the OCL standard descriptions ---
complete the goal of \inlineisar+oclIsNew+ by describing where an object belongs.
\<close>

definition OclIsDeleted:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsDeleted'(')")
where "X .oclIsDeleted() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<in> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<notin> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

definition OclIsMaintained:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"("(_).oclIsMaintained'(')")
where "X .oclIsMaintained() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<in> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<in> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

definition OclIsAbsent:: "('\<AA>, '\<alpha>::{null,object})val \<Rightarrow> ('\<AA>)Boolean"   ("(_).oclIsAbsent'(')")
where "X .oclIsAbsent() \<equiv> (\<lambda>\<tau> . if (\<delta> X) \<tau> = true \<tau>
                              then \<lfloor>\<lfloor>oid_of (X \<tau>) \<notin> dom(heap(fst \<tau>)) \<and>
                                     oid_of (X \<tau>) \<notin> dom(heap(snd \<tau>))\<rfloor>\<rfloor>
                              else invalid \<tau>)"

lemma state_split : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow>
                     \<tau> \<Turnstile> (X .oclIsNew()) \<or> \<tau> \<Turnstile> (X .oclIsDeleted()) \<or>
                     \<tau> \<Turnstile> (X .oclIsMaintained()) \<or> \<tau> \<Turnstile> (X .oclIsAbsent())"
by(simp add: OclIsDeleted_def OclIsNew_def OclIsMaintained_def OclIsAbsent_def
             OclValid_def true_def, blast)

lemma notNew_vs_others : "\<tau> \<Turnstile> \<delta> X \<Longrightarrow>
                         (\<not> \<tau> \<Turnstile> (X .oclIsNew())) = (\<tau> \<Turnstile> (X .oclIsDeleted()) \<or>
                          \<tau> \<Turnstile> (X .oclIsMaintained()) \<or> \<tau> \<Turnstile> (X .oclIsAbsent()))"
by(simp add: OclIsDeleted_def OclIsNew_def OclIsMaintained_def OclIsAbsent_def
                OclNot_def OclValid_def true_def, blast)

subsection\<open>OclIsModifiedOnly\<close>
subsubsection\<open>Definition\<close>

text\<open>The following predicate---which is not part of the OCL
standard---provides a simple, but powerful means to describe framing
conditions. For any formal approach, be it animation of OCL contracts,
test-case generation or die-hard theorem proving, the specification of
the part of a system transition that \emph{does not change} is of
primordial importance. The following operator establishes the equality
between old and new objects in the state (provided that they exist in
both states), with the exception of those objects.\<close>

definition OclIsModifiedOnly ::"('\<AA>::object,'\<alpha>::{null,object})Set \<Rightarrow> '\<AA> Boolean"
                        ("_->oclIsModifiedOnly'(')")
where "X->oclIsModifiedOnly() \<equiv> (\<lambda>(\<sigma>,\<sigma>').
                           let X' = (oid_of ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e(X(\<sigma>,\<sigma>'))\<rceil>\<rceil>);
                               S = ((dom (heap \<sigma>) \<inter> dom (heap \<sigma>')) - X')
                           in if (\<delta> X) (\<sigma>,\<sigma>') = true (\<sigma>,\<sigma>') \<and> (\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e(X(\<sigma>,\<sigma>'))\<rceil>\<rceil>. x \<noteq> null)
                              then \<lfloor>\<lfloor>\<forall> x \<in> S. (heap \<sigma>) x = (heap \<sigma>') x\<rfloor>\<rfloor>
                              else invalid (\<sigma>,\<sigma>'))"

subsubsection\<open>Execution with Invalid or Null or Null Element as Argument\<close>

lemma "invalid->oclIsModifiedOnly() = invalid"
by(simp add: OclIsModifiedOnly_def)

lemma "null->oclIsModifiedOnly() = invalid"
by(simp add: OclIsModifiedOnly_def)

lemma
 assumes X_null : "\<tau> \<Turnstile> X->includes\<^sub>S\<^sub>e\<^sub>t(null)"
 shows "\<tau> \<Turnstile> X->oclIsModifiedOnly() \<triangleq> invalid"
 apply(insert X_null,
       simp add : OclIncludes_def OclIsModifiedOnly_def StrongEq_def OclValid_def true_def)
 apply(case_tac \<tau>, simp)
 apply(simp split: if_split_asm)
by(simp add: null_fun_def, blast)

subsubsection\<open>Context Passing\<close>

lemma cp_OclIsModifiedOnly : "X->oclIsModifiedOnly() \<tau> = (\<lambda>_. X \<tau>)->oclIsModifiedOnly() \<tau>"
by(simp only: OclIsModifiedOnly_def, case_tac \<tau>, simp only:, subst cp_defined, simp)

subsection\<open>OclSelf\<close>

text\<open>The following predicate---which is not part of the OCL
standard---explicitly retrieves in the pre or post state the original OCL expression
given as argument.\<close>

definition [simp]: "OclSelf x H fst_snd = (\<lambda>\<tau> . if (\<delta> x) \<tau> = true \<tau>
                        then if oid_of (x \<tau>) \<in> dom(heap(fst \<tau>)) \<and> oid_of (x \<tau>) \<in> dom(heap (snd \<tau>))
                             then  H \<lceil>(heap(fst_snd \<tau>))(oid_of (x \<tau>))\<rceil>
                             else invalid \<tau>
                        else invalid \<tau>)"

definition OclSelf_at_pre :: "('\<AA>::object,'\<alpha>::{null,object})val \<Rightarrow>
                      ('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow>
                      ('\<AA>::object,'\<alpha>::{null,object})val" ("(_)@pre(_)")
where "x @pre H = OclSelf x H fst"

definition OclSelf_at_post :: "('\<AA>::object,'\<alpha>::{null,object})val \<Rightarrow>
                      ('\<AA> \<Rightarrow> '\<alpha>) \<Rightarrow>
                      ('\<AA>::object,'\<alpha>::{null,object})val" ("(_)@post(_)")
where "x @post H = OclSelf x H snd"

subsection\<open>Framing Theorem\<close>

lemma all_oid_diff:
 assumes def_x : "\<tau> \<Turnstile> \<delta> x"
 assumes def_X : "\<tau> \<Turnstile> \<delta> X"
 assumes def_X' : "\<And>x. x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> x \<noteq> null"

 defines "P \<equiv> (\<lambda>a. not (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x a))"
 shows "(\<tau> \<Turnstile> X->forAll\<^sub>S\<^sub>e\<^sub>t(a| P a)) = (oid_of (x \<tau>) \<notin> oid_of ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>)"
proof -
 have P_null_bot: "\<And>b. b = null \<or> b = \<bottom> \<Longrightarrow>
                        \<not> (\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>(_:: 'a state \<times> 'a state). x) \<tau> = b \<tau>)"
  apply(erule disjE)
   apply(simp, rule ballI,
         simp add: P_def StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def, rename_tac x',
         subst cp_OclNot, simp,
         subgoal_tac "x \<tau> \<noteq> null \<and> x' \<noteq> null", simp,
         simp add: OclNot_def null_fun_def null_option_def bot_option_def bot_fun_def invalid_def,
         ( metis def_X' def_x foundation16[THEN iffD1]
         | (metis bot_fun_def OclValid_def Set_inv_lemma def_X def_x defined_def valid_def,
            metis def_X' def_x foundation16[THEN iffD1])))+
 done


 have not_inj : "\<And>x y. ((not x) \<tau> = (not y) \<tau>) = (x \<tau> = y \<tau>)"
 by (metis foundation21 foundation22)

 have P_false : "\<exists>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = false \<tau> \<Longrightarrow>
                 oid_of (x \<tau>) \<in> oid_of ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
  apply(erule bexE, rename_tac x')
  apply(simp add: P_def)
  apply(simp only: OclNot3[symmetric], simp only: not_inj)
  apply(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def split: if_split_asm)
    apply(subgoal_tac "x \<tau> \<noteq> null \<and> x' \<noteq> null", simp)
    apply (metis (mono_tags) drop.simps def_x foundation16[THEN iffD1] true_def)
 by(simp add: invalid_def bot_option_def true_def)+

 have P_true : "\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = true \<tau> \<Longrightarrow>
                oid_of (x \<tau>) \<notin> oid_of ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
  apply(subgoal_tac "\<forall>x'\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. oid_of x' \<noteq> oid_of (x \<tau>)")
   apply (metis imageE)
  apply(rule ballI, drule_tac x = "x'" in ballE) prefer 3 apply assumption
   apply(simp add: P_def)
   apply(simp only: OclNot4[symmetric], simp only: not_inj)
   apply(simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def false_def split: if_split_asm)
    apply(subgoal_tac "x \<tau> \<noteq> null \<and> x' \<noteq> null", simp)
    apply (metis def_X' def_x  foundation16[THEN iffD1])
 by(simp add: invalid_def bot_option_def false_def)+

 have bool_split : "\<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> null \<tau> \<Longrightarrow>
                    \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> \<bottom> \<tau> \<Longrightarrow>
                    \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> \<noteq> false \<tau> \<Longrightarrow>
                    \<forall>x\<in>\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>. P (\<lambda>_. x) \<tau> = true \<tau>"
  apply(rule ballI)
  apply(drule_tac x = x in ballE) prefer 3 apply assumption
   apply(drule_tac x = x in ballE) prefer 3 apply assumption
    apply(drule_tac x = x in ballE) prefer 3 apply assumption
     apply (metis (full_types) bot_fun_def OclNot4 OclValid_def foundation16
                               foundation9 not_inj null_fun_def)
 by(fast+)

 show ?thesis
  apply(subst OclForall_rep_set_true[OF def_X], simp add: OclValid_def)
  apply(rule iffI, simp add: P_true)
 by (metis P_false P_null_bot bool_split)
qed

theorem framing:
      assumes modifiesclause:"\<tau> \<Turnstile> (X->excluding\<^sub>S\<^sub>e\<^sub>t(x))->oclIsModifiedOnly()"
      and oid_is_typerepr : "\<tau> \<Turnstile> X->forAll\<^sub>S\<^sub>e\<^sub>t(a| not (StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t x a))"
      shows "\<tau> \<Turnstile> (x @pre P  \<triangleq>  (x @post P))"
 apply(case_tac "\<tau> \<Turnstile> \<delta> x")
 proof - show "\<tau> \<Turnstile> \<delta> x \<Longrightarrow> ?thesis" proof - assume def_x : "\<tau> \<Turnstile> \<delta> x" show ?thesis proof -

 have def_X : "\<tau> \<Turnstile> \<delta> X"
  apply(insert oid_is_typerepr, simp add: UML_Set.OclForall_def OclValid_def split: if_split_asm)
 by(simp add: bot_option_def true_def)

 have def_X' : "\<And>x. x \<in> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil> \<Longrightarrow> x \<noteq> null"
  apply(insert modifiesclause, simp add: OclIsModifiedOnly_def OclValid_def split: if_split_asm)
  apply(case_tac \<tau>, simp split: if_split_asm)
   apply(simp add: UML_Set.OclExcluding_def split: if_split_asm)
    apply(subst (asm) (2) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse)
     apply(simp, (rule disjI2)+)
     apply (metis (hide_lams, mono_tags) Diff_iff Set_inv_lemma def_X)
    apply(simp)
    apply(erule ballE[where P = "\<lambda>x. x \<noteq> null"]) apply(assumption)
    apply(simp)
    apply (metis (hide_lams, no_types) def_x  foundation16[THEN iffD1])
   apply (metis (hide_lams, no_types) OclValid_def def_X def_x foundation20
                                      OclExcluding_valid_args_valid OclExcluding_valid_args_valid'')
 by(simp add: invalid_def bot_option_def)

 have oid_is_typerepr : "oid_of (x \<tau>) \<notin> oid_of ` \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (X \<tau>)\<rceil>\<rceil>"
 by(rule all_oid_diff[THEN iffD1, OF def_x def_X def_X' oid_is_typerepr])

 show ?thesis
  apply(simp add: StrongEq_def OclValid_def true_def OclSelf_at_pre_def OclSelf_at_post_def
                  def_x[simplified OclValid_def])
  apply(rule conjI, rule impI)
   apply(rule_tac f = "\<lambda>x. P \<lceil>x\<rceil>" in arg_cong)
   apply(insert modifiesclause[simplified OclIsModifiedOnly_def OclValid_def])
   apply(case_tac \<tau>, rename_tac \<sigma> \<sigma>', simp split: if_split_asm)
    apply(subst (asm) (2) UML_Set.OclExcluding_def)
    apply(drule foundation5[simplified OclValid_def true_def], simp)
    apply(subst (asm) Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp)
     apply(rule disjI2)+
     apply (metis (hide_lams, no_types) DiffD1 OclValid_def Set_inv_lemma def_x
                                        foundation16 foundation18')
    apply(simp)
    apply(erule_tac x = "oid_of (x (\<sigma>, \<sigma>'))" in ballE) apply simp+
    apply (metis (hide_lams, no_types)
                 DiffD1 image_iff image_insert insert_Diff_single insert_absorb oid_is_typerepr)
   apply(simp add: invalid_def bot_option_def)+
 by blast
 qed qed
qed(simp add: OclSelf_at_post_def OclSelf_at_pre_def OclValid_def StrongEq_def true_def)+


text\<open>As corollary, the framing property can be expressed with only the strong equality
as comparison operator.\<close>

theorem framing':
  assumes wff : "WFF \<tau>"
  assumes modifiesclause:"\<tau> \<Turnstile> (X->excluding\<^sub>S\<^sub>e\<^sub>t(x))->oclIsModifiedOnly()"
  and oid_is_typerepr : "\<tau> \<Turnstile> X->forAll\<^sub>S\<^sub>e\<^sub>t(a| not (x \<triangleq> a))"
  and oid_preserve: "\<And>x. x \<in> ran (heap(fst \<tau>)) \<or> x \<in> ran (heap(snd \<tau>)) \<Longrightarrow>
                          oid_of (H x) = oid_of x"
  and xy_together:
  "\<tau> \<Turnstile> X->forAll\<^sub>S\<^sub>e\<^sub>t(y | (H .allInstances()->includes\<^sub>S\<^sub>e\<^sub>t(x) and H .allInstances()->includes\<^sub>S\<^sub>e\<^sub>t(y)) or
                     (H .allInstances@pre()->includes\<^sub>S\<^sub>e\<^sub>t(x) and H .allInstances@pre()->includes\<^sub>S\<^sub>e\<^sub>t(y)))"
  shows "\<tau> \<Turnstile> (x @pre P  \<triangleq>  (x @post P))"
proof -
 have def_X : "\<tau> \<Turnstile> \<delta> X"
  apply(insert oid_is_typerepr, simp add: UML_Set.OclForall_def OclValid_def split: if_split_asm)
 by(simp add: bot_option_def true_def)
 show ?thesis
  apply(case_tac "\<tau> \<Turnstile> \<delta> x", drule foundation20)
   apply(rule framing[OF modifiesclause])
   apply(rule OclForall_cong'[OF _ oid_is_typerepr xy_together], rename_tac y)
   apply(cut_tac Set_inv_lemma'[OF def_X]) prefer 2 apply assumption
   apply(rule OclNot_contrapos_nn, simp add: StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_def)
     apply(simp add: OclValid_def, subst cp_defined, simp,
           assumption)
   apply(rule StrictRefEq\<^sub>O\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t_vs_StrongEq''[THEN iffD1, OF wff _ _ oid_preserve], assumption+)
 by(simp add: OclSelf_at_post_def OclSelf_at_pre_def OclValid_def StrongEq_def true_def)+
qed

subsection\<open>Miscellaneous\<close>

lemma pre_post_new: "\<tau> \<Turnstile> (x .oclIsNew()) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon>(x @pre H1)) \<and> \<not> (\<tau> \<Turnstile> \<upsilon>(x @post H2))"
by(simp add: OclIsNew_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: if_split_asm)

lemma pre_post_old: "\<tau> \<Turnstile> (x .oclIsDeleted()) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon>(x @pre H1)) \<and> \<not> (\<tau> \<Turnstile> \<upsilon>(x @post H2))"
by(simp add: OclIsDeleted_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: if_split_asm)

lemma pre_post_absent: "\<tau> \<Turnstile> (x .oclIsAbsent()) \<Longrightarrow> \<not> (\<tau> \<Turnstile> \<upsilon>(x @pre H1)) \<and> \<not> (\<tau> \<Turnstile> \<upsilon>(x @post H2))"
by(simp add: OclIsAbsent_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: if_split_asm)

lemma pre_post_maintained: "(\<tau> \<Turnstile> \<upsilon>(x @pre H1) \<or> \<tau> \<Turnstile> \<upsilon>(x @post H2)) \<Longrightarrow> \<tau> \<Turnstile> (x .oclIsMaintained())"
by(simp add: OclIsMaintained_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: if_split_asm)

lemma pre_post_maintained':
"\<tau> \<Turnstile> (x .oclIsMaintained()) \<Longrightarrow> (\<tau> \<Turnstile> \<upsilon>(x @pre (Some o H1)) \<and> \<tau> \<Turnstile> \<upsilon>(x @post (Some o H2)))"
by(simp add: OclIsMaintained_def OclSelf_at_pre_def OclSelf_at_post_def
             OclValid_def StrongEq_def true_def false_def
             bot_option_def invalid_def bot_fun_def valid_def
      split: if_split_asm)

lemma framing_same_state: "(\<sigma>, \<sigma>) \<Turnstile> (x @pre H  \<triangleq>  (x @post H))"
by(simp add: OclSelf_at_pre_def OclSelf_at_post_def OclValid_def StrongEq_def)

section\<open>Accessors on Object\<close>
subsection\<open>Definition\<close>

definition "select_object mt incl smash deref l = smash (foldl incl mt (map deref l))
 \<comment> \<open>smash returns null with \<open>mt\<close> in input (in this case, object contains null pointer)\<close>"

text\<open>The continuation \<open>f\<close> is usually instantiated with a smashing
function which is either the identity @{term id} or, for \inlineocl{0..1} cardinalities
of associations, the @{term OclANY}-selector which also handles the
@{term null}-cases appropriately. A standard use-case for this combinator
is for example:\<close>
term "(select_object mtSet UML_Set.OclIncluding UML_Set.OclANY f  l oid )::('\<AA>, 'a::null)val"

definition "select_object\<^sub>S\<^sub>e\<^sub>t = select_object mtSet UML_Set.OclIncluding id"
definition "select_object_any0\<^sub>S\<^sub>e\<^sub>t f s_set = UML_Set.OclANY (select_object\<^sub>S\<^sub>e\<^sub>t f s_set)"
definition "select_object_any\<^sub>S\<^sub>e\<^sub>t f s_set = 
 (let s = select_object\<^sub>S\<^sub>e\<^sub>t f s_set in
  if s->size\<^sub>S\<^sub>e\<^sub>t() \<triangleq> \<one> then
    s->any\<^sub>S\<^sub>e\<^sub>t()
  else
    \<bottom>
  endif)"
definition "select_object\<^sub>S\<^sub>e\<^sub>q = select_object mtSequence UML_Sequence.OclIncluding id"
definition "select_object_any\<^sub>S\<^sub>e\<^sub>q f s_set = UML_Sequence.OclANY (select_object\<^sub>S\<^sub>e\<^sub>q f s_set)"
definition "select_object\<^sub>P\<^sub>a\<^sub>i\<^sub>r f1 f2 = (\<lambda>(a,b). OclPair (f1 a) (f2 b))"

subsection\<open>Validity and Definedness Properties\<close>

lemma select_fold_exec\<^sub>S\<^sub>e\<^sub>q:
 assumes "list_all (\<lambda>f. (\<tau> \<Turnstile> \<upsilon> f)) l"
 shows "\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (foldl UML_Sequence.OclIncluding Sequence{} l \<tau>)\<rceil>\<rceil> = List.map (\<lambda>f. f \<tau>) l"
proof -
 have def_fold: "\<And>l. list_all (\<lambda>f. \<tau> \<Turnstile> \<upsilon> f) l \<Longrightarrow>
            \<tau> \<Turnstile> (\<delta> foldl UML_Sequence.OclIncluding Sequence{} l)"
  apply(rule rev_induct[where P = "\<lambda>l. list_all (\<lambda>f. (\<tau> \<Turnstile> \<upsilon> f)) l \<longrightarrow> \<tau> \<Turnstile> (\<delta> foldl UML_Sequence.OclIncluding Sequence{} l)", THEN mp], simp)
 by(simp add: foundation10')
 show ?thesis
  apply(rule rev_induct[where P = "\<lambda>l. list_all (\<lambda>f. (\<tau> \<Turnstile> \<upsilon> f)) l \<longrightarrow> \<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (foldl UML_Sequence.OclIncluding Sequence{} l \<tau>)\<rceil>\<rceil> = List.map (\<lambda>f. f \<tau>) l", THEN mp], simp)
    apply(simp add: mtSequence_def)
    apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, (simp | intro impI)+)
   apply(simp add: UML_Sequence.OclIncluding_def, intro conjI impI)
    apply(subst Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp, (rule disjI2)+)
     apply(simp add: list_all_iff foundation18', simp)
   apply(subst (asm) def_fold[simplified (no_asm) OclValid_def], simp, simp add: OclValid_def)
 by (rule assms)
qed

lemma select_fold_exec\<^sub>S\<^sub>e\<^sub>t:
 assumes "list_all (\<lambda>f. (\<tau> \<Turnstile> \<upsilon> f)) l"
 shows "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (foldl UML_Set.OclIncluding Set{} l \<tau>)\<rceil>\<rceil> = set (List.map (\<lambda>f. f \<tau>) l)"
proof -
 have def_fold: "\<And>l. list_all (\<lambda>f. \<tau> \<Turnstile> \<upsilon> f) l \<Longrightarrow>
            \<tau> \<Turnstile> (\<delta> foldl UML_Set.OclIncluding Set{} l)"
  apply(rule rev_induct[where P = "\<lambda>l. list_all (\<lambda>f. (\<tau> \<Turnstile> \<upsilon> f)) l \<longrightarrow> \<tau> \<Turnstile> (\<delta> foldl UML_Set.OclIncluding Set{} l)", THEN mp], simp)
 by(simp add: foundation10')
 show ?thesis
  apply(rule rev_induct[where P = "\<lambda>l. list_all (\<lambda>f. (\<tau> \<Turnstile> \<upsilon> f)) l \<longrightarrow> \<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (foldl UML_Set.OclIncluding Set{} l \<tau>)\<rceil>\<rceil> = set (List.map (\<lambda>f. f \<tau>) l)", THEN mp], simp)
    apply(simp add: mtSet_def)
    apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, (simp | intro impI)+)
   apply(simp add: UML_Set.OclIncluding_def, intro conjI impI)
    apply(subst Abs_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp, (rule disjI2)+)
     apply(simp add: list_all_iff foundation18', simp)
   apply(subst (asm) def_fold[simplified (no_asm) OclValid_def], simp, simp add: OclValid_def)
 by (rule assms)
qed

lemma fold_val_elem\<^sub>S\<^sub>e\<^sub>q:
 assumes "\<tau> \<Turnstile> \<upsilon> (foldl UML_Sequence.OclIncluding Sequence{} (List.map (f p) s_set))"
 shows "list_all (\<lambda>x. (\<tau> \<Turnstile> \<upsilon> (f p x))) s_set"
 apply(rule rev_induct[where P = "\<lambda>s_set. \<tau> \<Turnstile> \<upsilon> foldl UML_Sequence.OclIncluding Sequence{} (List.map (f p) s_set) \<longrightarrow> list_all (\<lambda>x. \<tau> \<Turnstile> \<upsilon> f p x) s_set", THEN mp])
   apply(simp, auto)
    apply (metis (hide_lams, mono_tags) UML_Sequence.OclIncluding.def_valid_then_def UML_Sequence.OclIncluding.defined_args_valid foundation20)+
by(simp add: assms)

lemma fold_val_elem\<^sub>S\<^sub>e\<^sub>t:
 assumes "\<tau> \<Turnstile> \<upsilon> (foldl UML_Set.OclIncluding Set{} (List.map (f p) s_set))"
 shows "list_all (\<lambda>x. (\<tau> \<Turnstile> \<upsilon> (f p x))) s_set"
 apply(rule rev_induct[where P = "\<lambda>s_set. \<tau> \<Turnstile> \<upsilon> foldl UML_Set.OclIncluding Set{} (List.map (f p) s_set) \<longrightarrow> list_all (\<lambda>x. \<tau> \<Turnstile> \<upsilon> f p x) s_set", THEN mp])
   apply(simp, auto)
    apply (metis (hide_lams, mono_tags) foundation10' foundation20)+
by(simp add: assms)

lemma select_object_any_defined\<^sub>S\<^sub>e\<^sub>q:
 assumes def_sel: "\<tau> \<Turnstile> \<delta> (select_object_any\<^sub>S\<^sub>e\<^sub>q f s_set)"
 shows "s_set \<noteq> []"
 apply(insert def_sel, case_tac s_set)
  apply(simp add: select_object_any\<^sub>S\<^sub>e\<^sub>q_def UML_Sequence.OclANY_def select_object\<^sub>S\<^sub>e\<^sub>q_def select_object_def
                  defined_def OclValid_def
                  false_def true_def bot_fun_def bot_option_def
             split: if_split_asm)
  apply(simp add: mtSequence_def, subst (asm) Abs_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e_inverse, simp, simp)
by(simp)

lemma (*select_object_any_defined\<^sub>S\<^sub>e\<^sub>t:*)
 assumes def_sel: "\<tau> \<Turnstile> \<delta> (select_object_any0\<^sub>S\<^sub>e\<^sub>t f s_set)"
 shows "s_set \<noteq> []"
 apply(insert def_sel, case_tac s_set)
  apply(simp add: select_object_any0\<^sub>S\<^sub>e\<^sub>t_def UML_Sequence.OclANY_def select_object\<^sub>S\<^sub>e\<^sub>t_def select_object_def
                  defined_def OclValid_def
                  false_def true_def bot_fun_def bot_option_def
             split: if_split_asm)
by(simp)

lemma select_object_any_defined\<^sub>S\<^sub>e\<^sub>t:
 assumes def_sel: "\<tau> \<Turnstile> \<delta> (select_object_any\<^sub>S\<^sub>e\<^sub>t f s_set)"
 shows "s_set \<noteq> []"
 apply(insert def_sel, case_tac s_set)
  apply(simp add: select_object_any\<^sub>S\<^sub>e\<^sub>t_def UML_Sequence.OclANY_def select_object\<^sub>S\<^sub>e\<^sub>t_def select_object_def
                  defined_def OclValid_def
                  false_def true_def bot_fun_def bot_option_def
                  OclInt0_def OclInt1_def StrongEq_def OclIf_def null_fun_def null_option_def
             split: if_split_asm)
by(simp)

lemma select_object_any_exec0\<^sub>S\<^sub>e\<^sub>q:
 assumes def_sel: "\<tau> \<Turnstile> \<delta> (select_object_any\<^sub>S\<^sub>e\<^sub>q f s_set)"
 shows "\<tau> \<Turnstile> (select_object_any\<^sub>S\<^sub>e\<^sub>q f s_set \<triangleq> f (hd s_set))"
  apply(insert def_sel[simplified foundation16],
        simp add: select_object_any\<^sub>S\<^sub>e\<^sub>q_def foundation22 UML_Sequence.OclANY_def split: if_split_asm)
  apply(case_tac "\<lceil>\<lceil>Rep_Sequence\<^sub>b\<^sub>a\<^sub>s\<^sub>e (select_object\<^sub>S\<^sub>e\<^sub>q f s_set \<tau>)\<rceil>\<rceil>", simp add: bot_option_def, simp)
  apply(simp add: select_object\<^sub>S\<^sub>e\<^sub>q_def select_object_def)
  apply(subst (asm) select_fold_exec\<^sub>S\<^sub>e\<^sub>q)
   apply(rule fold_val_elem\<^sub>S\<^sub>e\<^sub>q, simp add: foundation18' invalid_def)
  apply(simp)
by(drule arg_cong[where f = hd], subst (asm) hd_map, simp add: select_object_any_defined\<^sub>S\<^sub>e\<^sub>q[OF def_sel], simp)

lemma select_object_any_exec\<^sub>S\<^sub>e\<^sub>q:
 assumes def_sel: "\<tau> \<Turnstile> \<delta> (select_object_any\<^sub>S\<^sub>e\<^sub>q f s_set)"
 shows "\<exists>e. List.member s_set e \<and> (\<tau> \<Turnstile> (select_object_any\<^sub>S\<^sub>e\<^sub>q f s_set \<triangleq> f e))"
 apply(insert select_object_any_exec0\<^sub>S\<^sub>e\<^sub>q[OF def_sel])
 apply(rule exI[where x = "hd s_set"], simp)
 apply(case_tac s_set, simp add: select_object_any_defined\<^sub>S\<^sub>e\<^sub>q[OF def_sel])
by (metis list.sel member_rec(1))

lemma (*select_object_any_exec\<^sub>S\<^sub>e\<^sub>t:*)
 assumes def_sel: "\<tau> \<Turnstile> \<delta> (select_object_any0\<^sub>S\<^sub>e\<^sub>t f s_set)"
 shows "\<exists> e. List.member s_set e \<and> (\<tau> \<Turnstile> (select_object_any0\<^sub>S\<^sub>e\<^sub>t f s_set \<triangleq> f e))"
proof -
 have list_all_map: "\<And>P f l. list_all P (List.map f l) = list_all (P o f) l"
 by(induct_tac l, simp_all)

 fix z
 show ?thesis
  when "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (select_object\<^sub>S\<^sub>e\<^sub>t f s_set \<tau>)\<rceil>\<rceil> = z"
  apply(insert that def_sel[simplified foundation16],
        simp add: select_object_any0\<^sub>S\<^sub>e\<^sub>t_def foundation22 UML_Set.OclANY_def null_fun_def split: if_split_asm)

  apply(simp add: select_object\<^sub>S\<^sub>e\<^sub>t_def select_object_def)
  apply(subst (asm) select_fold_exec\<^sub>S\<^sub>e\<^sub>t)
   apply(rule fold_val_elem\<^sub>S\<^sub>e\<^sub>t, simp add: OclValid_def)
  apply(simp add: comp_def)

  apply(case_tac s_set, simp, simp add: false_def true_def, simp)

  proof - fix a l
  show "insert (f a \<tau>) ((\<lambda>x. f x \<tau>) ` set l) = z \<Longrightarrow>
        \<exists>e. List.member (a # l) e \<and> (SOME y. y \<in> z) = f e \<tau>"
   apply(rule list.induct[where P = "\<lambda>l. \<forall>z a. insert (f a \<tau>) ((\<lambda>x. f x \<tau>) ` set l) = z \<longrightarrow>
        (\<exists>e. List.member (a # l) e \<and> ((SOME y. y \<in> z) = f e \<tau>))", THEN spec, THEN spec, THEN mp], intro allI impI)
     proof - fix x xa show "insert (f xa \<tau>) ((\<lambda>x. f x \<tau>) ` set []) = x \<Longrightarrow> \<exists>e. List.member [xa] e \<and> (SOME y. y \<in> x) = f e \<tau>"
      apply(rule exI[where x = xa], simp add: List.member_def)
      apply(subst some_equality[where a = "f xa \<tau>"])
        apply (metis (mono_tags) insertI1)
       apply (metis (mono_tags) empty_iff insert_iff)
     by(simp)
    apply_end(intro allI impI, simp)
    fix x list xa xb
    show " \<forall>x. \<exists>e. List.member (x # list) e \<and> (SOME y. y = f x \<tau> \<or> y \<in> (\<lambda>x. f x \<tau>) ` set list) = f e \<tau> \<Longrightarrow>
       insert (f xb \<tau>) (insert (f x \<tau>) ((\<lambda>x. f x \<tau>) ` set list)) = xa \<Longrightarrow>
       \<exists>e. List.member (xb # x # list) e \<and> (SOME y. y \<in> xa) = f e \<tau>"
     apply(case_tac "x = xb", simp)
      apply(erule allE[where x = xb])
      apply(erule exE)
      proof - fix e show "insert (f xb \<tau>) ((\<lambda>x. f x \<tau>) ` set list) = xa \<Longrightarrow>
         x = xb \<Longrightarrow>
         List.member (xb # list) e \<and> (SOME y. y = f xb \<tau> \<or> y \<in> (\<lambda>x. f x \<tau>) ` set list) = f e \<tau> \<Longrightarrow>
         \<exists>e. List.member (xb # xb # list) e \<and> (SOME y. y \<in> xa) = f e \<tau>"
      apply(rule exI[where x = e], auto)
      by (metis member_rec(1))
     apply_end(case_tac "List.member list x")
      apply_end(erule allE[where x = xb])
      apply_end(erule exE)
      fix e
      let ?P = "\<lambda>y. y = f xb \<tau> \<or> y \<in> (\<lambda>x. f x \<tau>) ` set list"
      show "insert (f xb \<tau>) (insert (f x \<tau>) ((\<lambda>x. f x \<tau>) ` set list)) = xa \<Longrightarrow>
         x \<noteq> xb \<Longrightarrow>
         List.member list x \<Longrightarrow>
         List.member (xb # list) e \<and> (SOME y. y = f xb \<tau> \<or> y \<in> (\<lambda>x. f x \<tau>) ` set list) = f e \<tau> \<Longrightarrow>
         \<exists>e. List.member (xb # x # list) e \<and> (SOME y. y \<in> xa) = f e \<tau>"
       apply(rule exI[where x = e], auto)
        apply (metis member_rec(1))

       apply(subgoal_tac "?P (f e \<tau>)")
        prefer 2
        apply(case_tac "xb = e", simp)
        apply (metis (mono_tags) image_eqI in_set_member member_rec(1)) 

       apply(rule someI2[where a = "f e \<tau>"])
        apply(erule disjE, simp)+
        apply(rule disjI2)+ apply(simp)
oops

lemma select_object_any_exec\<^sub>S\<^sub>e\<^sub>t:
 assumes def_sel: "\<tau> \<Turnstile> \<delta> (select_object_any\<^sub>S\<^sub>e\<^sub>t f s_set)"
 shows "\<exists> e. List.member s_set e \<and> (\<tau> \<Turnstile> (select_object_any\<^sub>S\<^sub>e\<^sub>t f s_set \<triangleq> f e))"
proof -
 have card_singl: "\<And>A a. finite A \<Longrightarrow> card (insert a A) = 1 \<Longrightarrow> A \<subseteq> {a}"
 by (auto, metis Suc_inject card_Suc_eq card_eq_0_iff insert_absorb insert_not_empty singleton_iff)

 have list_same: "\<And>f s_set z' x. f ` set s_set = {z'} \<Longrightarrow> List.member s_set x \<Longrightarrow> f x = z'"
 by (metis (full_types) empty_iff imageI in_set_member insert_iff)

 fix z
 show ?thesis
  when "\<lceil>\<lceil>Rep_Set\<^sub>b\<^sub>a\<^sub>s\<^sub>e (select_object\<^sub>S\<^sub>e\<^sub>t f s_set \<tau>)\<rceil>\<rceil> = z"
  apply(insert that def_sel[simplified foundation16],
        simp add: select_object_any\<^sub>S\<^sub>e\<^sub>t_def foundation22
                  Let_def null_fun_def bot_fun_def OclIf_def
             split: if_split_asm)
  apply(simp add: StrongEq_def OclInt1_def true_def UML_Set.OclSize_def
                  bot_option_def UML_Set.OclANY_def null_fun_def
                  split: if_split_asm)
  apply(subgoal_tac "\<exists>z'. z = {z'}")
   prefer 2
   apply(rule finite.cases[where a = z], simp, simp, simp)
   apply(rule card_singl, simp, simp)
  apply(erule exE, clarsimp)

  apply(simp add: select_object\<^sub>S\<^sub>e\<^sub>t_def select_object_def)
  apply(subst (asm) select_fold_exec\<^sub>S\<^sub>e\<^sub>t)
   apply(rule fold_val_elem\<^sub>S\<^sub>e\<^sub>t, simp add: OclValid_def true_def)
  apply(simp add: comp_def)

  apply(case_tac s_set, simp)
  proof - fix z' a list show "(\<lambda>x. f x \<tau>) ` set s_set = {z'} \<Longrightarrow> s_set = a # list \<Longrightarrow> \<exists>e. List.member s_set e \<and> z' = f e \<tau>"
    apply(drule list_same[where x1 = a])
     apply (metis member_rec(1))
   by (metis (hide_lams, mono_tags) ListMem_iff elem in_set_member)
  qed
qed blast+

end
