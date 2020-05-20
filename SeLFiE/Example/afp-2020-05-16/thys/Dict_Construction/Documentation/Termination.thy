section \<open>Termination heuristics\<close>
text_raw \<open>\label{sec:termination}\<close>

theory Termination
  imports "../Dict_Construction"
begin

text \<open>
  As indicated in the introduction, the newly-defined functions must be proven terminating. In
  general, we cannot reuse the original termination proof, as the following example illustrates:
\<close>

fun f :: "nat \<Rightarrow> nat" where
"f 0 = 0" |
"f (Suc n) = f n"

lemma [code]: "f x = f x" ..

text \<open>
  The invocation of @{theory_text \<open>declassify f\<close>} would fail, because @{const f}'s code equations
  are not terminating.

  Hence, in the general case where users have modified the code equations, we need to fall back
  to an (automated) attempt to prove termination.

  In the remainder of this section, we will illustrate the special case where the user has not
  modified the code equations, i.e., the original termination proof should ``morally'' be still
  applicable. For this, we will perform the dictionary construction manually.
\<close>

\<comment> \<open>Some ML incantations to ensure that the dictionary types are present\<close>
local_setup \<open>Class_Graph.ensure_class @{class plus} #> snd\<close>
local_setup \<open>Class_Graph.ensure_class @{class zero} #> snd\<close>

fun sum_list :: "'a::{plus,zero} list \<Rightarrow> 'a" where
"sum_list [] = 0" |
"sum_list (x # xs) = x + sum_list xs"

text \<open>
  The above function carries two distinct class constraints, which are translated into two
  dictionary parameters:
\<close>

function sum_list' where
"sum_list' d_plus d_zero [] = Groups_zero__class_zero__field d_zero" |
"sum_list' d_plus d_zero (x # xs) = Groups_plus__class_plus__field d_plus x (sum_list' d_plus d_zero xs)"
by pat_completeness auto

text \<open>
  Now, we need to carry out the termination proof of @{const sum_list'}. The @{theory_text function}
  package analyzes the function definition and discovers one recursive call. In pseudo-notation:

  @{text [display] \<open>(d_plus, d_zero, x # xs) \<leadsto> (d_plus, d_zero, xs)\<close>}

  The result of this analysis is captured in the inductive predicate @{const sum_list'_rel}. Its
  introduction rules look as follows:
\<close>

thm sum_list'_rel.intros
\<comment> \<open>@{thm sum_list'_rel.intros}\<close>

text \<open>Compare this to the relation for @{const sum_list}:\<close>

thm sum_list_rel.intros
\<comment> \<open>@{thm sum_list_rel.intros}\<close>

text \<open>
  Except for the additional (unchanging) dictionary arguments, these relations are more or less
  equivalent to each other. There is an important difference, though: @{const sum_list_rel} has
  sort constraints, @{const sum_list'_rel} does not. (This will become important later on.)
\<close>

context
  notes [[show_sorts]]
begin

term sum_list_rel
\<comment> \<open>@{typ \<open>'a::{plus,zero} list \<Rightarrow> 'a::{plus,zero} list \<Rightarrow> bool\<close>}\<close>

term sum_list'_rel
\<comment> \<open>@{typ \<open>'a::type Groups_plus__dict \<times> 'a::type Groups_zero__dict \<times> 'a::type list \<Rightarrow> 'a::type Groups_plus__dict \<times> 'a::type Groups_zero__dict \<times> 'a::type list \<Rightarrow> bool\<close>}\<close>

end

text \<open>
  Let us know discuss the rough concept of the termination proof for @{const sum_list'}. The goal is
  to show that @{const sum_list'_rel} is well-founded. Usually, this is proved by specifying a
  \<^emph>\<open>measure function\<close> that
  \<^enum> maps the arguments to natural numbers
  \<^enum> decreases for each recursive call.
\<close>
text \<open>
  Here, however, we want to instead show that each recursive call in @{const sum_list'} has a
  corresponding recursive call in @{const sum_list}. In other words, we want to show that the
  existing proof of well-foundedness of @{const sum_list_rel} can be lifted to a proof of
  well-foundedness of @{const sum_list'_rel}. This is what the theorem
  @{thm [source=true] wfP_simulate_simple} states:

  @{thm [display=true] wfP_simulate_simple}

  Given any well-founded relation \<open>r\<close> and a function \<open>g\<close> that maps function arguments from \<open>r'\<close> to
  \<open>r\<close>, we can deduce that \<open>r'\<close> is also well-founded.

  For our example, we need to provide a function \<open>g\<close> of type
  @{typ \<open>'b Groups_plus__dict \<times> 'b Groups_zero__dict \<times> 'b list \<Rightarrow> 'a list\<close>}.
  Because the dictionary parameters are not changing, they can safely be dropped by \<open>g\<close>.
  However, because of the sort constraint in @{const sum_list_rel}, the term @{term "snd \<circ> snd"}
  is not a well-typed instantiation for \<open>g\<close>.

  Instead (this is where the heuristic comes in), we assume that the original function
  @{const sum_list} is parametric, i.e., termination does not depend on the elements of the list
  passed to it, but only on the structure of the list. Additionally, we assume that all involved
  type classes have at least one instantiation.

  With this in mind, we can use @{term "map (\<lambda>_. undefined) \<circ> snd \<circ> snd"} as \<open>g\<close>:
\<close>

thm wfP_simulate_simple[where
  r = sum_list_rel and
  r' = sum_list'_rel and
  g = "map (\<lambda>_. undefined) \<circ> snd \<circ> snd"]

text \<open>
  Finally, we can prove the termination of @{const sum_list'}.
\<close>

termination sum_list'
proof -
  have "wfP sum_list'_rel"
  proof (rule wfP_simulate_simple)
    \<comment> \<open>We first need to obtain the well-foundedness theorem for @{const sum_list_rel} from the ML
        guts of the @{theory_text function} package.\<close>
    show "wfP sum_list_rel"
      apply (rule accp_wfPI)
      apply (tactic \<open>resolve_tac @{context} [Function.get_info @{context} @{term sum_list} |> #totality |> the] 1\<close>)
      done

    define g :: "'b Groups_plus__dict \<times> 'b Groups_zero__dict \<times> 'b list \<Rightarrow> 'c::{plus,zero} list" where
      "g = map (\<lambda>_. undefined) \<circ> snd \<circ> snd"

    \<comment> \<open>Prove the simulation of @{const sum_list'_rel} by @{const sum_list_rel} by rule induction.\<close>
    show "sum_list_rel (g x) (g y)" if "sum_list'_rel x y" for x y
      using that
      proof (induction x y rule: sum_list'_rel.induct)
        case (1 d_plus d_zero x xs)
        show ?case
          \<comment> \<open>Unfold the constituent parts of @{term g}:\<close>
          apply (simp only: g_def comp_apply snd_conv list.map)
          \<comment> \<open>Use the corresponding introduction rule of @{const sum_list_rel} and hope for the best:\<close>
          apply (rule sum_list_rel.intros(1))
          done
      qed
  qed

  \<comment> \<open>This is the goal that the @{theory_text function} package expects.\<close>
  then show "\<forall>x. sum_list'_dom x"
    by (rule wfP_implies_dom)
qed

text \<open>This can be automated with a special tactic:\<close>

experiment
begin

termination sum_list'
  apply (tactic \<open>
    Transfer_Termination.termination_tac
      (Function.get_info @{context} @{term sum_list'})
      (Function.get_info @{context} @{term sum_list})
      @{context}
      1\<close>; fail)
  done

end

text \<open>
  A similar technique can be used for making functions defined in locales executable when, for some
  reason, the definition of a ``defs'' locale is not feasible.
\<close>

locale foo =
  fixes A :: "nat"
  assumes "A > 0"
begin

fun f where
"f 0 = A" |
"f (Suc n) = Suc (f n)"

\<comment> \<open>We carry out this proof in the locale for simplicity; a real implementation would probably
    have to set up a local theory properly.\<close>
lemma f_total: "wfP f_rel"
apply (rule accp_wfPI)
apply (tactic \<open>resolve_tac @{context} [Function.get_info @{context} @{term f} |> #totality |> the] 1\<close>)
done

end

\<comment> \<open>The dummy interpretation serves the same purpose as the assumption that class constraints have
    at least one instantiation.\<close>
interpretation dummy: foo 1 by standard simp

function f' where
"f' A 0 = A" |
"f' A (Suc n) = Suc (f' A n)"
by pat_completeness auto

termination f'
  apply (rule wfP_implies_dom)
  apply (rule wfP_simulate_simple[where g = "snd"])
   apply (rule dummy.f_total)
  subgoal for x y
    apply (induction x y rule: f'_rel.induct)
    subgoal
     apply (simp only: snd_conv)
     apply (rule dummy.f_rel.intros)
     done
    done
  done

text \<open>Automatic:\<close>

experiment
begin

termination f'
  apply (tactic \<open>
    Transfer_Termination.termination_tac
      (Function.get_info @{context} @{term f'})
      (Function.get_info @{context} @{term dummy.f})
      @{context}
      1\<close>; fail)
  done

end

end