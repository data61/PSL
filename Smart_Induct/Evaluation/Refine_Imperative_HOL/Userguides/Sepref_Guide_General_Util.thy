section \<open>General Purpose Utilities\<close>
theory Sepref_Guide_General_Util
imports "../IICF/IICF"
begin

text \<open>This userguide documents some of the general purpose utilities that 
  come with the Sepref tool, but are useful in other contexts, too.\<close>

subsection \<open>Methods\<close>
subsubsection \<open>Resolve with Premises\<close>
text \<open>The @{method rprems} resolves the current subgoal with 
  one of its premises. It returns a sequence of possible resolvents.
  Optionally, the number of the premise to resolve with can be specified.
\<close>

subsubsection \<open>First-Order Resolution\<close>
text \<open>The @{method fo_rule} applies a rule with first-order matching.
  It is very useful to be used with theorems like @{thm arg_cong}.\<close>

notepad begin
  have "card {x. 3<x \<and> x<(7::nat)} = card {x. 4\<le>x \<and> x\<le>(6::nat)}"
    apply (fo_rule arg_cong)
    apply auto
    done

  \<comment> \<open>While the first goal could also have been solved with 
    \<open>rule arg_cong[where f=card]\<close>, things would be much more 
    verbose for the following goal. (Such goals actually occur in practice!)\<close>  

  fix f :: "nat set \<Rightarrow> nat set \<Rightarrow> bool"  
  have "\<And>a. f {x. x*2 + a + 3 < 10} {x. 3<x \<and> x<(7::nat)} = f {x. x*2 + a \<le>6} {x. 4\<le>x \<and> x\<le>(6::nat)}"
    apply (fo_rule arg_cong fun_cong cong)+
    apply auto
    done

end


subsubsection \<open>Clarsimp all goals\<close>
text \<open>@{method clarsimp_all} is a \<open>clarsimp\<close> on all goals. 
  It takes the same arguments as \<open>clarsimp\<close>.\<close>

subsubsection \<open>VCG solver\<close>
text \<open>@{method vc_solve} clarsimps all subgoals. 
  Then, it tries to apply a rule specified in the \<open>solve: \<close> argument,
  and tries to solve the result by \<open>auto\<close>. If the goal cannot be solved this way, 
  it is not changed.

  This method is handy to be applied after verification condition generation.
  If \<open>auto\<close> shall be tried on all subgoals, specify \<open>solve: asm_rl\<close>.
\<close>

subsection \<open>Structured Apply Scripts (experimental)\<close>
text \<open>A few variants of the apply command, that document the
  subgoal structure of a proof. They are a lightweight alternative to 
  @{command subgoal}, and fully support schematic variables.
  
  @{command applyS} applies a method to the current subgoal, and fails if the
    subgoal is not solved.

  @{command apply1} applies a method to the current subgoal, and fails if
    the goal is solved or additional goals are created.

  @{command focus} selects the current subgoal, and optionally applies a method.

  @{command applyF} selects the current subgoal and applies a method.

  @{command solved} enforces no subgoals to be left in the current selection, and unselects.

  Note: The selection/unselection mechanism is a primitive version of focusing
    on a subgoal, realized by inserting protect-tags into the goal-state.

\<close>

subsection \<open>Extracting Definitions from Theorems\<close>
text \<open>
  The @{command concrete_definition} can be used to extract parts of a theorem
  as a constant. It is documented at the place where it is defined 
  (ctrl-click to jump there).
\<close>



(* clarsimp_all, vc_solve *)

(*
  Methods
    rprems

  Structured Apply
  concrete_definition, prepare_code_thms

  CONSTRAINT
  PHASES'

*)

end
