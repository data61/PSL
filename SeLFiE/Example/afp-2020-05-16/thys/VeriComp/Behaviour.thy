theory Behaviour
  imports Main
begin

datatype 'state behaviour =
  Terminates 'state | Diverges | is_wrong: Goes_wrong 'state

text \<open>
Terminating behaviours are annotated with the last state of the execution in order to compare the result of two executions with the @{const rel_behaviour} relation.

The exact meaning of the three behaviours is defined in the semantics locale
\<close>

end