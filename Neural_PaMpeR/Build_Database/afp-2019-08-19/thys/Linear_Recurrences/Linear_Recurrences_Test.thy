section \<open>Evaluation of the linear recurrence solver\<close>
theory Linear_Recurrences_Test
imports 
  Complex_Main
  "HOL-Library.Code_Target_Numeral"
  Linear_Recurrences_Solver
  Linear_Recurrences_Pretty
  Algebraic_Numbers.Show_Real_Precise
  Show.Show_Complex
  Show_RatFPS
begin

text \<open>
  The rational FPS of the Fibonacci recurrence:
\<close>
value "show (lhr_fps [-1,-1,1] [0,1 :: rat])"

text \<open>
  The closed-form solution of the Fibonacci recurrence:
\<close>
value "show (solve_lhr [-1,-1,1] [0,1 :: complex])"

text \<open>
  The solution in its pretty-printed form:
\<close>
value "show_ratfps_solution (the (solve_lhr [-1,-1,1] [0,1 :: complex]))"

text \<open>
  We can also convince ourselves that the coefficients of the rational FPS we get
  are again the Fibonacci numbers.
\<close>
value "let f = fps_of_ratfps (lhr_fps [-1,-1,1] [0,1 :: rat])
       in  map (fps_nth f) [0..<10]"


text \<open>
  The closed form of $0, 1, 2, 3, 0, 1, 2, 3, \ldots$, which satisfies the
  recurrence $f(n+4) - f(n) = 0$:
\<close>
value "show_ratfps_solution (the (solve_lhr [-1,0,0,0,1] [0,1,2,3 :: complex]))"

text \<open>
  The solution of the recurrence $f(n) + 2 f(n-1) = n \cdot 2^n$ with $f(0) = 1$:
\<close>
value "show_ratfps_solution (the (solve_lir [2, 1] [1 :: complex] [(1, 1, 2)]))"

end
