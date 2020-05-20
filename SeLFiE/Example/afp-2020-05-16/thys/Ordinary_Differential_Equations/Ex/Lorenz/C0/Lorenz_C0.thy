theory Lorenz_C0
  imports
    Lorenz_Approximation.Lorenz_Approximation
begin

lemma check_lines_c0: "check_lines False ordered_lines"
  by (parallel_check (* "output/lorenz_c0_" *) _ 15 9)

end
