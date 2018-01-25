theory Build_Regression_Tree
  imports "../PaMpeR_Base"
  keywords "build_regression_trees" :: thy_decl
  and      "print_out_regression_trees" :: thy_decl
begin

ML_file "../Assertions.ML"

reset_regression_tree_table

build_regression_trees

print_out_regression_trees

end