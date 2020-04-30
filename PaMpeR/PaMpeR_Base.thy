(*  Title:      PaMpeR_Base.thy
    Author:     Yutaka Nagashima, CIIRC, CTU    
*)
theory PaMpeR_Base
  imports "Build_Regression_Tree/Decision_Tree"
  keywords "which_method" :: diag
  and    "why_method" :: diag
  and    "rank_method" :: diag
  and    "build_regression_trees" :: thy_decl
  and    "print_out_regression_trees" :: thy_decl
  and    "reset_regression_tree_table" :: thy_decl
  and    "read_regression_trees" :: thy_decl
  and    "build_fast_feature_extractor" :: thy_decl
begin

ML_file "Assertions.ML"
ML_file "../PSL/Parser_Combinator.ML"
ML_file "PaMpeR_Interface.ML"

end
