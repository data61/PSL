(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Converting Matrices to Strings\<close>

text \<open>We just instantiate matrices in the show-class by printing them as lists of lists.\<close>

theory Show_Matrix
imports
  Show.Show
  Matrix
begin

definition shows_vec :: "'a :: show vec \<Rightarrow> shows" where
  "shows_vec v \<equiv> shows (list_of_vec v)"

instantiation vec :: ("show") "show"
begin

definition "shows_prec p (v :: 'a vec) \<equiv> shows_vec v"
definition "shows_list (vs :: 'a vec list) \<equiv> shows_sep shows_vec (shows '', '') vs"

instance 
  by standard (simp_all add: shows_vec_def show_law_simps shows_prec_vec_def shows_list_vec_def)
end

definition shows_mat :: "'a :: show mat \<Rightarrow> shows" where
  "shows_mat A \<equiv> shows (mat_to_list A)"

instantiation mat :: ("show") "show"
begin

definition "shows_prec p (A :: 'a mat) \<equiv> shows_mat A"
definition "shows_list (As :: 'a mat list) \<equiv> shows_sep shows_mat (shows '', '') As"

instance 
  by standard (simp_all add: shows_mat_def show_law_simps shows_prec_mat_def shows_list_mat_def)
end

end
