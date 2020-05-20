section \<open>Formalized Proof \label{sec:proof}\<close>

theory SortKeys
  imports Data "HOL-Library.List_Lexorder" "HOL-Library.Product_Lexorder"
begin

datatype sort_dir =
  Left |
  Right
derive linorder sort_dir

lemma sort_dir_less_def [simp]: "(x < y) = (x = Left \<and> y = Right)" 
  by (cases x, case_tac [!] y, simp_all add:less_sort_dir_def)

datatype 'a sort_key = 
  NonFinal "('a \<times> sort_dir)" "'a sort_key" | 
  Final 'a

type_synonym 'id position = "'id sort_key extended"

fun embed_dir where "embed_dir (x,Left) = (x, 0)" | "embed_dir (x,Right) = (x, Suc (Suc 0))"

lemma embed_dir_inj [simp]: "(embed_dir x = embed_dir y) = (x = y)"
  by (cases x, cases y, case_tac [!] "snd x", case_tac [!] "snd y", simp+)

lemma embed_dir_mono [simp]: "(embed_dir x < embed_dir y) = (x < y)"
  by (cases x, cases y, case_tac [!] "snd x", case_tac [!] "snd y", (simp add:less_sort_dir_def)+)

fun sort_key_embedding :: "'a sort_key \<Rightarrow> ('a \<times> nat) list"
  where 
   "sort_key_embedding (NonFinal x y) = embed_dir x#(sort_key_embedding y)" |
   "sort_key_embedding (Final i) = [(i, Suc 0)]" 

lemma sort_key_embedding_injective: 
  "sort_key_embedding x = sort_key_embedding y \<Longrightarrow> x = y"
  apply (induct x arbitrary: y)
  apply (metis embed_dir_inj list.distinct(1) list.inject sort_key.exhaust
      sort_key_embedding.simps)
  by (metis fst_conv list.distinct(1) list.inject sort_key.exhaust
      sort_key_embedding.simps)

instantiation sort_key :: (ord) ord
begin
definition sort_key_less_eq_def [simp]: 
  "(x :: ('a :: ord) sort_key) \<le> y \<longleftrightarrow> 
    (sort_key_embedding x \<le> sort_key_embedding y)"

definition sort_key_less_def [simp]: 
  "(x :: ('a :: ord) sort_key) < y \<longleftrightarrow> 
    (sort_key_embedding x < sort_key_embedding y)"

instance ..
end

instantiation sort_key :: (order) order
begin
instance by (intro_classes, simp_all add: less_le_not_le sort_key_embedding_injective)
end

instantiation sort_key :: (linorder) linorder
begin
instance by (intro_classes, meson less_imp_le not_le sort_key_less_eq_def)
end

end