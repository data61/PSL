(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>List representation\<close>

theory List_Representation
  imports Main
begin

lemma rev_take_Suc: assumes j: "j < length xs"
  shows "rev (take (Suc j) xs) = xs ! j # rev (take j xs)" 
proof -
  from j have xs: "xs = take j xs @ xs ! j # drop (Suc j) xs" by (rule id_take_nth_drop)
  show ?thesis unfolding arg_cong[OF xs, of "\<lambda> xs. rev (take (Suc j) xs)"] 
    by (simp add: min_def)
qed
    
type_synonym 'a list_repr = "'a list \<times> 'a list"   

definition list_repr :: "nat \<Rightarrow> 'a list_repr \<Rightarrow> 'a list \<Rightarrow> bool" where
  "list_repr i ba xs = (i \<le> length xs \<and> fst ba = rev (take i xs) \<and> snd ba = drop i xs)"  

definition of_list_repr :: "'a list_repr \<Rightarrow> 'a list" where
  "of_list_repr ba = (rev (fst ba) @ snd ba)" 
  
lemma of_list_repr: "list_repr i ba xs \<Longrightarrow> of_list_repr ba = xs" 
  unfolding of_list_repr_def list_repr_def by auto
    
definition get_nth_i :: "'a list_repr \<Rightarrow> 'a" where
  "get_nth_i ba = hd (snd ba)" 

definition get_nth_im1 :: "'a list_repr \<Rightarrow> 'a" where
  "get_nth_im1 ba = hd (fst ba)" 
  
lemma get_nth_i: "list_repr i ba xs \<Longrightarrow> i < length xs \<Longrightarrow> get_nth_i ba = xs ! i" 
  unfolding list_repr_def get_nth_i_def 
  by (auto simp: hd_drop_conv_nth) 

lemma get_nth_im1: "list_repr i ba xs \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> get_nth_im1 ba = xs ! (i - 1)" 
  unfolding list_repr_def get_nth_im1_def 
  by (cases i, auto simp: rev_take_Suc) 
    
definition update_i :: "'a list_repr \<Rightarrow> 'a \<Rightarrow> 'a list_repr" where
  "update_i ba x = (fst ba, x # tl (snd ba))" 
  
lemma Cons_tl_drop_update: "i < length xs \<Longrightarrow> x # tl (drop i xs) = drop i (xs[i := x])"
proof (induct i arbitrary: xs)
  case (0 xs)
  thus ?case by (cases xs, auto)
next
  case (Suc i xs)
  thus ?case by (cases xs, auto)
qed
  
lemma update_i: "list_repr i ba xs \<Longrightarrow> i < length xs \<Longrightarrow> list_repr i (update_i ba x) (xs [i := x])" 
  unfolding update_i_def list_repr_def 
  by (auto simp: Cons_tl_drop_update)
    
definition update_im1 :: "'a list_repr \<Rightarrow> 'a \<Rightarrow> 'a list_repr" where
  "update_im1 ba x = (x # tl (fst ba), snd ba)" 

lemma update_im1: "list_repr i ba xs \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> list_repr i (update_im1 ba x) (xs [i - 1 := x])" 
  unfolding update_im1_def list_repr_def 
  by (cases i, auto simp: rev_take_Suc)
  
lemma tl_drop_Suc: "tl (drop i xs) = drop (Suc i) xs"
proof (induct i arbitrary: xs)
  case (0 xs) thus ?case by (cases xs, auto)
next
  case (Suc i xs) thus ?case by (cases xs, auto)
qed
    
definition inc_i :: "'a list_repr \<Rightarrow> 'a list_repr" where
  "inc_i ba = (case ba of (b,a) \<Rightarrow> (hd a # b, tl a))" 
    
lemma inc_i: "list_repr i ba xs \<Longrightarrow> i < length xs \<Longrightarrow> list_repr (Suc i) (inc_i ba) xs" 
  unfolding list_repr_def inc_i_def by (cases ba, auto simp: rev_take_Suc hd_drop_conv_nth tl_drop_Suc) 

definition dec_i :: "'a list_repr \<Rightarrow> 'a list_repr" where
  "dec_i ba = (case ba of (b,a) \<Rightarrow> (tl b, hd b # a))" 
    
lemma dec_i: "list_repr i ba xs \<Longrightarrow> i \<noteq> 0 \<Longrightarrow> list_repr (i - 1) (dec_i ba) xs" 
  unfolding list_repr_def dec_i_def 
  by (cases ba; cases i, auto simp: rev_take_Suc hd_drop_conv_nth Cons_nth_drop_Suc) 

lemma dec_i_Suc: "list_repr (Suc i) ba xs \<Longrightarrow> list_repr i (dec_i ba) xs" 
  using dec_i[of "Suc i" ba xs] by auto

end
