(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Code Generation for Basic Matrix Operations\<close>

text \<open>In this theory we implement matrices as arrays of arrays.
  Due to the target language serialization, access to matrix
  entries should be constant time. Hence operations like
  matrix addition, multiplication, etc.~should all have their 
  standard complexity. 

  There might be room for optimizations. 

  To implement the infinite carrier set, we use A.\ Lochbihler's container framework
  \cite{Containers-AFP}.\<close>

theory Matrix_IArray_Impl
imports
  Matrix
  "HOL-Library.IArray"
  Containers.Set_Impl
begin

typedef 'a vec_impl = "{(n,v :: 'a iarray). IArray.length v = n}" by auto
typedef 'a mat_impl = "{(nr,nc,m :: 'a iarray iarray). 
  IArray.length m = nr \<and> IArray.all (\<lambda> r. IArray.length r = nc) m}" 
  by (rule exI[of _ "(0,0,IArray [])"], auto)

setup_lifting type_definition_vec_impl
setup_lifting type_definition_mat_impl

lift_definition vec_impl :: "'a vec_impl \<Rightarrow> 'a vec" is
  "\<lambda> (n,v). (n,mk_vec n (IArray.sub v))" by auto

lift_definition vec_add_impl :: "'a::plus vec_impl \<Rightarrow> 'a vec_impl \<Rightarrow> 'a vec_impl" is
  "\<lambda> (n,v) (m,w).
  (n, IArray.of_fun (\<lambda>i. IArray.sub v i + IArray.sub w i) n)"
by auto

lift_definition mat_impl :: "'a mat_impl \<Rightarrow> 'a mat" is
  "\<lambda> (nr,nc,m). (nr,nc,mk_mat nr nc (\<lambda> (i,j). IArray.sub (IArray.sub m i) j))" by auto

lift_definition vec_of_list_impl :: "'a list \<Rightarrow> 'a vec_impl" is
  "\<lambda> v. (length v, IArray v)" by auto

lift_definition list_of_vec_impl :: "'a vec_impl \<Rightarrow> 'a list" is
  "\<lambda> (n,v). IArray.list_of v" .
  
lift_definition vec_of_fun :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a vec_impl" is
  "\<lambda> n f. (n, IArray.of_fun f n)" by auto

lift_definition mat_of_fun :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> 'a mat_impl" is
  "\<lambda> nr nc f. (nr, nc, IArray.of_fun (\<lambda> i. IArray.of_fun (\<lambda> j. f (i,j)) nc) nr)" by auto

lift_definition vec_index_impl :: "'a vec_impl \<Rightarrow> nat \<Rightarrow> 'a"
  is "\<lambda> (n,v). IArray.sub v" .

lift_definition index_mat_impl :: "'a mat_impl \<Rightarrow> nat \<times> nat \<Rightarrow> 'a"
  is "\<lambda> (nr,nc,m) (i,j). if i < nr then IArray.sub (IArray.sub m i) j 
    else IArray.sub (IArray ([] ! (i - nr))) j" .

lift_definition vec_equal_impl :: "'a vec_impl \<Rightarrow> 'a vec_impl \<Rightarrow> bool"
  is "\<lambda> (n1,v1) (n2,v2). n1 = n2 \<and> v1 = v2" .

lift_definition mat_equal_impl :: "'a mat_impl \<Rightarrow> 'a mat_impl \<Rightarrow> bool"
  is "\<lambda> (nr1,nc1,m1) (nr2,nc2,m2). nr1 = nr2 \<and> nc1 = nc2 \<and> m1 = m2" .

lift_definition dim_vec_impl :: "'a vec_impl \<Rightarrow> nat" is fst .

lift_definition dim_row_impl :: "'a mat_impl \<Rightarrow> nat" is fst .
lift_definition dim_col_impl :: "'a mat_impl \<Rightarrow> nat" is "fst o snd" .

code_datatype vec_impl
code_datatype mat_impl

lemma vec_code[code]: "vec n f = vec_impl (vec_of_fun n f)"
  by (transfer, auto simp: mk_vec_def)

lemma mat_code[code]: "mat nr nc f = mat_impl (mat_of_fun nr nc f)"
  by (transfer, auto simp: mk_mat_def, intro ext, clarsimp, 
  auto intro: undef_cong_mat)

lemma vec_of_list[code]: "vec_of_list v = vec_impl (vec_of_list_impl v)"
  by (transfer, auto simp: mk_vec_def)

lemma list_of_vec_code[code]: "list_of_vec (vec_impl v) = list_of_vec_impl v"
  by (transfer, auto simp: mk_vec_def, case_tac b, auto intro: nth_equalityI)

lemma empty_nth: "\<not> i < length x \<Longrightarrow> x ! i = [] ! (i - length x)"
  by (metis append_Nil2 nth_append)

lemma undef_vec: "\<not> i < length x \<Longrightarrow> undef_vec (i - length x) = x ! i"
  unfolding undef_vec_def by (rule empty_nth[symmetric])
  
lemma vec_index_code[code]: "(vec_impl v) $ i = vec_index_impl v i"
  by (transfer, auto simp: mk_vec_def, case_tac b, auto simp: undef_vec)

lemma index_mat_code[code]: "(mat_impl m) $$ ij = (index_mat_impl m ij :: 'a)"
proof (transfer, unfold o_def, clarify)
  fix m :: "'a iarray iarray" and i j nc
  assume all: "IArray.all (\<lambda>r. IArray.length r = nc) m"
  obtain mm where m: "m = IArray mm" by (cases m)
  with all have all: "\<And> v. v \<in> set mm \<Longrightarrow> IArray.length v = nc" by auto
  show "snd (snd (IArray.length m, nc, mk_mat (IArray.length m) nc (\<lambda>(i, y). m !! i !! y))) (i, j) =
     (if i < IArray.length m then m !! i !! j
        else IArray ([] ! (i - IArray.length m)) !! j)" (is "?l = ?r")
  proof (cases "i < length mm")
    case False
    hence "\<And> f. \<not> i < length (map f [0..<length mm])" by simp
    note [simp] = empty_nth[OF this]
    have "?l = [] ! (i - length mm) ! j" using False unfolding m mk_mat_def undef_mat_def by simp
    also have "\<dots> = ?r" unfolding m by (simp add: False empty_nth[OF False])
    finally show ?thesis .
  next
    case True
    obtain v where mm: "mm ! i = IArray v" by (cases "mm ! i")
    with True all[of "mm ! i"] have len: "length v = nc" unfolding set_conv_nth by force
    from mm True have "?l = map ((!) v) [0..<nc] ! j" (is "_ = ?m") unfolding m mk_mat_def undef_mat_def by simp
    also have "?m = m !! i !! j"
    proof (cases "j < length v")
      case True
      thus ?thesis unfolding m using mm len by auto
    next
      case False
      hence j: "\<not> j < length (map ((!) v) [0..<length v])" by simp
      show ?thesis unfolding m using mm len by (auto simp: empty_nth[OF j] empty_nth[OF False])
    qed
    also have "\<dots> = ?r" using True m by simp
    finally show ?thesis .
  qed
qed

lift_definition (code_dt) mat_of_rows_list_impl :: "nat \<Rightarrow> 'a list list \<Rightarrow> 'a mat_impl option" is
  "\<lambda> n rows. if list_all (\<lambda> r. length r = n) rows then Some (length rows, n, IArray (map IArray rows)) 
  else None" 
  by (auto split: if_splits simp: list_all_iff)

lemma mat_of_rows_list_impl: "mat_of_rows_list_impl n rs = Some A \<Longrightarrow> mat_impl A = mat_of_rows_list n rs" 
  unfolding mat_of_rows_list_def
  by (transfer, auto split: if_splits simp: list_all_iff intro!: cong_mk_mat)
  
lemma mat_of_rows_list_code[code]: "mat_of_rows_list nc vs = 
  (case mat_of_rows_list_impl nc vs of Some A \<Rightarrow> mat_impl A 
  | None \<Rightarrow> mat_of_rows nc (map (\<lambda> v. vec nc (nth v)) vs))"
proof (cases "mat_of_rows_list_impl nc vs")
  case (Some A)
  from mat_of_rows_list_impl[OF this] show ?thesis unfolding Some by simp
next
  case None
  show ?thesis unfolding None unfolding mat_of_rows_list_def mat_of_rows_def
    by (intro eq_matI, auto)  
qed

lemma dim_vec_code[code]: "dim_vec (vec_impl v) = dim_vec_impl v"
  by (transfer, auto)

lemma dim_row_code[code]: "dim_row (mat_impl m) = dim_row_impl m"
  by (transfer, auto)

lemma dim_col_code[code]: "dim_col (mat_impl m) = dim_col_impl m"
  by (transfer, auto)

instantiation vec :: (type)equal
begin
  definition "(equal_vec :: ('a vec \<Rightarrow> 'a vec \<Rightarrow> bool)) = (=)"
instance
  by (intro_classes, auto simp: equal_vec_def)
end

instantiation mat :: (type)equal
begin
  definition "(equal_mat :: ('a mat \<Rightarrow> 'a mat \<Rightarrow> bool)) = (=)"
instance
  by (intro_classes, auto simp: equal_mat_def)
end

lemma veq_equal_code[code]: "HOL.equal (vec_impl (v1 :: 'a vec_impl)) (vec_impl v2) = vec_equal_impl v1 v2"
proof - 
  {
    fix x1 x2 :: "'a list"
    assume len: "length x1 = length x2"
       and index: "(\<lambda>i. if i < length x2 then IArray x1 !! i else undef_vec (i - length (IArray.list_of (IArray x1)))) =
            (\<lambda>i. if i < length x2 then IArray x2 !! i else undef_vec (i - length (IArray.list_of (IArray x2))))"    
    have "x1 = x2"
    proof (intro nth_equalityI[OF len])
      fix i
      assume "i < length x1"
      with fun_cong[OF index, of i] len show "x1 ! i = x2 ! i" by simp
    qed
  } note * = this
  show ?thesis unfolding equal_vec_def
    by (transfer, insert *, auto simp: mk_vec_def, case_tac b, case_tac ba, auto)
qed

lemma mat_equal_code[code]: "HOL.equal (mat_impl (m1 :: 'a mat_impl)) (mat_impl m2) = mat_equal_impl m1 m2"
proof - 
  show ?thesis unfolding equal_mat_def
  proof (transfer, auto, case_tac b, case_tac ba, auto)
    fix x1 x2 :: "'a iarray list" and nc
    assume len: "\<forall>r\<in>set x1. length (IArray.list_of r) = nc"
      "\<forall>r\<in>set x2. length (IArray.list_of r) = nc"
      "length x1 = length x2"
    and index: "mk_mat (length x2) nc (\<lambda>(i, j). x1 ! i !! j) = mk_mat (length x2) nc (\<lambda>(i, j). x2 ! i !! j)"
    show "x1 = x2"
    proof (rule nth_equalityI[OF len(3)])
      fix i
      assume i: "i < length x1"
      obtain ia1 where 1: "x1 ! i = IArray ia1" by (cases "x1 ! i")
      obtain ia2 where 2: "x2 ! i = IArray ia2" by (cases "x2 ! i")
      from i 1 len(1) have l1: "length ia1 = nc" using nth_mem by fastforce
      from i 2 len(2-3) have l2: "length ia2 = nc" using nth_mem by fastforce
      from l1 l2 have l: "length ia1 = length ia2" by simp
      show "x1 ! i = x2 ! i" unfolding 1 2
      proof (simp, rule nth_equalityI[OF l])
        fix j
        assume j: "j < length ia1"
        with fun_cong[OF index, of "(i,j)"] i len(3)
        have "x1 ! i !! j = x2 ! i !! j"
          by (simp add: mk_mat_def l1)
        thus "ia1 ! j = ia2 ! j" unfolding 1 2 by simp
      qed
    qed
  qed
qed  

declare prod.set_conv_list[code del, code_unfold]

derive (eq) ceq mat vec
derive (no) ccompare mat vec
derive (dlist) set_impl mat vec
derive (no) cenum mat vec

lemma carrier_mat_code[code]: "carrier_mat nr nc = Collect_set (\<lambda> A. dim_row A = nr \<and> dim_col A = nc)" by auto
lemma carrier_vec_code[code]: "carrier_vec n = Collect_set (\<lambda> v. dim_vec v = n)" 
  unfolding carrier_vec_def by auto

end
