section "Equality"

theory Derive_Eq
  imports Main "../Derive" Derive_Datatypes
begin

class eq =
  fixes eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

(* Manual instances for nat, unit, prod, and sum *)
instantiation nat and unit:: eq
begin
  definition eq_nat : "eq (x::nat) y \<longleftrightarrow> x = y"
  definition eq_unit_def: "eq (x::unit) y \<longleftrightarrow> True"
  instance ..
end

instantiation prod and sum :: (eq, eq) eq
begin
  definition eq_prod_def: "eq x y \<longleftrightarrow> (eq (fst x) (fst y)) \<and> (eq (snd x) (snd y))"
  definition eq_sum_def: "eq x y = (case x of Inl a \<Rightarrow> (case y of Inl b \<Rightarrow> eq a b | Inr b \<Rightarrow> False)
                                            | Inr a \<Rightarrow> (case y of Inl b \<Rightarrow> False | Inr b \<Rightarrow> eq a b))"

  instance ..
end  

(* nonrecursive test *)

derive_generic eq simple .

(* some tests *)
lemma "eq (A 4) (A 4)" by eval
lemma "eq (A 6) (A 4) \<longleftrightarrow> False" by eval
lemma "eq C C" by eval
lemma "eq (B 4 5) (B 4 5)" by eval
lemma "eq (B 4 4) (A 3) \<longleftrightarrow> False" by eval
lemma "eq C (A 4) \<longleftrightarrow> False" by eval

(* type with parameter *)

derive_generic eq either .

lemma "eq (L (3::nat)) (R 3) \<longleftrightarrow> False" by code_simp
lemma "eq (L (3::nat)) (L 3)" by code_simp
lemma "eq (L (3::nat)) (L 4) \<longleftrightarrow> False" by code_simp

(* recursive types *)
derive_generic eq list .


lemma "eq ([]::(nat list)) []" by eval
lemma "eq ([1,2,3]:: (nat list)) [1,2,3]" by eval
lemma "eq [(1::nat)] [1,2] \<longleftrightarrow> False" by eval

derive_generic eq tree .

lemma "eq Leaf Leaf" by code_simp
lemma "eq (Node (1::nat) Leaf Leaf) Leaf \<longleftrightarrow> False" by eval
lemma "eq (Node (1::nat) Leaf Leaf) (Node (1::nat) Leaf Leaf)" by eval
lemma "eq (Node (1::nat) (Node 2 Leaf Leaf) (Node 3 Leaf Leaf)) (Node (1::nat) (Node 2 Leaf Leaf) (Node 4 Leaf Leaf)) 
    \<longleftrightarrow> False" by eval

(* mutually recursive types *)

derive_generic eq even_nat .
derive_generic eq exp .

lemma "eq Even_Zero Even_Zero" by eval
lemma "eq Even_Zero (Even_Succ (Odd_Succ Even_Zero)) \<longleftrightarrow> False" by eval
lemma "eq (Odd_Succ (Even_Succ (Odd_Succ Even_Zero))) (Odd_Succ (Even_Succ (Odd_Succ Even_Zero)))" by eval
lemma "eq (Odd_Succ (Even_Succ (Odd_Succ Even_Zero))) (Odd_Succ (Even_Succ (Odd_Succ (Even_Succ (Odd_Succ Even_Zero)))))
    \<longleftrightarrow> False" by eval

lemma "eq (Const (1::nat)) (Const (1::nat))" by code_simp
lemma "eq (Const (1::nat)) (Var (1::nat)) \<longleftrightarrow> False" by eval
lemma "eq (Term (Prod (Const (1::nat)) (Factor (Const (2::nat))))) (Term (Prod (Const (1::nat)) (Factor (Const (2::nat)))))"
    by code_simp
lemma "eq (Term (Prod (Const (1::nat)) (Factor (Const (2::nat))))) (Term (Prod (Const (1::nat)) (Factor (Const (3::nat)))))
    \<longleftrightarrow> False" by code_simp

end