(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Resultants\<close>

text \<open>This theory defines the Sylvester matrix and the resultant and contains 
  basic facts about these notions. After the connection between resultants
  and subresultants has been established, we then use properties of subresultants
  to transfer them to resultants. Remark: these properties have previously been proven
  separately for both resultants and subresultants; and this is the reason for
  splitting the theory of resultants in two parts, namely ``Resultant-Prelim'' and
  ``Resultant'' which is located in the Algebraic-Number AFP-entry. 
\<close> 

theory Resultant_Prelim
imports
  Jordan_Normal_Form.Determinant 
  Polynomial_Interpolation.Ring_Hom_Poly 
begin
  
text \<open>Sylvester matrix\<close>
  
definition sylvester_mat_sub :: "nat \<Rightarrow> nat \<Rightarrow> 'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a :: zero mat" where
  "sylvester_mat_sub m n p q \<equiv>
   mat (m+n) (m+n) (\<lambda> (i,j).
     if i < n then
       if i \<le> j \<and> j - i \<le> m then coeff p (m + i - j) else 0
     else if i - n \<le> j \<and> j \<le> i then coeff q (i-j) else 0)"

definition sylvester_mat :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a :: zero mat" where
  "sylvester_mat p q \<equiv> sylvester_mat_sub (degree p) (degree q) p q"

lemma sylvester_mat_sub_dim[simp]:
  fixes m n p q
  defines "S \<equiv> sylvester_mat_sub m n p q"
  shows "dim_row S = m+n" and "dim_col S = m+n"
  unfolding S_def sylvester_mat_sub_def by auto

lemma sylvester_mat_sub_carrier:
  shows "sylvester_mat_sub m n p q \<in> carrier_mat (m+n) (m+n)" by auto

lemma sylvester_mat_dim[simp]:
  fixes p q
  defines "d \<equiv> degree p + degree q"
  shows "dim_row (sylvester_mat p q) = d" "dim_col (sylvester_mat p q) = d"
  unfolding sylvester_mat_def d_def by auto

lemma sylvester_carrier_mat:
  fixes p q
  defines "d \<equiv> degree p + degree q"
  shows "sylvester_mat p q \<in> carrier_mat d d" unfolding d_def by auto

lemma sylvester_mat_sub_index:
  fixes p q
  assumes i: "i < m+n" and j: "j < m+n"
  shows "sylvester_mat_sub m n p q $$ (i,j) =
    (if i < n then
       if i \<le> j \<and> j - i \<le> m then coeff p (m + i - j) else 0
     else if i - n \<le> j \<and> j \<le> i then coeff q (i-j) else 0)"
  unfolding sylvester_mat_sub_def
  unfolding index_mat(1)[OF i j] by auto

lemma sylvester_index_mat:
  fixes p q
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes i: "i < m+n" and j: "j < m+n"
  shows "sylvester_mat p q $$ (i,j) =
    (if i < n then
       if i \<le> j \<and> j - i \<le> m then coeff p (m + i - j) else 0
     else if i - n \<le> j \<and> j \<le> i then coeff q (i - j) else 0)"
  unfolding sylvester_mat_def
  using sylvester_mat_sub_index[OF i j] unfolding m_def n_def.

lemma sylvester_index_mat2:
  fixes p q :: "'a :: comm_semiring_1 poly"
  defines "m \<equiv> degree p" and "n \<equiv> degree q"
  assumes i: "i < m+n" and j: "j < m+n"
  shows "sylvester_mat p q $$ (i,j) =
    (if i < n then coeff (monom 1 (n - i) * p) (m+n-j)
     else coeff (monom 1 (m + n - i) * q) (m+n-j))"
  apply(subst sylvester_index_mat)
  unfolding m_def[symmetric] n_def[symmetric]
  using i j apply (simp,simp)
  unfolding coeff_monom_mult
  apply(cases "i < n")
  apply (cases "i \<le> j \<and> j - i \<le> m")
  using j m_def apply (force, force simp: coeff_eq_0)
  apply (cases "i - n \<le> j \<and> j \<le> i")
  using i j coeff_eq_0[of q] n_def by auto

lemma sylvester_mat_sub_0[simp]: "sylvester_mat_sub 0 n 0 q = 0\<^sub>m n n"
  unfolding sylvester_mat_sub_def by auto

lemma sylvester_mat_0[simp]: "sylvester_mat 0 q = 0\<^sub>m (degree q) (degree q)"
  unfolding sylvester_mat_def by simp

lemma sylvester_mat_const[simp]:
  fixes a :: "'a :: semiring_1"
  shows "sylvester_mat [:a:] q = a \<cdot>\<^sub>m 1\<^sub>m (degree q)"
    and "sylvester_mat p [:a:] = a \<cdot>\<^sub>m 1\<^sub>m (degree p)"
  by(auto simp: sylvester_index_mat)

lemma sylvester_mat_sub_map:
  assumes f0: "f 0 = 0"
  shows "map_mat f (sylvester_mat_sub m n p q) = sylvester_mat_sub m n (map_poly f p) (map_poly f q)"
    (is "?l = ?r")
proof(rule eq_matI)
  note [simp] = coeff_map_poly[of f, OF f0]
  show dim: "dim_row ?l = dim_row ?r" "dim_col ?l = dim_col ?r" by auto
  fix i j
  assume ij: "i < dim_row ?r" "j < dim_col ?r"
  note ij' = this[unfolded sylvester_mat_sub_dim]
  note ij'' = ij[unfolded dim[symmetric] index_map_mat]
  show "?l $$ (i, j) = ?r $$ (i,j)"
    unfolding index_map_mat(1)[OF ij''] 
    unfolding sylvester_mat_sub_index[OF ij']
    unfolding Let_def
    using f0 by auto
qed


definition resultant :: "'a poly \<Rightarrow> 'a poly \<Rightarrow> 'a :: comm_ring_1" where
  "resultant p q = det (sylvester_mat p q)"

text \<open>Resultant, but the size of the base Sylvester matrix is given.\<close>

definition "resultant_sub m n p q = det (sylvester_mat_sub m n p q)"

lemma resultant_sub: "resultant p q = resultant_sub (degree p) (degree q) p q"
  unfolding resultant_def sylvester_mat_def resultant_sub_def by auto

lemma resultant_const[simp]:
  fixes a :: "'a :: comm_ring_1"
  shows "resultant [:a:] q = a ^ (degree q)"
    and "resultant p [:a:] = a ^ (degree p)"
  unfolding resultant_def unfolding sylvester_mat_const by simp_all

lemma resultant_1[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  shows "resultant 1 p = 1" "resultant p 1 = 1"
  using resultant_const(1) [of 1 p] resultant_const(2) [of p 1]
  by (auto simp add: pCons_one)

lemma resultant_0[simp]:
  fixes p :: "'a :: comm_ring_1 poly"
  assumes "degree p > 0"
  shows "resultant 0 p = 0" "resultant p 0 = 0"
  using resultant_const(1)[of 0 p] resultant_const(2)[of p 0]
  using zero_power assms by auto

lemma (in comm_ring_hom) resultant_map_poly: "degree (map_poly hom p) = degree p \<Longrightarrow>
  degree (map_poly hom q) = degree q \<Longrightarrow> resultant (map_poly hom p) (map_poly hom q) = hom (resultant p q)" 
  unfolding resultant_def sylvester_mat_def sylvester_mat_sub_def hom_det[symmetric]
  by (rule arg_cong[of _ _ det], auto)
    
lemma (in inj_comm_ring_hom) resultant_hom: "resultant (map_poly hom p) (map_poly hom q) = hom (resultant p q)"
  by (rule resultant_map_poly, auto)
    
end
