(* Title:      Kleene algebra with tests
   Author:     Alasdair Armstrong, Victor B. F. Gomes, Georg Struth
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
*)

section \<open>Test Dioids\<close>

theory Test_Dioid
  imports Kleene_Algebra.Dioid
begin

text \<open>
  Tests are embedded in a weak dioid, a dioid without the right annihilation and left distributivity axioms, using an 
  operator $t$ defined by a complementation operator. This allows us to use tests in weak settings, such as Probabilistic Kleene Algebra and Demonic Refinement Algebra.
\<close>

subsection \<open>Test Monoids\<close>

class n_op =
  fixes n_op :: "'a \<Rightarrow> 'a" ("n _" [90] 91)

class test_monoid = monoid_mult + n_op +
  assumes tm1 [simp]: "n n 1 = 1" 
  and tm2 [simp]: "n x \<cdot> n n x = n 1" 
  and tm3: "n x \<cdot> n (n n z \<cdot> n n y) = n (n (n x \<cdot> n y) \<cdot> n (n x \<cdot> n z))"

begin 

(*no_notation zero_class.zero ("0")*)

definition a_zero :: "'a" ("o") where 
  "o \<equiv> n 1"

abbreviation "t x \<equiv> n n x"

definition n_add_op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<oplus>" 65) where 
  "x \<oplus> y \<equiv> n (n x \<cdot> n y)"

lemma "n 1 \<cdot> x = n 1"
(*nitpick*) oops

lemma "x \<cdot> n 1 = n 1"
(*nitpick*) oops

lemma "n 1 \<cdot> x = n 1 \<Longrightarrow> n x \<cdot> y \<cdot> t z = n 1 \<Longrightarrow> n x \<cdot> y = n x \<cdot> y \<cdot> n z  "
(*nitpick*) oops

lemma n_t_closed [simp]: "t (n x) = n x"
proof -
  have "\<And>x y. n x \<cdot> n (t (n x) \<cdot> t y) = t (n x \<cdot> n y)"
    by (simp add: local.tm3)
  thus ?thesis
   by (metis (no_types) local.mult_1_right local.tm1 local.tm2 local.tm3 mult_assoc)
qed

lemma mult_t_closed [simp]: "t (n x \<cdot> n y) = n x \<cdot> n y"
  by (metis local.mult_1_right local.tm1 local.tm2 local.tm3 n_t_closed)

lemma n_comm_var: "n (n x \<cdot> n y) = n (n y \<cdot> n x)"
  by (metis local.mult_1_left local.tm1 local.tm3 n_t_closed)

lemma n_comm: "n x \<cdot> n y = n y \<cdot> n x"
  using mult_t_closed n_comm_var by fastforce

lemma huntington1 [simp]: "n (n (n n x \<cdot> n y) \<cdot> n (n n x \<cdot> n n y)) = n n x"
  by (metis local.mult_1_right local.tm1 local.tm2 local.tm3)

lemma huntington2 [simp]: "n (n x \<oplus> n n y) \<oplus> n (n x \<oplus> n y) = n n x"
  by (simp add: n_add_op_def)

lemma add_assoc: "n x \<oplus> (n y \<oplus> n z) = (n x \<oplus> n y) \<oplus> n z"
  by (simp add: mult_assoc n_add_op_def)

lemma t_mult_closure: "t x = x \<Longrightarrow> t y = y \<Longrightarrow> t (x \<cdot> y) = x \<cdot> y"
  by (metis mult_t_closed)

lemma n_t_compl [simp]: "n x \<oplus> t x = 1"
  using n_add_op_def local.tm1 local.tm2 by presburger

lemma zero_least1 [simp]: "o \<oplus> n x = n x"
  by (simp add: a_zero_def n_add_op_def)

lemma zero_least2 [simp]: "o \<cdot> n x = o"
  by (metis a_zero_def local.tm2 local.tm3 mult_assoc mult_t_closed zero_least1)

lemma zero_least3 [simp]: "n x \<cdot> o  = o"
  using a_zero_def n_comm zero_least2 by fastforce

lemma one_greatest1 [simp]: "1 \<oplus> n x = 1"
  by (metis (no_types) a_zero_def local.tm1 n_add_op_def n_comm_var zero_least3)

lemma one_greatest2 [simp]: "n x \<oplus> 1 = 1"
  by (metis n_add_op_def n_comm_var one_greatest1)

lemma n_add_idem [simp]: "n x \<oplus> n x = n x"
  by (metis huntington1 local.mult_1_right n_t_closed n_t_compl n_add_op_def)

lemma n_mult_idem [simp]: "n x \<cdot> n x = n x"
  by (metis mult_t_closed n_add_idem n_add_op_def)

lemma n_preserve [simp]: "n x \<cdot> n y \<cdot> n x = n y \<cdot> n x"
  by (metis mult_assoc n_comm n_mult_idem)

lemma n_preserve2 [simp]: "n x \<cdot> n y \<cdot> t x = o"
  by (metis a_zero_def local.tm2 mult_assoc n_comm zero_least3)

lemma de_morgan1 [simp]: "n (n x \<cdot> n y) = t x \<oplus> t y"
  by (simp add: n_add_op_def)

lemma de_morgan4 [simp]: "n (t x \<oplus> t y) = n x \<cdot> n y"
  using n_add_op_def mult_t_closed n_t_closed by presburger

lemma n_absorb1 [simp]: "n x \<oplus> n x \<cdot> n y = n x"
  by (metis local.mult_1_right local.tm1 local.tm3 one_greatest2 n_add_op_def)

lemma n_absorb2 [simp]: "n x \<cdot> (n x \<oplus> n y) = n x"
  by (metis mult_t_closed n_absorb1 n_add_op_def)

lemma n_distrib1: "n x \<cdot> (n y \<oplus> n z) = (n x \<cdot> n y) \<oplus> (n x \<cdot> n z)"
  using local.tm3 n_comm_var  n_add_op_def by presburger

lemma n_distrib1_opp: "(n x \<oplus> n y) \<cdot> n z  = (n x \<cdot> n z) \<oplus> (n y \<cdot> n z)"
  using n_add_op_def n_comm n_distrib1 by presburger

lemma n_distrib2: "n x \<oplus> n y \<cdot> n z = (n x \<oplus> n y) \<cdot> (n x \<oplus> n z)"
  by (metis mult_t_closed n_distrib1 n_mult_idem  n_add_op_def)

lemma n_distrib2_opp: "n x \<cdot> n y \<oplus> n z = (n x \<oplus> n z) \<cdot> (n y \<oplus> n z)"
  by (metis de_morgan1 mult_t_closed n_distrib1_opp n_add_op_def)

definition ts_ord :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "x \<sqsubseteq> y = (n x \<cdot> n y = n y)"

lemma ts_ord_alt: "n x \<sqsubseteq> n y \<longleftrightarrow> n x \<oplus> n y = n y"
  by (metis mult_t_closed n_t_closed ts_ord_def n_add_op_def)

lemma ts_ord_refl: "n x \<sqsubseteq> n x"
  by (simp add: ts_ord_def)

lemma ts_ord_trans: "n x \<sqsubseteq> n y \<Longrightarrow> n y \<sqsubseteq> n z \<Longrightarrow> n x \<sqsubseteq> n z"
  by (metis mult_assoc ts_ord_def)

lemma ts_ord_antisym: "n x \<sqsubseteq> n y \<Longrightarrow> n y \<sqsubseteq> n x \<Longrightarrow> n x = n y"
  by (metis n_add_idem n_comm ts_ord_def n_add_op_def)

lemma ts_ord_mult_isol: "n x \<sqsubseteq> n y \<Longrightarrow> n z \<cdot> n x \<sqsubseteq> n z \<cdot> n y"
proof -
  assume "n x \<sqsubseteq> n y"
  hence "n (n (n z \<cdot> n x) \<cdot> n (n z \<cdot> n y)) = n z \<cdot> n y"
    by (metis mult_t_closed n_add_idem n_distrib1 ts_ord_def n_add_op_def)
  thus ?thesis
    by (metis mult_t_closed ts_ord_def)
qed

lemma ts_ord_mult_isor: "n x \<sqsubseteq> n y \<Longrightarrow> n x \<cdot> n z \<sqsubseteq> n y \<cdot> n z"
  using n_comm ts_ord_mult_isol by auto

lemma ts_ord_add_isol: "n x \<sqsubseteq> n y \<Longrightarrow> n z \<oplus> n x \<sqsubseteq> n z \<oplus> n y"
  by (metis mult_assoc mult_t_closed n_mult_idem ts_ord_def n_add_op_def)

lemma ts_ord_add_isor: "n x \<sqsubseteq> n y \<Longrightarrow> n x \<oplus> n z \<sqsubseteq> n y \<oplus> n z"
  using n_add_op_def n_comm ts_ord_add_isol by presburger

lemma ts_ord_anti: "n x \<sqsubseteq> n y \<Longrightarrow> t y \<sqsubseteq> t x"
  by (metis n_absorb2 n_add_idem n_comm ts_ord_def n_add_op_def)

lemma ts_ord_anti_iff: "n x \<sqsubseteq> n y \<longleftrightarrow> t y \<sqsubseteq> t x"
  using ts_ord_anti by force

lemma zero_ts_ord: "o \<sqsubseteq> n x"
  by (simp add: a_zero_def ts_ord_def)

lemma n_subid: "n x \<sqsubseteq> 1"
  by (simp add: a_zero_def[symmetric] ts_ord_def)

lemma n_mult_lb1: "n x \<cdot> n y \<sqsubseteq> n x"
  by (metis (no_types) local.mult_1_right local.tm1 n_comm n_subid ts_ord_mult_isor)

lemma n_mult_lb2: "n x \<cdot> n y \<sqsubseteq> n y"
  by (metis n_comm n_mult_lb1)

lemma n_mult_glbI: "n z \<sqsubseteq> n x \<Longrightarrow>  n z \<sqsubseteq> n y \<Longrightarrow> n z \<sqsubseteq> n x \<cdot> n y"
  by (metis n_t_closed ts_ord_anti_iff ts_ord_def ts_ord_mult_isol)

lemma n_mult_glb: "n z \<sqsubseteq> n x \<and> n z \<sqsubseteq> n y \<longleftrightarrow> n z \<sqsubseteq> n x \<cdot> n y"
  by (metis mult_t_closed n_mult_glbI n_mult_lb1 n_mult_lb2 ts_ord_trans)

lemma n_add_ub1: "n x \<sqsubseteq> n x \<oplus> n y"
  by (metis (no_types) n_absorb2 n_mult_lb2 n_add_op_def)

lemma n_add_ub2: "n y \<sqsubseteq> n x \<oplus> n y"
  by (metis n_add_ub1 n_comm_var n_add_op_def)

lemma n_add_lubI: "n x \<sqsubseteq> n z \<Longrightarrow> n y \<sqsubseteq> n z \<Longrightarrow> n x \<oplus> n y \<sqsubseteq> n z"
  by (metis ts_ord_add_isol ts_ord_alt) 

lemma n_add_lub: "n x \<sqsubseteq> n z \<and> n y \<sqsubseteq> n z \<longleftrightarrow> n x \<oplus> n y \<sqsubseteq> n z"
  by (metis n_add_lubI n_add_op_def n_add_ub1 n_add_ub2 ts_ord_trans)

lemma n_galois1: "n x \<sqsubseteq> n y \<oplus> n z \<longleftrightarrow> n x \<cdot> t y \<sqsubseteq> n z"
proof 
  assume "n x \<sqsubseteq> n y \<oplus> n z"
  hence "n x \<cdot> t y \<sqsubseteq> (n y \<oplus> n z ) \<cdot> t y"
    by (metis n_add_op_def ts_ord_mult_isor)
  also have "... = n y \<cdot> t y \<oplus> n z \<cdot> t y"
    using n_add_op_def local.tm3 n_comm by presburger    
  also have "... = n z \<cdot> t y"
    using a_zero_def local.tm2 n_distrib2 zero_least1 by presburger
  finally show "n x \<cdot> t y \<sqsubseteq> n z"
    by (metis mult_t_closed n_mult_glb)
next
  assume a: "n x \<cdot> t y \<sqsubseteq> n z" 
  have "n x = t (n x \<cdot> (n y \<oplus> t y))"
    using local.mult_1_right n_t_closed n_t_compl by presburger
  also have "... = t (n x \<cdot> n y \<oplus> n x \<cdot> t y)"
    using n_distrib1 by presburger
  also have "...  \<sqsubseteq> t (n y \<oplus> n x \<cdot> t y)"
    by (metis calculation local.mult_1_right mult_t_closed n_add_op_def n_add_ub2 n_distrib2 n_t_compl)
  finally show "n x \<sqsubseteq> n y \<oplus> n z"
    by (metis (no_types, hide_lams) a mult_t_closed ts_ord_add_isol ts_ord_trans n_add_op_def)
qed

lemma n_galois2: "n x \<sqsubseteq> t y \<oplus> n z \<longleftrightarrow> n x \<cdot> n y \<sqsubseteq> n z"
  by (metis n_galois1 n_t_closed)

lemma n_distrib_alt: "n x \<cdot> n z = n y \<cdot> n z \<Longrightarrow> n x \<oplus> n z = n y \<oplus> n z \<Longrightarrow> n x = n y"
proof -
  assume a: "n x \<cdot> n z = n y \<cdot> n z" and b: "n x \<oplus> n z = n y \<oplus> n z"
  have "n x = n x \<oplus> n x \<cdot> n z"
    using n_absorb1 by presburger
  also have "... = n x \<oplus> n y \<cdot> n z"
    using a by presburger
  also have "... = (n x \<oplus> n y) \<cdot> (n x \<oplus> n z)"
    using n_distrib2 by blast
  also have "... = (n y \<oplus> n x) \<cdot> (n y \<oplus> n z)"
    using n_add_op_def b n_comm by presburger 
  also have "... = n y \<cdot> (n x \<oplus> n z)"
    by (metis a b n_distrib1 n_distrib2 n_mult_idem)
  also have "... = n y \<cdot> (n y \<oplus> n z)"
    using b by presburger 
  finally show "n x = n y"
    using n_absorb2 by presburger
qed

lemma n_dist_var1: "(n x \<oplus> n y) \<cdot> (t x \<oplus> n z) = t x \<cdot> n y \<oplus> n x \<cdot> n z"
proof - 
  have "(n x \<oplus> n y) \<cdot> (t x \<oplus> n z) = n x \<cdot> t x \<oplus> n y \<cdot> t x \<oplus> (n x \<cdot> n z \<oplus> n y \<cdot> n z)" 
    using n_add_op_def n_distrib1 n_distrib1_opp by presburger
  also have "... = t x \<cdot> n y \<oplus> (n x \<cdot> n z \<oplus> (n x \<oplus> t x) \<cdot> t (n y \<cdot> n z))"
    using n_add_op_def local.mult_1_left local.tm1 local.tm2 n_comm n_t_closed by presburger
  also have "... = t x \<cdot> n y \<oplus> (n x \<cdot> n z \<oplus> (n x \<cdot> n y \<cdot> n z \<oplus> t x \<cdot> n y \<cdot> n z))"
    by (metis mult_assoc mult_t_closed n_distrib1_opp)
  also have "... = (t x \<cdot> n y \<oplus> t x \<cdot> n y \<cdot> n z) \<oplus> (n x \<cdot> n z \<oplus> n x \<cdot> n y \<cdot> n z)"
proof -
  have f1: "\<And>a aa ab. n n (n (a::'a) \<cdot> (n aa \<cdot> n ab)) = n a \<cdot> (n aa \<cdot> n ab)"
    by (metis (full_types) mult_t_closed)
  have "\<And>a aa ab. n (a::'a) \<cdot> (n aa \<cdot> n ab) = n aa \<cdot> (n ab \<cdot> n a)"
    by (metis mult_assoc n_comm)
  hence "n (n (n y \<cdot> n n x) \<cdot> n n (n (n x \<cdot> n z) \<cdot> (n (n x \<cdot> n y \<cdot> n z) \<cdot> n (n y \<cdot> n n x \<cdot> n z)))) = n (n (n y \<cdot> n n x) \<cdot> n (n y \<cdot> n n x \<cdot> n z) \<cdot> (n (n x \<cdot> n z) \<cdot> n (n x \<cdot> n y \<cdot> n z)))"
    using f1 mult_assoc by presburger
  thus ?thesis
    using mult_t_closed n_add_op_def n_comm by presburger
qed
     also have "... = (t x \<cdot> n y \<oplus> t (t x \<cdot> n y) \<cdot> n z) \<oplus> (n x \<cdot> n z \<oplus> t (n x \<cdot> n z) \<cdot> n y)"
    using mult_assoc mult_t_closed n_comm by presburger
  also have "... = (t x \<cdot> n y \<cdot> (1 \<oplus> n z)) \<oplus> (n x \<cdot> n z \<cdot> (1 \<oplus> n y))"
    by (metis a_zero_def n_add_op_def local.mult_1_right local.tm1 mult_t_closed n_absorb1 zero_least2)
  finally show ?thesis
    by simp
qed

lemma n_dist_var2: "n (n x \<cdot> n y \<oplus> t x \<cdot> n z) = n x \<cdot> t y \<oplus> t x \<cdot> t z"
  by (metis (no_types) n_add_op_def n_dist_var1 n_t_closed)

end

subsection \<open>Test Near-Semirings\<close>
 
class test_near_semiring_zerol = ab_near_semiring_one_zerol + n_op + plus_ord + 
  assumes test_one [simp]: "n n 1 = 1" 
  and test_mult [simp]: "n n (n x \<cdot> n y) = n x \<cdot> n y" 
  and test_mult_comp [simp]: "n x \<cdot> n n x = 0"
  and test_de_morgan [simp]: "n (n n x \<cdot> n n y) = n x + n y"  

begin

lemma n_zero [simp]: "n 0 = 1"
proof -
  have "n 0 = n (n 1 \<cdot> n n 1)"
    using local.test_mult_comp by presburger
  also have "... = n (n 1 \<cdot> 1)"
    by simp
  finally show ?thesis
    by simp
qed

lemma n_one [simp]: "n 1 = 0"
proof -
  have "n 1 = n 1 \<cdot> 1"
    by simp
  also have "... = n 1 \<cdot> n n 1"
    by simp
  finally show ?thesis
    using test_mult_comp by metis
qed

lemma one_idem [simp]: "1 + 1 = 1"
proof -
  have "1 + 1 = n n 1 + n n 1"
    by simp
  also have "... = n (n n n 1 \<cdot> n n n 1)"
    using local.test_de_morgan by presburger
  also have "... = n (0 \<cdot> n n n 1)"
    by simp
  also have "... = n 0"
    by simp
  finally show ?thesis
    by simp
qed

subclass near_dioid_one_zerol
proof 
  fix x
  have "x + x = (1 + 1) \<cdot> x"
    using local.distrib_right' local.mult_onel by presburger
  also have "... = 1 \<cdot> x"
    by simp
  finally show "x + x = x"
    by simp
qed

lemma t_n_closed [simp]: "n n (n x) = n x"
proof -
  have "n n (n x) = n (n n x \<cdot> 1)"
    by simp
  also have "... = n (n n x \<cdot> n n 1)"
    by simp
  also have "... = n x + n 1"
    using local.test_de_morgan by presburger
  also have "... = n x + 0"
    by simp
  finally show ?thesis 
    by simp
qed

lemma t_de_morgan_var1 [simp]: "n (n x \<cdot> n y) = n n x + n n y"
  by (metis local.test_de_morgan t_n_closed)

lemma n_mult_comm: "n x \<cdot> n y = n y \<cdot> n x"
proof -
  have "n x \<cdot> n y = n n (n x \<cdot> n y)"
    by (metis local.test_mult)
  also have "... = n (n n x + n n y)"
    by simp
  also have "... = n (n n y + n n x)"
    by (metis add_commute)
  also have "... = n n (n y \<cdot> n x)"
    by simp
  finally show ?thesis
    by (metis local.test_mult)
qed
  
lemma tm3': "n x \<cdot> n (n n z \<cdot> n n y) = n (n (n x \<cdot> n y) \<cdot> n (n x \<cdot> n z))"
proof -
  have "n x \<cdot> n (n n z \<cdot> n n y) = n (n n y \<cdot> n n z) \<cdot> n x"
    using n_mult_comm by presburger
  also have "... = (n y + n z) \<cdot> n x"
    by simp
  also have "... = n y \<cdot> n x + n z \<cdot> n x"
    by simp
  also have "... = n n (n x \<cdot> n y) + n n (n x \<cdot> n z)" 
    by (metis local.test_mult n_mult_comm)
  finally show ?thesis
    by (metis t_de_morgan_var1)
qed

subclass test_monoid
proof
  show "n n 1 = 1"
    by simp
  show "\<And>x. n x \<cdot> n n x = n 1"
    by simp
  show " \<And>x z y. n x \<cdot> n (n n z \<cdot> n n y) = n (n (n x \<cdot> n y) \<cdot> n (n x \<cdot> n z))"
    using tm3' by blast
qed

lemma ord_transl [simp]: "n x \<le> n y \<longleftrightarrow> n x \<sqsubseteq> n y"
  by (simp add: local.join.sup.absorb_iff2 local.n_add_op_def local.ts_ord_alt)

lemma add_transl [simp]: "n x + n y = n x \<oplus> n y"
  by (simp add: local.n_add_op_def)

lemma zero_trans: "0 = o"
  by (metis local.a_zero_def n_one)

definition test :: "'a \<Rightarrow> bool" where
  "test p \<equiv> t p = p"

notation n_op ("!_" [101] 100)

lemma test_prop: "(\<forall>x. test x \<longrightarrow> P x) \<longleftrightarrow> (\<forall>x. P (t x))"
  by (metis test_def t_n_closed)

lemma test_propI: "test x \<Longrightarrow> P x \<Longrightarrow> P (t x)"
  by (simp add: test_def)

lemma test_propE [elim!]: "test x \<Longrightarrow> P (t x) \<Longrightarrow> P x"
  by (simp add: test_def)

lemma test_comp_closed [simp]: "test p \<Longrightarrow> test (!p)"
  by (simp add: test_def)

lemma test_double_comp_var: "test p \<Longrightarrow> p = !(!p)"
  by auto

lemma test_mult_closed: "test p \<Longrightarrow> test q \<Longrightarrow> test (p \<cdot> q)"
  by (metis local.test_mult test_def)

lemma t_add_closed [simp]: "t (n x + n y) = n x + n y"
  by (metis local.test_de_morgan t_n_closed)

lemma test_add_closed: "test p \<Longrightarrow> test q \<Longrightarrow> test (p + q)"
  by (metis t_add_closed test_def)

lemma test_mult_comm_var: "test p \<Longrightarrow> test q \<Longrightarrow> p \<cdot> q = q \<cdot> p"
  using n_mult_comm by auto

lemma t_zero [simp]: "t 0 = 0"
  by simp

lemma test_zero_var: "test 0"
  by (simp add: test_def)

lemma test_one_var: "test 1"
  by (simp add: test_def)

lemma test_preserve: "test p \<Longrightarrow> test q \<Longrightarrow> p \<cdot> q \<cdot> p = q \<cdot> p"
  by auto

lemma test_preserve2: "test p \<Longrightarrow> test q \<Longrightarrow> p \<cdot> q \<cdot> !p = 0"
  by (metis local.a_zero_def local.n_preserve2 n_one test_double_comp_var)

 
lemma n_subid': "n x \<le> 1"
  using local.n_subid n_zero ord_transl by blast

lemma test_subid: "test p \<Longrightarrow> p \<le> 1"
  using n_subid' by auto

lemma test_mult_idem_var [simp]: "test p \<Longrightarrow> p \<cdot> p = p"
  by auto

lemma n_add_comp [simp]: "n x + t x = 1"
  by simp

lemma n_add_comp_var [simp]: "t x + n x = 1"
  by (simp add: add_commute)

lemma test_add_comp [simp]: "test p \<Longrightarrow> p + !p = 1"
  using n_add_comp by fastforce
 
lemma test_comp_mult1 [simp]: "test p \<Longrightarrow> !p \<cdot> p = 0"
  by auto

lemma test_comp_mult2 [simp]: "test p \<Longrightarrow> p \<cdot> !p = 0"
  using local.test_mult_comp by fastforce

lemma test_comp: "test p \<Longrightarrow> \<exists>q. test q \<and> p + q = 1 \<and> p \<cdot> q = 0"
  using test_add_comp test_comp_closed test_comp_mult2 by blast

lemma n_absorb1' [simp]: "n x + n x \<cdot> n y = n x"
  by (metis add_transl local.de_morgan4 local.n_absorb1)

lemma test_absorb1 [simp]: "test p \<Longrightarrow> test q \<Longrightarrow> p + p \<cdot> q = p"
  by auto

lemma n_absorb2' [simp]: "n x \<cdot> (n x + n y) = n x"
  by simp

lemma test_absorb2: "test p \<Longrightarrow> test q \<Longrightarrow> p \<cdot> (p + q) = p"
  by auto

lemma n_distrib_left: "n x \<cdot> (n y + n z) = (n x \<cdot> n y) + (n x \<cdot> n z)"
  by (metis (no_types) add_transl local.de_morgan4 local.n_distrib1)

lemma test_distrib_left: "test p \<Longrightarrow>  test q \<Longrightarrow> test r \<Longrightarrow> p \<cdot> (q + r) = p \<cdot> q + p \<cdot> r"
  using n_distrib_left by auto

lemma de_morgan1': "test p \<Longrightarrow> test q \<Longrightarrow> !p + !q = !(p \<cdot> q)"
  by auto

lemma n_de_morgan_var2 [simp]: "n (n x + n y) = t x \<cdot> t y"
  by (metis local.test_de_morgan local.test_mult)

lemma n_de_morgan_var3 [simp]: "n (t x + t y) = n x \<cdot> n y"
  by simp

lemma de_morgan2: "test p \<Longrightarrow> test q \<Longrightarrow> !p \<cdot> !q = !(p + q)"
  by auto

lemma de_morgan3: "test p \<Longrightarrow> test q \<Longrightarrow> !(!p + !q) = p \<cdot> q"
  using local.de_morgan1' local.t_mult_closure test_def by auto  

lemma de_morgan4': "test p \<Longrightarrow> test q \<Longrightarrow> !(!p \<cdot> !q) = p + q"
  by auto

lemma n_add_distr: "n x + (n y \<cdot> n z) = (n x + n y) \<cdot> (n x + n z)"
  by (metis add_transl local.n_distrib2 n_de_morgan_var3)

lemma test_add_distr: "test p \<Longrightarrow> test q \<Longrightarrow> test r \<Longrightarrow> p + q \<cdot> r = (p + q) \<cdot> (p + r)"
  using n_add_distr by fastforce

lemma n_add_distl: "(n x \<cdot> n y) + n z = (n x + n z) \<cdot> (n y + n z)"
  by (simp add: add_commute n_add_distr)

lemma test_add_distl_var: "test p \<Longrightarrow> test q \<Longrightarrow> test r \<Longrightarrow> p \<cdot> q + r = (p + r) \<cdot> (q + r)"
  by (simp add: add_commute test_add_distr)

lemma n_ord_def_alt: "n x \<le> n y \<longleftrightarrow> n x \<cdot> n y = n x"
  by (metis (no_types) local.join.sup.absorb_iff2 local.n_absorb2' local.n_mult_lb2 ord_transl)

lemma test_leq_mult_def_var: "test p \<Longrightarrow> test q \<Longrightarrow> p \<le> q \<longleftrightarrow> p \<cdot> q = p"
  using n_ord_def_alt by auto

lemma n_anti: "n x \<le> n y \<Longrightarrow> t y \<le> t x"
  using local.ts_ord_anti ord_transl by blast

lemma n_anti_iff: "n x \<le> n y \<longleftrightarrow> t y \<le> t x"
  using n_anti by fastforce

lemma test_comp_anti_iff: "test p \<Longrightarrow> test q \<Longrightarrow> p \<le> q \<longleftrightarrow> !q \<le> !p"
  using n_anti_iff by auto

lemma n_restrictl: "n x \<cdot> y \<le> y"
  using local.mult_isor n_subid' by fastforce

lemma test_restrictl: "test p \<Longrightarrow> p \<cdot> x \<le> x"
  by (auto simp: n_restrictl)

lemma n_mult_lb1': "n x \<cdot> n y \<le> n x"
  by (simp add: local.join.sup.orderI)

lemma test_mult_lb1: "test p \<Longrightarrow> test q \<Longrightarrow> p \<cdot> q \<le> p"
  by (auto simp: n_mult_lb1')

lemma n_mult_lb2': "n x \<cdot> n y \<le> n y"
  by (fact local.n_restrictl)

lemma test_mult_lb2: "test p \<Longrightarrow> test q \<Longrightarrow> p \<cdot> q \<le> q"
  by (rule test_restrictl)

lemma n_mult_glbI': "n z \<le> n x \<Longrightarrow>  n z \<le> n y \<Longrightarrow> n z \<le> n x \<cdot> n y"
  by (metis mult_isor n_ord_def_alt)

lemma test_mult_glbI:  "test p \<Longrightarrow> test q \<Longrightarrow> test r \<Longrightarrow> p \<le> q \<Longrightarrow> p \<le> r \<Longrightarrow> p \<le> q \<cdot> r"
  by (metis (no_types) local.mult_isor test_leq_mult_def_var)

lemma n_mult_glb': "n z \<le> n x \<and> n z \<le> n y \<longleftrightarrow> n z \<le> n x \<cdot> n y"
  using local.order_trans n_mult_glbI' n_mult_lb1' n_mult_lb2' by blast

lemma test_mult_glb: "test p \<Longrightarrow> test q \<Longrightarrow> test r \<Longrightarrow> p \<le> q \<and> p \<le> r \<longleftrightarrow> p \<le> q \<cdot> r"
  using local.n_mult_glb' by force

lemma n_galois1': "n x \<le> n y + n z \<longleftrightarrow> n x \<cdot> t y \<le> n z"
proof -
  have "n x \<le> n y + n z \<longleftrightarrow> n x \<sqsubseteq> n y \<oplus> n z"
    by (metis local.test_de_morgan ord_transl n_add_op_def)
  also have "... \<longleftrightarrow> n x \<cdot> t y \<sqsubseteq> n z"
    using local.n_galois1 by auto
  also have "... \<longleftrightarrow> n x \<cdot> t y \<le> n z"
    by (metis local.test_mult ord_transl)
  finally show ?thesis
    by simp
qed

lemma test_galois1: "test p \<Longrightarrow> test q \<Longrightarrow> test r \<Longrightarrow> p \<le> q + r \<longleftrightarrow> p \<cdot> !q \<le> r"
  using n_galois1' by auto

lemma n_galois2': "n x \<le> t y + n z \<longleftrightarrow> n x \<cdot> n y \<le> n z"
  using local.n_galois1' by auto

lemma test_galois2: "test p \<Longrightarrow> test q \<Longrightarrow> test r \<Longrightarrow> p \<le> !q + r \<longleftrightarrow> p \<cdot> q \<le> r"
  using test_galois1 by auto

lemma n_huntington2: "n (n x + t y) + n (n x + n y) = n n x"
  by simp

lemma test_huntington2: "test p \<Longrightarrow> test q \<Longrightarrow> !(p + q) + !(p + !q) = !p"
proof -
  assume a1: "test p"
  assume a2: "test q"
  have "p = !(!p)"
    using a1 test_double_comp_var by blast
  thus ?thesis
    using a2 by (metis (full_types) n_huntington2 test_double_comp_var)
qed

lemma n_kat_1_opp: "n x \<cdot> y \<cdot> n z = y \<cdot> n z \<longleftrightarrow> t x \<cdot> y \<cdot> n z = 0"
proof
  assume "n x \<cdot> y \<cdot> n z = y \<cdot> n z"
  hence "t x \<cdot> y \<cdot> n z = t x \<cdot> n x \<cdot> y \<cdot> n z"
    by (simp add: mult_assoc)
  thus " t x \<cdot> y \<cdot> n z = 0"
    by (simp add: n_mult_comm)
next
  assume "n n x \<cdot> y \<cdot> n z = 0"
  hence "n x \<cdot> y \<cdot> n z = 1 \<cdot> y \<cdot> n z"
    by (metis local.add_zerol local.distrib_right' n_add_comp t_n_closed)
  thus "n x \<cdot> y \<cdot> n z = y \<cdot> n z"
    by auto
qed

lemma test_eq4: "test p \<Longrightarrow> test q \<Longrightarrow> !p \<cdot> x \<cdot> !q = x \<cdot> !q \<longleftrightarrow> p \<cdot> x \<cdot> !q = 0"
  using n_kat_1_opp by auto

lemma n_kat_1_var: "t x \<cdot> y \<cdot> t z = y \<cdot> t z \<longleftrightarrow> n x \<cdot> y \<cdot> t z = 0"
  by (simp add: n_kat_1_opp)

lemma test_kat_1: "test p \<Longrightarrow> test q \<Longrightarrow> p \<cdot> x \<cdot> q = x \<cdot> q \<longleftrightarrow> !p \<cdot> x \<cdot> q = 0"
  using n_kat_1_var by auto

lemma n_kat_21_opp:  "y \<cdot> n z \<le> n x \<cdot> y \<Longrightarrow> n x \<cdot> y \<cdot> n z = y \<cdot> n z"
proof -
  assume "y \<cdot> n z \<le> n x \<cdot> y"
  hence "y \<cdot> n z + n x \<cdot> y = n x \<cdot> y"
    by (meson local.join.sup_absorb2)
  hence "n x \<cdot> y \<cdot> n z = y \<cdot> n z + (n x \<cdot> (y \<cdot> n z) + 0)"
    by (metis local.add_zeror local.distrib_right' local.n_mult_idem mult_assoc)
  thus ?thesis
    by (metis local.add_zeror local.distrib_right' local.join.sup_absorb2 local.join.sup_left_commute local.mult_onel local.n_subid')
qed

lemma test_kat_21_opp: "test p \<Longrightarrow> test q \<Longrightarrow> x \<cdot> q \<le> p \<cdot> x \<longrightarrow> p \<cdot> x \<cdot> q = x \<cdot> q"
  using n_kat_21_opp by auto

lemma  " n x \<cdot> y \<cdot> n z = y \<cdot> n z \<Longrightarrow> y \<cdot> n z \<le> n x \<cdot> y"
  (*nitpick*) oops

lemma n_distrib_alt': "n x \<cdot> n z = n y \<cdot> n z \<Longrightarrow> n x + n z = n y + n z \<Longrightarrow> n x = n y"
  using local.n_distrib_alt by auto

lemma test_distrib_alt: "test p \<Longrightarrow> test q \<Longrightarrow> test r \<Longrightarrow> p \<cdot> r = q \<cdot> r \<and> p + r = q + r \<longrightarrow> p = q"
  using n_distrib_alt by auto

lemma n_eq1: "n x \<cdot> y \<le> z \<and> t x \<cdot> y \<le> z \<longleftrightarrow> y \<le> z"
proof -
  have  "n x \<cdot> y \<le> z \<and> t x \<cdot> y \<le> z \<longleftrightarrow> n x \<cdot> y + t x \<cdot> y \<le> z"
    by simp
  also have "... \<longleftrightarrow> (n x + t x) \<cdot> y \<le> z"
    using local.distrib_right' by presburger
  finally show ?thesis
    by auto
qed

lemma test_eq1: "test p \<Longrightarrow> y \<le> x \<longleftrightarrow> p \<cdot> y \<le> x \<and> !p \<cdot> y \<le> x"
  using n_eq1 by auto

lemma n_dist_var1': "(n x + n y) \<cdot> (t x + n z) = t x \<cdot> n y + n x \<cdot> n z"
  by (metis add_transl local.n_dist_var1 local.test_mult)

lemma test_dist_var1: "test p \<Longrightarrow> test q \<Longrightarrow> test r \<Longrightarrow> (p + q) \<cdot> (!p + r) = !p \<cdot> q + p \<cdot> r"
  using n_dist_var1' by fastforce

lemma n_dist_var2': "n (n x \<cdot> n y + t x \<cdot> n z) = n x \<cdot> t y + t x \<cdot> t z"
proof -
  have f1: "!x \<cdot> !y = !(!(!x \<cdot> !y))"
    using n_de_morgan_var3 t_de_morgan_var1 by presburger
  have "!(!(!x)) = !x"
    by simp
  thus ?thesis
    using f1 by (metis (no_types) n_de_morgan_var3 n_dist_var1' t_de_morgan_var1)
qed

lemma test_dist_var2: "test p \<Longrightarrow> test q \<Longrightarrow> test r \<Longrightarrow> !(p \<cdot> q + !p \<cdot> r) = (p \<cdot> !q + !p \<cdot> !r)"
  using n_dist_var2' by auto

lemma test_restrictr: "test p \<Longrightarrow> x \<cdot> p \<le> x"
  (* nitpick *) oops

lemma test_eq2: "test p \<Longrightarrow> z \<le> p \<cdot> x + !p \<cdot> y \<longleftrightarrow> p \<cdot> z \<le> p \<cdot> x \<and> !p \<cdot> z \<le> !p \<cdot> y"
  (* nitpick *) oops

lemma test_eq3: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> q \<longleftrightarrow> p \<cdot> x \<le> x \<cdot> q"
  (* nitpick *) oops

lemma test1: "\<lbrakk>test p; test q; p \<cdot> x \<cdot> !q = 0\<rbrakk> \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; x \<cdot> !q = !p \<cdot> x \<cdot> !q\<rbrakk> \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> q"
  (* nitpick *) oops

lemma comm_add: "\<lbrakk>test p; p\<cdot>x = x\<cdot>p; p\<cdot>y = y\<cdot>p\<rbrakk> \<Longrightarrow> p\<cdot>(x + y) = (x + y)\<cdot>p"
  (* nitpick *) oops

lemma comm_add_var: "\<lbrakk>test p; test q; test r; p\<cdot>x = x\<cdot>p; p\<cdot>y = y\<cdot>p\<rbrakk> \<Longrightarrow> p\<cdot>(q\<cdot>x + r\<cdot>y) = (q\<cdot>x + r\<cdot>y)\<cdot>p"
  (* nitpick *) oops

lemma "test p \<Longrightarrow> p \<cdot> x = x \<cdot> p \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> p \<and> !p \<cdot> x = !p \<cdot> x \<cdot> !p "
  (* nitpick *) oops

lemma test_distrib: "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p + q)\<cdot>(q\<cdot>y + !q\<cdot>x) = q\<cdot>y + !q\<cdot>p\<cdot>x"
  (* nitpick *) oops

end

subsection \<open>Test Near Semirings with Distributive Tests\<close>

text \<open>
  We now make the assumption that tests distribute over finite sums of arbitrary elements from the left.
  This can be justified in models such as multirelations and probabilistic predicate transformers.
\<close>

class test_near_semiring_zerol_distrib = test_near_semiring_zerol  +
  assumes n_left_distrib: "n x \<cdot> (y + z) = n x \<cdot> y + n x \<cdot> z"

begin

lemma n_left_distrib_var: "test p \<Longrightarrow> p \<cdot> (x + y) = p \<cdot> x + p \<cdot> y"
  using n_left_distrib by auto

lemma n_mult_left_iso: "x \<le> y \<Longrightarrow> n z \<cdot> x \<le> n z \<cdot> y"
  by (metis local.join.sup.absorb_iff1 local.n_left_distrib)

lemma test_mult_isol: "test p \<Longrightarrow> x \<le> y \<Longrightarrow> p \<cdot> x \<le> p \<cdot> y"
  using n_mult_left_iso by auto

lemma "test p \<Longrightarrow> x \<cdot> p \<le> x"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> q \<longleftrightarrow> p \<cdot> x \<le> x \<cdot> q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; p \<cdot> x \<cdot> !q = 0\<rbrakk> \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; x \<cdot> !q = !p \<cdot> x \<cdot> !q\<rbrakk> \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> q"
  (* nitpick *) oops

text \<open>Next, we study tests with commutativity conditions.\<close>

lemma comm_add: "test p \<Longrightarrow>  p \<cdot> x = x \<cdot> p \<Longrightarrow>  p \<cdot> y = y \<cdot> p \<Longrightarrow> p \<cdot> (x + y) = (x + y) \<cdot> p"
  by (simp add: n_left_distrib_var)

lemma comm_add_var: "test p \<Longrightarrow> test q \<Longrightarrow> test r \<Longrightarrow> p \<cdot> x = x \<cdot> p \<Longrightarrow> p \<cdot> y = y \<cdot> p \<Longrightarrow> p \<cdot> (q \<cdot> x + r \<cdot> y) = (q \<cdot> x + r \<cdot> y) \<cdot> p"
proof -
  assume a1: "test p"
  assume a2: "test q"
  assume a3: "p \<cdot> x = x \<cdot> p"
  assume a4: "test r"
  assume a5: "p \<cdot> y = y \<cdot> p"
  have f6: "p \<cdot> (q \<cdot> x) = q \<cdot> p \<cdot> x"
    using a2 a1 local.test_mult_comm_var mult_assoc by presburger
  have "p \<cdot> (r \<cdot> y) = r \<cdot> p \<cdot> y"
    using a4 a1 by (simp add: local.test_mult_comm_var mult_assoc)
  thus ?thesis
    using f6 a5 a3 a1 by (simp add: mult_assoc n_left_distrib_var)
qed

lemma test_distrib: "test p \<Longrightarrow> test q \<Longrightarrow> (p + q) \<cdot> (q \<cdot> y + !q \<cdot> x) = q \<cdot> y + !q \<cdot> p \<cdot> x"
proof -
  assume a: "test p" and b: "test q"
  hence "(p + q) \<cdot> (q \<cdot> y + !q \<cdot> x) = p \<cdot> q \<cdot> y + p \<cdot> !q \<cdot> x + q \<cdot> q \<cdot> y + q \<cdot> !q \<cdot> x"
    using local.add.assoc local.distrib_right' mult_assoc n_left_distrib_var by presburger
  also have "... = p \<cdot> q \<cdot> y + !q \<cdot> p \<cdot> x + q \<cdot> y"
   by (simp add: a b local.test_mult_comm_var) 
  also have "... = (p + 1) \<cdot> q \<cdot> y + !q \<cdot> p \<cdot> x"
    using add_commute local.add.assoc by force
  also have "... = q \<cdot> y + !q \<cdot> p \<cdot> x"
    by (simp add: a local.join.sup.absorb2 local.test_subid)
  finally show ?thesis
    by simp
qed

end

subsection \<open>Test Predioids\<close>

text \<open>
  The following class is relevant for probabilistic Kleene algebras.
\<close>

class test_pre_dioid_zerol = test_near_semiring_zerol_distrib + pre_dioid

begin

lemma n_restrictr: "x \<cdot> n y \<le> x"
  using local.mult_isol local.n_subid' by fastforce

lemma test_restrictr: "test p \<Longrightarrow> x \<cdot> p \<le> x"
  using n_restrictr by fastforce

lemma n_kat_2: "n x \<cdot> y = n x \<cdot> y \<cdot> n z \<longleftrightarrow> n x \<cdot> y \<le> y \<cdot> n z"
proof
  assume "n x \<cdot> y = n x \<cdot> y \<cdot> n z"
  thus "n x \<cdot> y \<le> y \<cdot> n z"
    by (metis mult.assoc n_restrictl)
next 
  assume "n x \<cdot> y \<le> y \<cdot> n z"
  hence "n x \<cdot> y  \<le> n x \<cdot> y \<cdot> n z"
    by (metis local.mult_isol local.n_mult_idem mult_assoc)
  thus "n x \<cdot> y  = n x \<cdot> y \<cdot> n z"
    by (simp add: local.order.antisym n_restrictr)
qed

lemma test_kat_2: "test p \<Longrightarrow> test q \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> q \<longleftrightarrow> p \<cdot> x \<le> x \<cdot> q"
  using n_kat_2 by auto

lemma n_kat_2_opp: "y \<cdot> n z = n x \<cdot> y \<cdot> n z \<longleftrightarrow> y \<cdot> n z \<le> n x \<cdot> y"
  by (metis local.n_kat_21_opp n_restrictr)

lemma test_kat_2_opp: "test p \<Longrightarrow> test q \<Longrightarrow> x \<cdot> q  = p \<cdot> x \<cdot> q \<longleftrightarrow> x \<cdot> q \<le> p \<cdot> x"
  by (metis local.test_kat_21_opp test_restrictr)

lemma "\<lbrakk>test p; test q; p\<cdot>x\<cdot>!q = 0\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; x\<cdot>!q = !p\<cdot>x\<cdot>!q\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> x \<cdot> (p + q) \<le> x \<cdot> p + x \<cdot> q"
  (* nitpick *) oops

end

text \<open>
  The following class is relevant for Demonic Refinement Algebras.
\<close>

class test_semiring_zerol = test_near_semiring_zerol + semiring_one_zerol

begin

subclass dioid_one_zerol ..

subclass test_pre_dioid_zerol
proof
show "\<And>x y z. !x \<cdot> (y + z) = !x \<cdot> y + !x \<cdot> z"
  by (simp add: local.distrib_left)
qed

lemma n_kat_31: "n x \<cdot> y \<cdot> t z = 0 \<Longrightarrow> n x \<cdot> y \<cdot> n z = n x \<cdot> y"
proof -
  assume a: "n x \<cdot> y \<cdot> t z = 0"
  have "n x \<cdot> y = n x \<cdot> y \<cdot> (n z + t z)"
    by simp
  also have "... = n x \<cdot> y \<cdot> n z + n x \<cdot> y \<cdot> t z"
    using local.distrib_left by blast
  finally show "n x \<cdot> y \<cdot> n z = n x \<cdot> y"
    using a  by auto
qed

lemma test_kat_31: "test p \<Longrightarrow> test q \<Longrightarrow> p \<cdot> x \<cdot> !q = 0 \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> q"
  by (metis local.test_double_comp_var n_kat_31)

lemma n_kat_var: "t x \<cdot> y \<cdot> t z = y \<cdot> t z \<Longrightarrow> n x \<cdot> y \<cdot> n z = n x \<cdot> y"
  using local.n_kat_1_var n_kat_31 by blast

lemma test1_var: "test p \<Longrightarrow> test q \<Longrightarrow> x \<cdot> !q = !p \<cdot> x \<cdot> !q \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> q"
  by (metis local.test_eq4 test_kat_31)

lemma "\<lbrakk>test p; test q; p\<cdot>x\<cdot>!q = 0\<rbrakk> \<Longrightarrow> !p\<cdot>x\<cdot>q = 0"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; p\<cdot>x = p\<cdot>x\<cdot>q\<rbrakk> \<Longrightarrow> x\<cdot>!q = !p\<cdot>x\<cdot>!q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; p\<cdot>x = p\<cdot>x\<cdot>q\<rbrakk> \<Longrightarrow> p\<cdot>x\<cdot>!q = 0"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; p\<cdot>x = p\<cdot>x\<cdot>q\<rbrakk> \<Longrightarrow> !p\<cdot>x\<cdot>q = 0"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; x\<cdot>!q = !p\<cdot>x\<cdot>!q\<rbrakk> \<Longrightarrow> !p\<cdot>x\<cdot>q = 0"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; !p\<cdot>x\<cdot>q = 0\<rbrakk> \<Longrightarrow> p\<cdot>x = p\<cdot>x\<cdot>q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; !p\<cdot>x\<cdot>q = 0\<rbrakk> \<Longrightarrow> x\<cdot>!q = !p\<cdot>x\<cdot>!q"
  (* nitpick *) oops

lemma "\<lbrakk>test p; test q; !p\<cdot>x\<cdot>q = 0\<rbrakk> \<Longrightarrow> p\<cdot>x\<cdot>!q = 0"
  (* nitpick *) oops

lemma "test p \<Longrightarrow> p \<cdot> x = p \<cdot> x \<cdot> p \<and> !p \<cdot> x = !p \<cdot> x \<cdot> !p \<Longrightarrow> p \<cdot> x = x \<cdot> p"
  (* nitpick *) oops

end

subsection \<open>Test Semirings\<close>

text \<open>
  The following class is relevant for Kleene Algebra with Tests.
\<close>

class test_semiring = test_semiring_zerol + semiring_one_zero

begin

lemma n_kat_1: "n x \<cdot> y \<cdot> t z = 0 \<longleftrightarrow> n x \<cdot> y \<cdot> n z = n x \<cdot> y"
  by (metis local.annir local.n_kat_31 local.test_mult_comp mult_assoc)

lemma test_kat_1': "test p \<Longrightarrow> test q \<Longrightarrow> p \<cdot> x \<cdot> !q = 0 \<longleftrightarrow> p \<cdot> x =  p \<cdot> x \<cdot> q"
  by (metis local.test_double_comp_var n_kat_1)

lemma n_kat_3: "n x \<cdot> y \<cdot> t z = 0 \<longleftrightarrow> n x \<cdot> y \<le> y \<cdot> n z"
  using local.n_kat_2 n_kat_1 by force

lemma test_kat_3: "test p \<Longrightarrow> test q \<Longrightarrow>  p \<cdot> x \<cdot> !q = 0 \<longleftrightarrow> p \<cdot> x \<le> x \<cdot> q"
  using n_kat_3 by auto

lemma n_kat_prop: "n x \<cdot> y \<cdot> n z = n x \<cdot> y \<longleftrightarrow> t x \<cdot> y \<cdot> t z = y \<cdot> t z"
  by (metis local.annir local.n_kat_1_opp local.n_kat_var local.t_n_closed local.test_mult_comp mult_assoc)

lemma test_kat_prop: "test p \<Longrightarrow> test q  \<Longrightarrow>  p \<cdot> x = p \<cdot> x \<cdot> q  \<longleftrightarrow> x \<cdot> !q = !p \<cdot> x \<cdot> !q"
  by (metis local.annir local.test1_var local.test_comp_mult2 local.test_eq4 mult_assoc)

lemma n_kat_3_opp: "t x \<cdot> y \<cdot> n z = 0 \<longleftrightarrow> y \<cdot> n z \<le> n x \<cdot> y"
  by (metis local.n_kat_1_var local.n_kat_2_opp local.t_n_closed)

lemma kat_1_var: "n x \<cdot> y \<cdot> n z = y \<cdot> n z \<longleftrightarrow> y \<cdot> n z \<le> n x \<cdot> y"
  using local.n_kat_2_opp by force
 
lemma "\<lbrakk>test p; test q\<rbrakk> \<Longrightarrow> (p\<cdot>x\<cdot>!q = 0) \<Longrightarrow> (!p\<cdot>x\<cdot>q = 0)"
  (* nitpick *) oops

lemma "n x \<cdot> y + t x \<cdot> z = n x \<cdot> y \<or> n x \<cdot> y + t x \<cdot> z = t x \<cdot> z"
(*nitpick*)
oops

end

end
