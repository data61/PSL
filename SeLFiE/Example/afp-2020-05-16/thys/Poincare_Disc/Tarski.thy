section\<open>Tarski axioms\<close>

text \<open>In this section we introduce axioms of Tarski \cite{tarski} trough a series of locales.\<close>

theory Tarski
imports Main
begin

text \<open>The first locale assumes all Tarski axioms except for the Euclid's axiom and the continuity
axiom and corresponds to absolute geometry.\<close>

locale TarskiAbsolute =
  fixes cong :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  fixes betw :: "'p \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> bool"
  assumes cong_reflexive:  "cong x y y x"
  assumes cong_transitive: "cong x y z u \<and> cong x y v w \<longrightarrow> cong z u v w"
  assumes cong_identity:   "cong x y z z \<longrightarrow> x = y"
  assumes segment_construction: "\<exists> z. betw x y z \<and> cong y z a b"
  assumes five_segment:    "x \<noteq> y \<and> betw x y z \<and> betw x' y' z' \<and> cong x y x' y' \<and> cong y z y' z' \<and> cong x u x' u' \<and> cong y u y' u' \<longrightarrow> cong z u z' u'"
  assumes betw_identity:   "betw x y x \<longrightarrow> x = y"
  assumes Pasch:           "betw x u z \<and> betw y v z \<longrightarrow> (\<exists> a. betw u a y \<and> betw x a v)"
  assumes lower_dimension: "\<exists> a. \<exists> b. \<exists> c. \<not> betw a b c \<and> \<not> betw b c a \<and> \<not> betw c a b"
  assumes upper_dimension: "cong x u x v \<and> cong y u y v \<and> cong z u z v \<and> u \<noteq> v \<longrightarrow> betw x y z \<or> betw y z x \<or> betw z x y"
begin

text \<open>The following definitions are used to specify axioms in the following locales.\<close>

text \<open>Point $p$ is on line $ab$.\<close>
definition on_line where
  "on_line p a b \<longleftrightarrow> betw p a b \<or> betw a p b \<or> betw a b p"

text \<open>Point $p$ is on ray $ab$.\<close>
definition on_ray where 
  "on_ray p a b \<longleftrightarrow> betw a p b \<or> betw a b p"

text \<open>Point $p$ is inside angle $abc$.\<close>
definition in_angle where
  "in_angle p a b c \<longleftrightarrow> b \<noteq> a \<and> b \<noteq> c \<and> p \<noteq> b \<and> (\<exists> x. betw a x c \<and> x \<noteq> a \<and> x \<noteq> c \<and> on_ray p b x)"

text \<open>Ray $r_ar_b$ meets the line $l_al_b$.\<close>
definition ray_meets_line where
  "ray_meets_line ra rb la lb \<longleftrightarrow> (\<exists> x. on_ray x ra rb \<and> on_line x la lb)"

end

text\<open>The second locales adds the negation of Euclid's axiom and limiting parallels and corresponds
to hyperbolic geometry.\<close>

locale TarskiHyperbolic = TarskiAbsolute + 
  assumes euclid_negation: "\<exists> a b c d t. betw a d t \<and> betw b d c \<and> a \<noteq> d \<and> (\<forall> x y. betw a b x \<and> betw a c y \<longrightarrow> \<not> betw x t y)"
  assumes limiting_parallels: "\<not> on_line a x1 x2 \<Longrightarrow> 
      (\<exists> a1 a2. \<not> on_line a a1 a2 \<and>
                \<not> ray_meets_line a a1 x1 x2 \<and>
                \<not> ray_meets_line a a2 x1 x2 \<and>
                (\<forall> a'. in_angle a' a1 a a2 \<longrightarrow> ray_meets_line a a' x1 x2))"

text\<open>The third locale adds the continuity axiom and corresponds to elementary hyperbolic geometry.\<close>
locale ElementaryTarskiHyperbolic = TarskiHyperbolic +
  assumes continuity: "\<lbrakk>\<exists> a. \<forall> x. \<forall> y. \<phi> x \<and> \<psi> y \<longrightarrow> betw a x y\<rbrakk> \<Longrightarrow> \<exists> b. \<forall> x. \<forall> y. \<phi> x \<and> \<psi> y \<longrightarrow> betw x b y"

end
