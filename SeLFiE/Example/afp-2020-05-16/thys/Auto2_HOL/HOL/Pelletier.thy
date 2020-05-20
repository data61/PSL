(*
  File: Pelletier.thy
  Author: Bohua Zhan

  Pelletier's problems. From the paper "Seventy-five problems for testing
  automatic theorem provers" by Francis Jeffry Pelletier.
*)

section \<open>Pelletier's problems\<close>

theory Pelletier
  imports Logic_Thms
begin

theorem p1: "(p \<longrightarrow> q) \<longleftrightarrow> (\<not>q \<longrightarrow> \<not>p)" by auto2

theorem p2: "(\<not>\<not>p) \<longleftrightarrow> p" by auto2

theorem p3: "\<not>(p \<longrightarrow> q) \<Longrightarrow> q \<longrightarrow> p" by auto2

theorem p4: "(\<not>p \<longrightarrow> q) \<longleftrightarrow> (\<not>q \<longrightarrow> p)" by auto2

theorem p5: "(p \<or> q) \<longrightarrow> (p \<or> r) \<Longrightarrow> p \<or> (q \<longrightarrow> r)" by auto2

theorem p6: "p \<or> \<not>p" by auto2

theorem p7: "p \<or> \<not>\<not>\<not>p" by auto2

theorem p8: "((p \<longrightarrow> q) \<longrightarrow> p) \<Longrightarrow> p" by auto2

theorem p9: "(p \<or> q) \<and> (\<not>p \<or> q) \<and> (p \<or> \<not>q) \<Longrightarrow> \<not>(\<not>p \<or> \<not>q)" by auto2

theorem p10: "q \<longrightarrow> r \<Longrightarrow> r \<longrightarrow> p \<and> q \<Longrightarrow> p \<longrightarrow> q \<or> r \<Longrightarrow> p \<longleftrightarrow> q" by auto2

theorem p11: "p \<longleftrightarrow> p" by auto2

theorem p12: "((p \<longleftrightarrow> q) \<longleftrightarrow> r) \<longleftrightarrow> (p \<longleftrightarrow> (q \<longleftrightarrow> r))"
@proof
  @case "p"
  @case "q"
@qed

theorem p13: "p \<or> (q \<and> r) \<longleftrightarrow> (p \<or> q) \<and> (p \<or> r)" by auto2

theorem p14: "(p \<longleftrightarrow> q) \<longleftrightarrow> ((q \<or> \<not>p) \<and> (\<not>q \<or> p))" by auto2

theorem p15: "(p \<longrightarrow> q) \<longleftrightarrow> (\<not>p \<or> q)" by auto2

theorem p16: "(p \<longrightarrow> q) \<or> (q \<longrightarrow> p)" by auto2

theorem p17: "(p \<and> (q \<longrightarrow> r) \<longrightarrow> s) \<longleftrightarrow> (\<not>p \<or> q \<or> s) \<and> (\<not>p \<or> \<not>r \<or> s)" by auto2

theorem p18: "\<exists>y::'a. \<forall>x. F(y) \<longrightarrow> F(x)"
@proof
  @case "\<forall>x. F(x)" @with
    @obtain "y::'a" where "y = y" @have "\<forall>x. F(y) \<longrightarrow> F(x)"
  @end
  @obtain y where "\<not>F(y)" @have "\<forall>x. F(y) \<longrightarrow> F(x)"
@qed

theorem p19: "\<exists>x::'a. \<forall>y z. (P(y) \<longrightarrow> Q(z)) \<longrightarrow> (P(x) \<longrightarrow> Q(x))"
@proof
  @case "\<exists>x. P(x) \<longrightarrow> Q(x)" @with
    @obtain x where "P(x) \<longrightarrow> Q(x)"
    @have "\<forall>y z. (P(y) \<longrightarrow> Q(z)) \<longrightarrow> (P(x) \<longrightarrow> Q(x))"
  @end
  @obtain "x::'a" where "x = x"
  @have "\<forall>y z. (P(y) \<longrightarrow> Q(z)) \<longrightarrow> (P(x) \<longrightarrow> Q(x))"
@qed

theorem p20: "\<forall>x y. \<exists>z. \<forall>w. P(x) \<and> Q(y) \<longrightarrow> R(z) \<and> S(w) \<Longrightarrow>
  \<exists>x y. P(x) \<and> Q(y) \<Longrightarrow> \<exists>z. R(z)"
@proof
  @obtain x y where "P(x)" "Q(y)"
  @obtain z where "\<forall>w. P(x) \<and> Q(y) \<longrightarrow> R(z) \<and> S(w)"
@qed

theorem p21: "\<exists>x. p \<longrightarrow> F(x) \<Longrightarrow> \<exists>x. F(x) \<longrightarrow> p \<Longrightarrow> \<exists>x. p \<longleftrightarrow> F(x)"
@proof
  @case "p" @with @obtain x where "F(x)" @have "p \<longleftrightarrow> F(x)" @end
  @case "\<not>p" @with @obtain x where "\<not>F(x)" @have "p \<longleftrightarrow> F(x)" @end
@qed

theorem p22: "\<forall>x::'a. p \<longleftrightarrow> F(x) \<Longrightarrow> p \<longleftrightarrow> (\<forall>x. F(x))"
@proof
  @case "p" @obtain "x::'a" where "x = x"
@qed

theorem p23: "(\<forall>x::'a. p \<or> F(x)) \<longleftrightarrow> (p \<or> (\<forall>x. F(x)))" by auto2

theorem p29: "\<exists>x. F(x) \<Longrightarrow> \<exists>x. G(x) \<Longrightarrow>
  ((\<forall>x. F(x) \<longrightarrow> H(x)) \<and> (\<forall>x. G(x) \<longrightarrow> J(x))) \<longleftrightarrow>
  (\<forall>x y. F(x) \<and> G(y) \<longrightarrow> H(x) \<and> J(y))"
@proof
  @obtain a b where "F(a)" "G(b)"
  @case "\<forall>x y. F(x) \<and> G(y) \<longrightarrow> H(x) \<and> J(y)" @with
    @have "\<forall>x. F(x) \<longrightarrow> H(x)" @with @have "F(x) \<and> G(b)" @end
    @have "\<forall>y. G(y) \<longrightarrow> J(y)" @with @have "F(a) \<and> G(y)" @end
  @end
@qed

theorem p30: "\<forall>x. F(x) \<or> G(x) \<longrightarrow> \<not>H(x) \<Longrightarrow>
  \<forall>x. (G(x) \<longrightarrow> \<not>I(x)) \<longrightarrow> F(x) \<and> H(x) \<Longrightarrow> \<forall>x. I(x)"
@proof
  @have "\<forall>x. I(x)" @with @case "F(x)" @end
@qed

theorem p31: "\<not>(\<exists>x. F(x) \<and> (G(x) \<or> H(x))) \<Longrightarrow> \<exists>x. I(x) \<and> F(x) \<Longrightarrow> \<forall>x. \<not>H(x) \<longrightarrow> J(x) \<Longrightarrow>
  \<exists>x. I(x) \<and> J(x)" by auto2

theorem p32: "\<forall>x. (F(x) \<and> (G(x) \<or> H(x))) \<longrightarrow> I(x) \<Longrightarrow> \<forall>x. I(x) \<and> H(x) \<longrightarrow> J(x) \<Longrightarrow>
  \<forall>x. K(x) \<longrightarrow> H(x) \<Longrightarrow> \<forall>x. F(x) \<and> K(x) \<longrightarrow> J(x)" by auto2

theorem p33: "(\<forall>x. p(a) \<and> (p(x) \<longrightarrow> p(b)) \<longrightarrow> p(c)) \<longleftrightarrow>
  (\<forall>x. (\<not>p(a) \<or> p(x) \<or> p(c)) \<and> (\<not>p(a) \<or> \<not>p(b) \<or> p(c)))" by auto2

theorem p35: "\<exists>(x::'a) (y::'b). P(x,y) \<longrightarrow> (\<forall>x y. P(x,y))" by auto2

theorem p39: "\<not>(\<exists>x. \<forall>y. F(y,x) \<longleftrightarrow> \<not>F(y,y))"
@proof
  @contradiction
  @obtain x where "\<forall>y. F(y,x) \<longleftrightarrow> \<not>F(y,y)"
  @case "F(x,x)"
@qed

(* Note there is a typo in the original text. *)
theorem p40: "\<exists>y. \<forall>x. F(x,y) \<longleftrightarrow> F(x,x) \<Longrightarrow> \<not>(\<forall>x. \<exists>y. \<forall>z. F(z,y) \<longleftrightarrow> \<not>F(z,x))"
@proof
  @obtain A where "\<forall>x. F(x,A) \<longleftrightarrow> F(x,x)"
  @have "\<not>(\<exists>y. \<forall>z. F(z,y) \<longleftrightarrow> \<not>F(z,A))" @with
    @have (@rule) "\<forall>y. \<not>(\<forall>z. F(z,y) \<longleftrightarrow> \<not>F(z,A))" @with
      @have "\<not>(F(y,y) \<longleftrightarrow> \<not>F(y,A))" @with @case "F(y,y)" @end
    @end
  @end
@qed

theorem p42: "\<not>(\<exists>y. \<forall>x. F(x,y) \<longleftrightarrow> \<not>(\<exists>z. F(x,z) \<and> F(z,x)))"
@proof
  @contradiction
  @obtain y where "\<forall>x. F(x,y) \<longleftrightarrow> \<not>(\<exists>z. F(x,z) \<and> F(z,x))"
  @case "F(y,y)"
@qed

theorem p43: "\<forall>x y. Q(x,y) \<longleftrightarrow> (\<forall>z. F(z,x) \<longleftrightarrow> F(z,y)) \<Longrightarrow>
  \<forall>x y. Q(x,y) \<longleftrightarrow> Q(y,x)" by auto2

theorem p47:
  "(\<forall>x. P1(x) \<longrightarrow> P0(x)) \<and> (\<exists>x. P1(x)) \<Longrightarrow>
   (\<forall>x. P2(x) \<longrightarrow> P0(x)) \<and> (\<exists>x. P2(x)) \<Longrightarrow>
   (\<forall>x. P3(x) \<longrightarrow> P0(x)) \<and> (\<exists>x. P3(x)) \<Longrightarrow>
   (\<forall>x. P4(x) \<longrightarrow> P0(x)) \<and> (\<exists>x. P4(x)) \<Longrightarrow>
   (\<forall>x. P5(x) \<longrightarrow> P0(x)) \<and> (\<exists>x. P5(x)) \<Longrightarrow>
   (\<exists>x. Q1(x)) \<and> (\<forall>x. Q1(x) \<longrightarrow> Q0(x)) \<Longrightarrow>
   \<forall>x. P0(x) \<longrightarrow> ((\<forall>y. Q0(y) \<longrightarrow> R(x,y)) \<or>
                   (\<forall>y. P0(y) \<and> S(y,x) \<and> (\<exists>z. Q0(z) \<and> R(y,z)) \<longrightarrow> R(x,y))) \<Longrightarrow>
   \<forall>x y. P3(y) \<and> (P5(x) \<or> P4(x)) \<longrightarrow> S(x,y) \<Longrightarrow>
   \<forall>x y. P3(x) \<and> P2(y) \<longrightarrow> S(x,y) \<Longrightarrow>
   \<forall>x y. P2(x) \<and> P1(y) \<longrightarrow> S(x,y) \<Longrightarrow>
   \<forall>x y. P1(x) \<and> (P2(y) \<or> Q1(y)) \<longrightarrow> \<not>R(x,y) \<Longrightarrow>
   \<forall>x y. P3(x) \<and> P4(y) \<longrightarrow> R(x,y) \<Longrightarrow>
   \<forall>x y. P3(x) \<and> P5(y) \<longrightarrow> \<not>R(x,y) \<Longrightarrow>
   \<forall>x. P4(x) \<or> P5(x) \<longrightarrow> (\<exists>y. Q0(y) \<and> R(x,y)) \<Longrightarrow>
   \<exists>x y. P0(x) \<and> P0(y) \<and> (\<exists>z. Q1(z) \<and> R(y,z) \<and> R(x,y))"
@proof
  @obtain x1 x2 x3 x4 x5 where "P1(x1)" "P2(x2)" "P3(x3)" "P4(x4)" "P5(x5)"
  @have "S(x3,x2)" @have "S(x2,x1)" @have "R(x3,x4)" @have "\<not>R(x3,x5)"
@qed

theorem p48: "a = b \<or> c = d \<Longrightarrow> a = c \<or> b = d \<Longrightarrow> a = d \<or> b = c" by auto2

theorem p49: "\<exists>x y. \<forall>(z::'a). z = x \<or> z = y \<Longrightarrow> P(a) \<and> P(b) \<Longrightarrow> (a::'a) \<noteq> b \<Longrightarrow> \<forall>x. P(x)"
@proof
  @obtain x y where "\<forall>(z::'a). z = x \<or> z = y"
  @have "x = a \<or> x = b"
  @have "\<forall>c. P(c)" @with @have "c = a \<or> c = b" @end
@qed

theorem p50: "\<forall>x. F(a,x) \<or> (\<forall>y. F(x,y)) \<Longrightarrow> \<exists>x. \<forall>y. F(x,y)"
@proof
  @case "\<forall>y. F(a,y)"
  @obtain y where "\<not>F(a,y)"
  @have (@rule) "\<forall>z. F(a,y) \<or> F(y,z)"
@qed

theorem p51: "\<exists>z w. \<forall>x y. F(x,y) \<longleftrightarrow> x = z \<and> y = w \<Longrightarrow>
  \<exists>z. \<forall>x. (\<exists>w. \<forall>y. F(x,y) \<longleftrightarrow> y = w) \<longleftrightarrow> x = z"
@proof
  @obtain z w where "\<forall>x y. F(x,y) \<longleftrightarrow> x = z \<and> y = w"
  @have "\<forall>x. (\<exists>w. \<forall>y. F(x,y) \<longleftrightarrow> y = w) \<longleftrightarrow> x = z" @with
    @case "x = z" @with @have "\<forall>y. F(x,y) \<longleftrightarrow> y = w" @end
  @end
@qed

theorem p52: "\<exists>z w. \<forall>x y. F(x,y) \<longleftrightarrow> x = z \<and> y = w \<Longrightarrow>
  \<exists>w. \<forall>y. (\<exists>z. \<forall>x. F(x,y) \<longleftrightarrow> x = z) \<longleftrightarrow> y = w"
@proof
  @obtain z w where "\<forall>x y. F(x,y) \<longleftrightarrow> x = z \<and> y = w"
  @have"\<forall>y. (\<exists>z. \<forall>x. F(x,y) \<longleftrightarrow> x = z) \<longleftrightarrow> y = w" @with
    @case "y = w" @with @have "\<forall>x. F(x,y) \<longleftrightarrow> x = z" @end
  @end
@qed

theorem p55:
  "\<exists>x. L(x) \<and> K(x,a) \<Longrightarrow>
   L(a) \<and> L(b) \<and> L(c) \<Longrightarrow>
   \<forall>x. L(x) \<longrightarrow> x = a \<or> x = b \<or> x = c \<Longrightarrow>
   \<forall>y x. K(x,y) \<longrightarrow> H(x,y) \<Longrightarrow>
   \<forall>x y. K(x,y) \<longrightarrow> \<not>R(x,y) \<Longrightarrow>
   \<forall>x. H(a,x) \<longrightarrow> \<not>H(c,x) \<Longrightarrow>
   \<forall>x. x \<noteq> b \<longrightarrow> H(a,x) \<Longrightarrow>
   \<forall>x. \<not>R(x,a) \<longrightarrow> H(b,x) \<Longrightarrow>
   \<forall>x. H(a,x) \<longrightarrow> H(b,x) \<Longrightarrow>  \<comment>\<open>typo in text\<close>
   \<forall>x. \<exists>y. \<not>H(x,y) \<Longrightarrow>
   a \<noteq> b \<Longrightarrow>
   K(a,a)"
@proof
  @case "K(b,a)" @with @have "\<forall>x. H(b,x)" @end
@qed

theorem p56: "(\<forall>x. (\<exists>y. F(y) \<and> x = f(y)) \<longrightarrow> F(x)) \<longleftrightarrow> (\<forall>x. F(x) \<longrightarrow> F(f(x)))" by auto2

theorem p57: "F(f(a,b),f(b,c)) \<Longrightarrow> F(f(b,c),f(a,c)) \<Longrightarrow>
  \<forall>x y z. F(x,y) \<and> F(y,z) \<longrightarrow> F(x,z) \<Longrightarrow> F(f(a,b),f(a,c))" by auto2

theorem p58: "\<forall>x y. f(x) = g(y) \<Longrightarrow> \<forall>x y. f(f(x)) = f(g(y))"
@proof
  @have "\<forall>x y. f(f(x)) = f(g(y))" @with
    @have "f(x) = g(y)"
  @end
@qed

theorem p59: "\<forall>x::'a. F(x) \<longleftrightarrow> \<not>F(f(x)) \<Longrightarrow> \<exists>x. F(x) \<and> \<not>F(f(x))"
@proof
  @obtain "x::'a" where "x = x" @case "F(x)"
@qed

theorem p60: "\<forall>x. F(x,f(x)) \<longleftrightarrow> (\<exists>y. (\<forall>z. F(z,y) \<longrightarrow> F(z,f(x))) \<and> F(x,y))" by auto2

theorem p61: "\<forall>x y z. f(x,f(y,z)) = f(f(x,y),z) \<Longrightarrow> \<forall>x y z w. f(x,f(y,f(z,w))) = f(f(f(x,y),z),w)"
  by auto2

end
