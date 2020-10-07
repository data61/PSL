(*  Based on:   HOL/Hoare/Examples.thy
*)
theory Labeled_Hoare_Examples
imports
  Labeled_Hoare
  "HOL-Hoare.Arith2"
begin


subsubsection \<open>Multiplication by successive addition\<close>

lemma multiply_by_add: "VARS m s a b
  {a=A \<and> b=B}
  m := 0; s := 0;
  WHILE m\<noteq>a
  INV {s=m*b \<and> a=A \<and> b=B}
  DO s := s+b; m := m+(1::nat) OD
  {s = A*B}"
by vcg_simp

lemma "VARS M N P :: int
 {m=M \<and> n=N}
 IF M < 0 THEN M := -M; N := -N ELSE SKIP FI;
 P := 0;
 WHILE 0 < M
 INV {0 \<le> M \<and> (\<exists>p. p = (if m<0 then -m else m) \<and> p*N = m*n \<and> P = (p-M)*N)}
 DO P := P+N; M := M - 1 OD
 {P = m*n}"
proof casified_vcg_simp
  case while
  { case postcondition
    then show ?case by auto
  next
    case invariant
    { case basic
      then show ?case by (auto simp: int_distrib)
    }
  }
qed


subsubsection \<open>Euclid's algorithm for GCD\<close>

lemma Euclid_GCD: "VARS a b
 {0<A \<and> 0<B}
 a := A; b := B;
 WHILE  a \<noteq> b
 INV {0<a \<and> 0<b \<and> gcd A B = gcd a b}
 DO IF a<b THEN b := b-a ELSE a := a-b FI OD
 {a = gcd A B}"
proof casified_vcg_simp
  case while
  { case postcondition
    then show ?case by (auto elim: gcd_nnn)
  next
    case invariant
    { case cond
      { case vc
        then show ?case
          by (simp_all add: linorder_not_less gcd_diff_l gcd_diff_r less_imp_le)
      }
    }
  }
qed


subsubsection \<open>Dijkstra's extension of Euclid's algorithm for simultaneous GCD and SCM\<close>

text\<open>
  From E.W. Disjkstra. Selected Writings on Computing, p 98 (EWD474),
  where it is given without the invariant. Instead of defining scm
  explicitly we have used the theorem scm x y = x*y/gcd x y and avoided
  division by mupltiplying with gcd x y.
\<close>

lemmas distribs =
  diff_mult_distrib diff_mult_distrib2 add_mult_distrib add_mult_distrib2

lemma gcd_scm: "VARS a b x y
 {0<A \<and> 0<B \<and> a=A \<and> b=B \<and> x=B \<and> y=A}
 WHILE  a \<noteq> b
 INV {0<a \<and> 0<b \<and> gcd A B = gcd a b \<and> 2*A*B = a*x + b*y}
 DO IF a<b THEN (b := b-a; x := x+y) ELSE (a := a-b; y := y+x) FI OD
 {a = gcd A B \<and> 2*A*B = a*(x+y)}"
proof casified_vcg
  case while {
    case precondition then show ?case by simp
  next
    case invariant
    case cond
    case vc
    then show ?case
      by (simp add: distribs gcd_diff_r linorder_not_less gcd_diff_l)
  next
    case postcondition then show ?case
      by (simp add: distribs gcd_nnn)
  }
qed


subsubsection \<open>Power by iterated squaring and multiplication\<close>

lemma power_by_mult: "VARS a b c
 {a=A \<and> b=B}
 c := (1::nat);
 WHILE b \<noteq> 0
 INV {A^B = c * a^b}
 DO  WHILE b mod 2 = 0
     INV {A^B = c * a^b}
     DO  a := a*a; b := b div 2 OD;
     c := c*a; b := b - 1
 OD
 {c = A^B}"
proof casified_vcg_simp
  case while
  case invariant
  case while
  case postcondition
  then show ?case by (cases b) simp_all
qed


subsubsection \<open>Factorial\<close>

lemma factorial: "VARS a b
 {a=A}
 b := 1;
 WHILE a \<noteq> 0
 INV {fac A = b * fac a}
 DO b := b*a; a := a - 1 OD
 {b = fac A}"
  apply vcg_simp
  apply(clarsimp split: nat_diff_split)
  done

lemma "VARS i f
 {True}
 i := (1::nat); f := 1;
 WHILE i \<le> n INV {f = fac(i - 1) \<and> 1 \<le> i \<and> i \<le> n+1}
 DO f := f*i; i := i+1 OD
 {f = fac n}"
proof casified_vcg_simp
  case while
  { case invariant
    { case basic
      then show ?case by (induct i) simp_all
    }
  next
    case postcondition
    then have "i = Suc n" by simp
    then show ?case by simp
  }
qed


subsubsection \<open>Quicksort\<close>

text \<open>
  The `partition' procedure for quicksort.
  `A' is the array to be sorted (modelled as a list).
  Elements of A must be of class order to infer at the end
  that the elements between u and l are equal to pivot.

  Ambiguity warnings of parser are due to := being used
  both for assignment and list update.
\<close>

lemma Partition:
  fixes pivot
  defines "leq \<equiv> \<lambda>A i. \<forall>k. k<i \<longrightarrow> A!k \<le> pivot"
  defines "geq \<equiv> \<lambda>A i. \<forall>k. i<k \<and> k<length A \<longrightarrow> pivot \<le> A!k"
  shows "
   VARS A u l
   {0 < length(A::('a::order)list)}
   l := 0; u := length A - Suc 0;
   WHILE l \<le> u
    INV {leq A l \<and> geq A u \<and> u<length A \<and> l\<le>length A}
    DO WHILE l < length A \<and> A!l \<le> pivot
        INV {leq A l \<and> geq A u \<and> u<length A \<and> l\<le>length A}
        DO l := l+1 OD;
       WHILE 0 < u \<and> pivot \<le> A!u
        INV {leq A l \<and> geq A u  \<and> u<length A \<and> l\<le>length A}
        DO u := u - 1 OD;
       IF l \<le> u THEN A := A[l := A!u, u := A!l] ELSE SKIP FI
    OD
   {leq A u \<and> (\<forall>k. u<k \<and> k<l \<longrightarrow> A!k = pivot) \<and> geq A l}"
  unfolding leq_def geq_def
proof casified_vcg_simp
  case basic
  then show ?case by auto
next
  case while
  { case postcondition
    then show ?case by (force simp: nth_list_update)
  next
    case invariant
    { case while
      { case invariant
        { case basic
          then show ?case by (blast elim!: less_SucE intro: Suc_leI)
        }
      }
    next
      case whilea
      { case invariant
        { case basic
          have lem: "\<And>m n. m - Suc 0 < n \<Longrightarrow> m < Suc n" by linarith
          from basic show ?case by (blast elim!: less_SucE intro: less_imp_diff_less dest: lem)
        }
      }
    }
  }
qed



end
