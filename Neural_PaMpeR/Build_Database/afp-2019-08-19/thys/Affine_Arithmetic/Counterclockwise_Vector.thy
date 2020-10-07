section \<open>CCW Vector Space\<close>
theory Counterclockwise_Vector
imports Counterclockwise
begin

locale ccw_vector_space = ccw_system12 ccw S for ccw::"'a::real_vector \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" and S +
  assumes translate_plus[simp]: "ccw (a + x) (b + x) (c + x) \<longleftrightarrow> ccw a b c"
  assumes scaleR1_eq[simp]: "0 < e \<Longrightarrow> ccw 0 (e*\<^sub>Ra) b = ccw 0 a b"
  assumes uminus1[simp]: "ccw 0 (-a) b = ccw 0 b a"
  assumes add1: "ccw 0 a b \<Longrightarrow> ccw 0 c b \<Longrightarrow> ccw 0 (a + c) b"
begin

lemma translate_plus'[simp]:
  "ccw (x + a) (x + b) (x + c) \<longleftrightarrow> ccw a b c"
  by (auto simp: ac_simps)

lemma uminus2[simp]: "ccw 0 a (- b) = ccw 0 b a"
  by (metis minus_minus uminus1)

lemma uminus_all[simp]: "ccw (-a) (-b) (-c) \<longleftrightarrow> ccw a b c"
proof -
  have "ccw (-a) (-b) (-c) \<longleftrightarrow> ccw 0 (- (b - a)) (- (c - a))"
    using translate_plus[of "-a" a "-b" "-c"]
    by simp
  also have "\<dots> \<longleftrightarrow> ccw 0 (b - a) (c - a)"
    by (simp del: minus_diff_eq)
  also have "\<dots> \<longleftrightarrow> ccw a b c"
    using translate_plus[of a "-a" b c]
    by simp
  finally show ?thesis .
qed

lemma translate_origin: "NO_MATCH 0 p \<Longrightarrow> ccw p q r \<longleftrightarrow> ccw 0 (q - p) (r - p)"
  using translate_plus[of p "- p" q r]
  by simp

lemma translate[simp]: "ccw a (a + b) (a + c) \<longleftrightarrow> ccw 0 b c"
  by (simp add: translate_origin)

lemma translate_plus3: "ccw (a - x) (b - x) c \<longleftrightarrow> ccw a b (c + x)"
  using translate_plus[of a "-x" b "c + x"] by simp

lemma renormalize:
  "ccw 0 (a - b) (c - a) \<Longrightarrow> ccw b a c"
  by (metis diff_add_cancel diff_self cyclic minus_diff_eq translate_plus3 uminus1)

lemma cyclicI: "ccw p q r \<Longrightarrow> ccw q r p"
  by (metis cyclic)

lemma
  scaleR2_eq[simp]:
  "0 < e \<Longrightarrow> ccw 0 xr (e *\<^sub>R P) \<longleftrightarrow> ccw 0 xr P"
  using scaleR1_eq[of e "-P" xr]
  by simp

lemma scaleR1_nonzero_eq:
  "e \<noteq> 0 \<Longrightarrow> ccw 0 (e *\<^sub>R a) b = (if e > 0 then ccw 0 a b else ccw 0 b a)"
proof cases
  assume "e < 0"
  define e' where "e' = - e"
  hence "e = -e'" "e' > 0" using \<open>e < 0\<close> by simp_all
  thus ?thesis by simp
qed simp

lemma neg_scaleR[simp]: "x < 0 \<Longrightarrow> ccw 0 (x *\<^sub>R b) c \<longleftrightarrow> ccw 0 c b"
  using scaleR1_nonzero_eq by auto

lemma
  scaleR1:
  "0 < e \<Longrightarrow> ccw 0 xr P \<Longrightarrow> ccw 0 (e *\<^sub>R xr) P"
  by simp

lemma
  add3: "ccw 0 a b \<and> ccw 0 a c \<Longrightarrow> ccw 0 a (b + c)"
  using add1[of "-b" a "-c"] uminus1[of "b + c" a]
  by simp

lemma add3_self[simp]: "ccw 0 p (p + q) \<longleftrightarrow> ccw 0 p q"
  using translate[of "-p" p "p + q"]
  apply (simp add: cyclic)
  apply (metis cyclic uminus2)
  done

lemma add2_self[simp]: "ccw 0 (p + q) p \<longleftrightarrow> ccw 0 q p"
  using translate[of "-p" "p + q" p]
  apply simp
  apply (metis cyclic uminus1)
  done

lemma scale_add3[simp]: "ccw 0 a (x *\<^sub>R a + b) \<longleftrightarrow> ccw 0 a b"
proof -
  {
    assume "x = 0"
    hence ?thesis by simp
  } moreover {
    assume "x > 0"
    hence ?thesis using add3_self scaleR1_eq by blast
  } moreover {
    assume "x < 0"
    define x' where "x' = - x"
    hence "x = -x'" "x' > 0" using \<open>x < 0\<close> by simp_all
    hence "ccw 0 a (x *\<^sub>R a + b) = ccw 0 (x' *\<^sub>R a + - b) (x' *\<^sub>R a)"
      by (subst uminus1[symmetric]) simp
    also have "\<dots> = ccw 0 (- b) a"
      unfolding add2_self by (simp add: \<open>x' > 0\<close>)
    also have "\<dots> = ccw 0 a b"
      by simp
    finally have ?thesis .
  } ultimately show ?thesis by arith
qed

lemma scale_add3'[simp]: "ccw 0 a (b + x *\<^sub>R a) \<longleftrightarrow> ccw 0 a b"
  and scale_minus3[simp]: "ccw 0 a (x *\<^sub>R a - b) \<longleftrightarrow> ccw 0 b a"
  and scale_minus3'[simp]: "ccw 0 a (b - x *\<^sub>R a) \<longleftrightarrow> ccw 0 a b"
  using
    scale_add3[of a x b]
    scale_add3[of a "-x" b]
    scale_add3[of a x "-b"]
  by (simp_all add: ac_simps)

lemma sum:
  assumes fin: "finite X"
  assumes ne: "X\<noteq>{}"
  assumes ncoll: "(\<And>x. x \<in> X \<Longrightarrow> ccw 0 a (f x))"
  shows "ccw 0 a (sum f X)"
proof -
  from ne obtain x where "x \<in> X" "insert x X = X" by auto
  have "ccw 0 a (sum f (insert x X))"
    using fin ncoll
  proof (induction X)
    case empty thus ?case using \<open>x \<in> X\<close> ncoll
      by auto
  next
    case (insert y F)
    hence "ccw 0 a (sum f (insert y (insert x F)))"
      by (cases "y = x") (auto intro!: add3)
    thus ?case
      by (simp add: insert_commute)
  qed
  thus ?thesis using \<open>insert x X = X\<close> by simp
qed

lemma sum2:
  assumes fin: "finite X"
  assumes ne: "X\<noteq>{}"
  assumes ncoll: "(\<And>x. x \<in> X \<Longrightarrow> ccw 0 (f x) a)"
  shows "ccw 0 (sum f X) a"
  using sum[OF assms(1,2), of "-a" f] ncoll
  by simp

lemma translate_minus[simp]:
  "ccw (x - a) (x - b) (x - c) = ccw (-a) (-b) (-c)"
  using translate_plus[of "-a" x "-b" "-c"]
  by simp

end

locale ccw_convex = ccw_system ccw S for ccw and S::"'a::real_vector set" +
  fixes oriented
  assumes convex2:
    "u \<ge> 0 \<Longrightarrow> v \<ge> 0 \<Longrightarrow> u + v = 1 \<Longrightarrow> ccw a b c \<Longrightarrow> ccw a b d \<Longrightarrow> oriented a b \<Longrightarrow>
      ccw a b (u *\<^sub>R c + v *\<^sub>R d)"
begin

lemma convex_hull:
  assumes [intro, simp]: "finite C"
  assumes ccw: "\<And>c. c \<in> C \<Longrightarrow> ccw a b c"
  assumes ch: "x \<in> convex hull C"
  assumes oriented: "oriented a b"
  shows "ccw a b x"
proof -
  define D where "D = C"
  have D: "C \<subseteq> D" "\<And>c. c \<in> D \<Longrightarrow> ccw a b c" by (simp_all add: D_def ccw)
  show "ccw a b x"
    using \<open>finite C\<close> D ch
  proof (induct arbitrary: x)
    case empty thus ?case by simp
  next
    case (insert c C)
    hence "C \<subseteq> D" by simp
    {
      assume "C = {}"
      hence ?case
        using insert
        by simp
    } moreover {
      assume "C \<noteq> {}"
      from convex_hull_insert[OF this, of c] insert(6)
      obtain u v d where "u \<ge> 0" "v \<ge> 0" "d \<in> convex hull C" "u + v = 1"
        and x: "x = u *\<^sub>R c + v *\<^sub>R d"
        by blast
      have "ccw a b d"
        by (auto intro: insert.hyps(3)[OF \<open>C \<subseteq> D\<close>] insert.prems \<open>d \<in> convex hull C\<close>)
      from insert
      have "ccw a b c"
        by simp
      from convex2[OF \<open>0 \<le> u\<close> \<open>0 \<le> v\<close> \<open>u + v = 1\<close> \<open>ccw a b c\<close> \<open>ccw a b d\<close> \<open>oriented a b\<close>]
      have ?case by (simp add: x)
    } ultimately show ?case by blast
  qed
qed

end

end

