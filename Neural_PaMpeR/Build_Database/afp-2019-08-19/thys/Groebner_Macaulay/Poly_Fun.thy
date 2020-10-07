section \<open>Integer Polynomial Functions\<close>

theory Poly_Fun
  imports Binomial_Int "HOL-Computational_Algebra.Polynomial"
begin

subsection \<open>Definition and Basic Properties\<close>

definition poly_fun :: "(int \<Rightarrow> int) \<Rightarrow> bool"
  where "poly_fun f \<longleftrightarrow> (\<exists>p::rat poly. \<forall>a. rat_of_int (f a) = poly p (rat_of_int a))"

lemma poly_funI: "(\<And>a. rat_of_int (f a) = poly p (rat_of_int a)) \<Longrightarrow> poly_fun f"
  by (auto simp: poly_fun_def)

lemma poly_funE:
  assumes "poly_fun f"
  obtains p where "\<And>a. rat_of_int (f a) = poly p (rat_of_int a)"
  using assms by (auto simp: poly_fun_def)

lemma poly_fun_eqI:
  assumes "poly_fun f" and "poly_fun g" and "infinite {a. f a = g a}"
  shows "f = g"
proof (rule ext)
  fix a
  from assms(1) obtain p where p: "\<And>a. rat_of_int (f a) = poly p (rat_of_int a)"
    by (rule poly_funE, blast)
  from assms(2) obtain q where q: "\<And>a. rat_of_int (g a) = poly q (rat_of_int a)"
    by (rule poly_funE, blast)
  have "p = q"
  proof (rule ccontr)
    let ?A = "{a. poly p (rat_of_int a) = poly q (rat_of_int a)}"
    assume "p \<noteq> q"
    hence "p - q \<noteq> 0" by simp
    hence fin: "finite {x. poly (p - q) x = 0}" by (rule poly_roots_finite)
    have "rat_of_int ` ?A \<subseteq> {x. poly (p - q) x = 0}" by (simp add: image_Collect_subsetI)
    hence "finite (rat_of_int ` ?A)" using fin by (rule finite_subset)
    moreover have "inj_on rat_of_int ?A" by (simp add: inj_on_def)
    ultimately have "finite ?A" by (simp only: finite_image_iff)
    also have "?A = {a. f a = g a}" by (simp flip: p q)
    finally show False using assms(3) by simp
  qed
  hence "rat_of_int (f a) = rat_of_int (g a)" by (simp add: p q)
  thus "f a = g a" by simp
qed

corollary poly_fun_eqI_ge:
  assumes "poly_fun f" and "poly_fun g" and "\<And>a. b \<le> a \<Longrightarrow> f a = g a"
  shows "f = g"
  using assms(1, 2)
proof (rule poly_fun_eqI)
  have "{b..} \<subseteq> {a. f a = g a}" by (auto intro: assms(3))
  thus "infinite {a. f a = g a}" using infinite_Ici by (rule infinite_super)
qed

corollary poly_fun_eqI_gr:
  assumes "poly_fun f" and "poly_fun g" and "\<And>a. b < a \<Longrightarrow> f a = g a"
  shows "f = g"
  using assms(1, 2)
proof (rule poly_fun_eqI)
  have "{b<..} \<subseteq> {a. f a = g a}" by (auto intro: assms(3))
  thus "infinite {a. f a = g a}" using infinite_Ioi by (rule infinite_super)
qed

subsection \<open>Closure Properties\<close>

lemma poly_fun_const [simp]: "poly_fun (\<lambda>_. c)"
  by (rule poly_funI[where p="[:rat_of_int c:]"]) simp

lemma poly_fun_id [simp]: "poly_fun (\<lambda>x. x)" "poly_fun id"
proof -
  show "poly_fun (\<lambda>x. x)" by (rule poly_funI[where p="[:0, 1:]"]) simp
  thus "poly_fun id" by (simp only: id_def)
qed

lemma poly_fun_uminus:
  assumes "poly_fun f"
  shows "poly_fun (\<lambda>x. - f x)" and "poly_fun (- f)"
proof -
  from assms obtain p where p: "\<And>a. rat_of_int (f a) = poly p (rat_of_int a)"
    by (rule poly_funE, blast)
  show "poly_fun (\<lambda>x. - f x)" by (rule poly_funI[where p="- p"]) (simp add: p)
  thus "poly_fun (- f)" by (simp only: fun_Compl_def)
qed

lemma poly_fun_uminus_iff [simp]:
  "poly_fun (\<lambda>x. - f x) \<longleftrightarrow> poly_fun f" "poly_fun (- f) \<longleftrightarrow> poly_fun f"
proof -
  show "poly_fun (\<lambda>x. - f x) \<longleftrightarrow> poly_fun f"
  proof
    assume "poly_fun (\<lambda>x. - f x)"
    hence "poly_fun (\<lambda>x. - (- f x))" by (rule poly_fun_uminus)
    thus "poly_fun f" by simp
  qed (rule poly_fun_uminus)
  thus "poly_fun (- f) \<longleftrightarrow> poly_fun f" by (simp only: fun_Compl_def)
qed

lemma poly_fun_plus [simp]:
  assumes "poly_fun f" and "poly_fun g"
  shows "poly_fun (\<lambda>x. f x + g x)"
proof -
  from assms(1) obtain p where p: "\<And>a. rat_of_int (f a) = poly p (rat_of_int a)"
    by (rule poly_funE, blast)
  from assms(2) obtain q where q: "\<And>a. rat_of_int (g a) = poly q (rat_of_int a)"
    by (rule poly_funE, blast)
  show ?thesis by (rule poly_funI[where p="p + q"]) (simp add: p q)
qed

lemma poly_fun_minus [simp]:
  assumes "poly_fun f" and "poly_fun g"
  shows "poly_fun (\<lambda>x. f x - g x)"
proof -
  from assms(1) obtain p where p: "\<And>a. rat_of_int (f a) = poly p (rat_of_int a)"
    by (rule poly_funE, blast)
  from assms(2) obtain q where q: "\<And>a. rat_of_int (g a) = poly q (rat_of_int a)"
    by (rule poly_funE, blast)
  show ?thesis by (rule poly_funI[where p="p - q"]) (simp add: p q)
qed

lemma poly_fun_times [simp]:
  assumes "poly_fun f" and "poly_fun g"
  shows "poly_fun (\<lambda>x. f x * g x)"
proof -
  from assms(1) obtain p where p: "\<And>a. rat_of_int (f a) = poly p (rat_of_int a)"
    by (rule poly_funE, blast)
  from assms(2) obtain q where q: "\<And>a. rat_of_int (g a) = poly q (rat_of_int a)"
    by (rule poly_funE, blast)
  show ?thesis by (rule poly_funI[where p="p * q"]) (simp add: p q)
qed

lemma poly_fun_divide:
  assumes "poly_fun f" and "\<And>a. c dvd f a"
  shows "poly_fun (\<lambda>x. f x div c)"
proof -
  from assms(1) obtain p where p: "\<And>a. rat_of_int (f a) = poly p (rat_of_int a)"
    by (rule poly_funE, blast)
  let ?p = "p * [:1 / rat_of_int c:]"
  show ?thesis
  proof (rule poly_funI)
    fix a
    have "c dvd f a" by fact
    hence "rat_of_int (f a div c) = rat_of_int (f a) / rat_of_int c" by auto
    also have "\<dots> = poly ?p (rat_of_int a)" by (simp add: p)
    finally show "rat_of_int (f a div c) = poly ?p (rat_of_int a)" .
  qed
qed

lemma poly_fun_pow [simp]:
  assumes "poly_fun f"
  shows "poly_fun (\<lambda>x. f x ^ k)"
proof -
  from assms(1) obtain p where p: "\<And>a. rat_of_int (f a) = poly p (rat_of_int a)"
    by (rule poly_funE, blast)
  show ?thesis by (rule poly_funI[where p="p ^ k"]) (simp add: p)
qed

lemma poly_fun_comp:
  assumes "poly_fun f" and "poly_fun g"
  shows "poly_fun (\<lambda>x. f (g x))" and "poly_fun (f \<circ> g)"
proof -
  from assms(1) obtain p where p: "\<And>a. rat_of_int (f a) = poly p (rat_of_int a)"
    by (rule poly_funE, blast)
  from assms(2) obtain q where q: "\<And>a. rat_of_int (g a) = poly q (rat_of_int a)"
    by (rule poly_funE, blast)
  show "poly_fun (\<lambda>x. f (g x))" by (rule poly_funI[where p="p \<circ>\<^sub>p q"]) (simp add: p q poly_pcompose)
  thus "poly_fun (f \<circ> g)" by (simp only: comp_def)
qed

lemma poly_fun_sum [simp]: "(\<And>i. i \<in> I \<Longrightarrow> poly_fun (f i)) \<Longrightarrow> poly_fun (\<lambda>x. (\<Sum>i\<in>I. f i x))"
proof (induct I rule: infinite_finite_induct)
  case (infinite I)
  from infinite(1) show ?case by simp
next
  case empty
  show ?case by simp
next
  case (insert i I)
  have "i \<in> insert i I" by simp
  hence "poly_fun (f i)" by (rule insert.prems)
  moreover have "poly_fun (\<lambda>x. \<Sum>i\<in>I. f i x)"
  proof (rule insert.hyps)
    fix j
    assume "j \<in> I"
    hence "j \<in> insert i I" by simp
    thus "poly_fun (f j)" by (rule insert.prems)
  qed
  ultimately have "poly_fun (\<lambda>x. f i x + (\<Sum>i\<in>I. f i x))" by (rule poly_fun_plus)
  with insert.hyps(1, 2) show ?case by simp
qed

lemma poly_fun_prod [simp]: "(\<And>i. i \<in> I \<Longrightarrow> poly_fun (f i)) \<Longrightarrow> poly_fun (\<lambda>x. (\<Prod>i\<in>I. f i x))"
proof (induct I rule: infinite_finite_induct)
  case (infinite I)
  from infinite(1) show ?case by simp
next
  case empty
  show ?case by simp
next
  case (insert i I)
  have "i \<in> insert i I" by simp
  hence "poly_fun (f i)" by (rule insert.prems)
  moreover have "poly_fun (\<lambda>x. \<Prod>i\<in>I. f i x)"
  proof (rule insert.hyps)
    fix j
    assume "j \<in> I"
    hence "j \<in> insert i I" by simp
    thus "poly_fun (f j)" by (rule insert.prems)
  qed
  ultimately have "poly_fun (\<lambda>x. f i x * (\<Prod>i\<in>I. f i x))" by (rule poly_fun_times)
  with insert.hyps(1, 2) show ?case by simp
qed

lemma poly_fun_pochhammer [simp]: "poly_fun f \<Longrightarrow> poly_fun (\<lambda>x. pochhammer (f x) k)"
  by (simp add: pochhammer_prod)

lemma poly_fun_gbinomial [simp]: "poly_fun f \<Longrightarrow> poly_fun (\<lambda>x. f x gchoose k)"
  by (simp add: gbinomial_int_pochhammer' poly_fun_divide fact_dvd_pochhammer)

end (* theory *)
