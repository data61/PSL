theory Polygon
imports Counterclockwise_2D_Strict
begin

subsection \<open>Polygonal chains\<close>

definition "polychain xs = (\<forall>i. Suc i<length xs \<longrightarrow> snd (xs ! i) = (fst (xs ! Suc i)))"

lemma polychainI:
  assumes "\<And>i. Suc i < length xs \<Longrightarrow> snd (xs ! i) = fst (xs ! Suc i)"
  shows "polychain xs"
  by (auto intro!: assms simp: polychain_def)

lemma polychain_Nil[simp]: "polychain [] = True"
  and polychain_singleton[simp]: "polychain [x] = True"
  by (auto simp: polychain_def)

lemma polychain_Cons:
  "polychain (y # ys) = (if ys = [] then True else snd y = fst (ys ! 0) \<and> polychain ys)"
  by (auto simp: polychain_def nth_Cons split: nat.split)

lemma polychain_appendI:
  "polychain xs \<Longrightarrow> polychain ys \<Longrightarrow> (xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> snd (last xs) = fst (hd ys)) \<Longrightarrow>
    polychain (xs @ ys)"
  by (induct xs arbitrary: ys)
    (auto simp add: polychain_Cons nth_append hd_conv_nth split: if_split_asm)

fun pairself where "pairself f (x, y) = (f x, f y)"

lemma pairself_apply: "pairself f x = (f (fst x), f (snd x))"
  by (cases x, simp)

lemma polychain_map_pairself: "polychain xs \<Longrightarrow> polychain (map (pairself f) xs)"
  by (auto simp: polychain_def pairself_apply)

definition "convex_polychain xs \<longleftrightarrow>
  (polychain xs \<and>
  (\<forall>i. Suc i < length xs \<longrightarrow> det3 (fst (xs ! i)) (snd (xs ! i)) (snd (xs ! Suc i)) > 0))"

lemma convex_polychain_Cons2[simp]:
  "convex_polychain (x#y#zs) \<longleftrightarrow>
    snd x = fst y \<and> det3 (fst x) (fst y) (snd y) > 0 \<and> convex_polychain (y#zs)"
  by (auto simp add: convex_polychain_def polychain_def nth_Cons split: nat.split)

lemma convex_polychain_ConsD:
  assumes "convex_polychain (x#xs)"
  shows "convex_polychain xs"
  using assms by (auto simp: convex_polychain_def polychain_def nth_Cons split: nat.split)

definition
  "convex_polygon xs \<longleftrightarrow> (convex_polychain xs \<and> (xs \<noteq> [] \<longrightarrow> fst (hd xs) = snd (last xs)))"

lemma convex_polychain_Nil[simp]: "convex_polychain [] = True"
  and convex_polychain_Cons[simp]: "convex_polychain [x] = True"
  by (auto simp: convex_polychain_def)

lemma convex_polygon_Cons2[simp]:
  "convex_polygon (x#y#zs) \<longleftrightarrow> fst x = snd (last (y#zs)) \<and> convex_polychain (x#y#zs)"
  by (auto simp: convex_polygon_def convex_polychain_def polychain_def nth_Cons)

lemma polychain_append_connected:
  "polychain (xs @ ys) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> fst (hd ys) = snd (last xs)"
  by (auto simp: convex_polychain_def nth_append not_less polychain_def last_conv_nth hd_conv_nth
    dest!: spec[where x = "length xs - 1"])

lemma convex_polychain_appendI:
  assumes cxs: "convex_polychain xs"
  assumes cys: "convex_polychain ys"
  assumes pxy: "polychain (xs @ ys)"
  assumes "xs \<noteq> [] \<Longrightarrow> ys \<noteq> [] \<Longrightarrow> det3 (fst (last xs)) (snd (last xs)) (snd (hd ys)) > 0"
  shows "convex_polychain (xs @ ys)"
proof -
  {
    fix i
    assume "i < length xs" "length xs \<le> Suc i" "Suc i < length xs + length ys"
    hence "xs \<noteq> []" "ys \<noteq> []" "i = length xs - 1" by auto
  }
  thus ?thesis
    using assms
    by (auto simp: hd_conv_nth convex_polychain_def nth_append Suc_diff_le last_conv_nth )
qed

lemma convex_polychainI:
  assumes "polychain xs"
  assumes "\<And>i. Suc i < length xs \<Longrightarrow> det3 (fst (xs ! i)) (snd (xs ! i)) (snd (xs ! Suc i)) > 0"
  shows "convex_polychain xs"
  by (auto intro!: assms simp: convex_polychain_def ccw'_def)

lemma convex_polygon_skip:
  assumes "convex_polygon (x # y # z # w # ws)"
  assumes "ccw'.sortedP (fst x) (map snd (butlast (x # y # z # w # ws)))"
  shows "convex_polygon ((fst x, snd y) # z # w # ws)"
  using assms by (auto elim!: ccw'.sortedP_Cons simp: ccw'_def[symmetric])


primrec polychain_of::"'a::ab_group_add \<Rightarrow> 'a list \<Rightarrow> ('a*'a) list" where
  "polychain_of xc [] = []"
| "polychain_of xc (xm#xs) = (xc, xc + xm)#polychain_of (xc + xm) xs"

lemma in_set_polychain_ofD: "ab \<in> set (polychain_of x xs) \<Longrightarrow> (snd ab - fst ab) \<in> set xs"
  by (induct xs arbitrary: x) auto

lemma fst_polychain_of_nth_0[simp]: "xs \<noteq> [] \<Longrightarrow> fst ((polychain_of p xs) ! 0) = p"
  by (cases xs) (auto simp: Let_def)

lemma fst_hd_polychain_of: "xs \<noteq> [] \<Longrightarrow> fst (hd (polychain_of x xs)) = x"
  by (cases xs) (auto simp: )

lemma length_polychain_of_eq[simp]:
  shows "length (polychain_of p qs) = length qs"
  by (induct qs arbitrary: p) simp_all

lemma
  polychain_of_subsequent_eq:
  assumes "Suc i < length qs"
  shows "snd (polychain_of p qs ! i) = fst (polychain_of p qs ! Suc i)"
  using assms
  by (induct qs arbitrary: p i) (auto simp add: nth_Cons split: nat.split)

lemma polychain_of_eq_empty_iff[simp]: "polychain_of p xs = [] \<longleftrightarrow> xs = []"
  by (cases xs) (auto simp: Let_def)

lemma in_set_polychain_of_imp_sum_list:
  assumes "z \<in> set (polychain_of Pc Ps)"
  obtains d where "z = (Pc + sum_list (take d Ps), Pc + sum_list (take (Suc d) Ps))"
  using assms
  apply atomize_elim
proof (induction Ps arbitrary: Pc z)
  case Nil thus ?case by simp
next
  case (Cons P Ps)
  hence "z = (Pc, Pc + P) \<or> z \<in> set (polychain_of (Pc + P) Ps)"
    by auto
  thus ?case
  proof
    assume "z \<in> set ((polychain_of (Pc + P) Ps))"
    from Cons.IH[OF this]
    obtain d
    where "z = (Pc + P + sum_list (take d Ps), Pc + P + sum_list (take (Suc d) Ps))"
      by auto
    thus ?case
      by (auto intro!: exI[where x="Suc d"])
  qed (auto intro!: exI[where x=0])
qed

lemma last_polychain_of: "length xs > 0 \<Longrightarrow> snd (last (polychain_of p xs)) = p + sum_list xs"
  by (induct xs arbitrary: p) simp_all

lemma polychain_of_singleton_iff: "polychain_of p xs = [a] \<longleftrightarrow> fst a = p \<and> xs = [(snd a - p)]"
  by (induct xs) auto

lemma polychain_of_add: "polychain_of (x + y) xs = map (((+) (y, y))) (polychain_of x xs)"
  by (induct xs arbitrary: x y) (auto simp: algebra_simps)

subsection \<open>Dirvec: Inverse of Polychain\<close>

primrec dirvec where "dirvec (x, y) = (y - x)"

lemma dirvec_minus: "dirvec x = snd x - fst x"
  by (cases x) simp

lemma dirvec_nth_polychain_of: "n < length xs \<Longrightarrow> dirvec ((polychain_of p xs) ! n ) = (xs ! n)"
  by (induct xs arbitrary: p n) (auto simp: nth_Cons split: nat.split)

lemma dirvec_hd_polychain_of: "xs \<noteq> [] \<Longrightarrow> dirvec (hd (polychain_of p xs)) = (hd xs)"
  by (simp add: hd_conv_nth dirvec_nth_polychain_of)

lemma dirvec_last_polychain_of: "xs \<noteq> [] \<Longrightarrow> dirvec (last (polychain_of p xs)) = (last xs)"
  by (simp add: last_conv_nth dirvec_nth_polychain_of)

lemma map_dirvec_polychain_of[simp]: "map dirvec (polychain_of x xs) = xs"
  by (induct xs arbitrary: x) simp_all


subsection \<open>Polychain of Sorted (@{term polychain_of}, @{term ccw'.sortedP})\<close>

lemma ccw'_sortedP_translateD:
  "linorder_list0.sortedP (ccw' x0) (map ((+) x \<circ> g) xs) \<Longrightarrow>
    linorder_list0.sortedP (ccw' (x0 - x)) (map g xs)"
proof (induct xs arbitrary: x0 x)
  case Nil thus ?case by (auto simp: linorder_list0.sortedP.Nil)
next
  case (Cons a xs x0 x)
  hence "\<forall>y\<in>set xs. ccw' (x0 - x) (g a) (g y)"
    by (auto elim!: linorder_list0.sortedP_Cons simp: ccw'.translate_origin algebra_simps)
  thus ?case
    using Cons.prems(1)
    by (auto elim!: linorder_list0.sortedP_Cons intro!: linorder_list0.sortedP.Cons simp: Cons.hyps)
qed

lemma ccw'_sortedP_translateI:
  "linorder_list0.sortedP (ccw' (x0 - x)) (map g xs) \<Longrightarrow>
    linorder_list0.sortedP (ccw' x0) (map ((+) x \<circ> g) xs)"
  using ccw'_sortedP_translateD[of "x0 - x" "-x" "(+) x o g" xs]
  by (simp add: o_def)

lemma ccw'_sortedP_translate_comp[simp]:
  "linorder_list0.sortedP (ccw' x0) (map ((+) x \<circ> g) xs) \<longleftrightarrow>
    linorder_list0.sortedP (ccw' (x0 - x)) (map g xs)"
  by (metis ccw'_sortedP_translateD ccw'_sortedP_translateI)

lemma snd_plus_commute: "snd \<circ> (+) (x0, x0) = (+) x0 o snd"
  by auto

lemma ccw'_sortedP_renormalize:
  "ccw'.sortedP a (map snd (polychain_of (x0 + x) xs)) \<longleftrightarrow>
   ccw'.sortedP (a - x0) (map snd (polychain_of x xs))"
  by (simp add: polychain_of_add add.commute snd_plus_commute)

lemma ccw'_sortedP_polychain_of01:
  shows "ccw'.sortedP 0 [u] \<Longrightarrow> ccw'.sortedP x0 (map snd (polychain_of x0 [u]))"
    and "ccw'.sortedP 0 [] \<Longrightarrow> ccw'.sortedP x0 (map snd (polychain_of x0 []))"
  by (auto intro!: linorder_list0.sortedP.Nil linorder_list0.sortedP.Cons  simp: ac_simps)

lemma ccw'_sortedP_polychain_of2:
  assumes "ccw'.sortedP 0 [u, v]"
  shows "ccw'.sortedP x0 (map snd (polychain_of x0 [u, v]))"
  using assms
  by (auto intro!: linorder_list0.sortedP.Nil linorder_list0.sortedP.Cons
    elim!: linorder_list0.sortedP_Cons simp: ac_simps ccw'.translate_origin)

lemma ccw'_sortedP_polychain_of3:
  assumes "ccw'.sortedP 0 (u#v#w#xs)"
  shows "ccw'.sortedP x0 (map snd (polychain_of x0 (u#v#w#xs)))"
  using assms
proof (induct xs arbitrary: x0 u v w)
  case Nil
  then have *: "ccw' 0 u v" "ccw' 0 v w" "ccw' 0 u w"
    by (auto intro!: linorder_list0.sortedP.Nil linorder_list0.sortedP.Cons
      elim!: linorder_list0.sortedP_Cons simp: ac_simps)
  moreover have "ccw' 0 (u + v) (u + (v + w))"
    by (metis add.assoc ccw'.add1 ccw'.add3_self *(2-))
  ultimately show ?case
    by (auto intro!: linorder_list0.sortedP.Nil linorder_list0.sortedP.Cons
      elim!: linorder_list0.sortedP_Cons simp: ac_simps ccw'.translate_origin ccw'.add3)
next
  case (Cons y ys)
  have s1: "linorder_list0.sortedP (ccw' 0)  ((u + v)#w#y#ys)" using Cons.prems
    by (auto intro!: linorder_list0.sortedP.Nil linorder_list0.sortedP.Cons
      elim!: linorder_list0.sortedP_Cons simp: ccw'.add1)
  have s2: "linorder_list0.sortedP (ccw' 0)  (u#(v + w)#y#ys)" using Cons.prems
    by (auto intro!: linorder_list0.sortedP.Nil linorder_list0.sortedP.Cons
      elim!: linorder_list0.sortedP_Cons simp: ccw'.add3 ccw'.add1)
  have s3: "linorder_list0.sortedP (ccw' 0)  (u#v#(w + y)#ys)" using Cons.prems
    by (auto intro!: linorder_list0.sortedP.Nil linorder_list0.sortedP.Cons
      elim!: linorder_list0.sortedP_Cons simp: ccw'.add3 ccw'.add1)
  show ?case
    using Cons.hyps[OF s1, of x0] Cons.hyps[OF s2, of x0] Cons.hyps[OF s3, of x0] Cons.prems
    by (auto intro!: linorder_list0.sortedP.Nil linorder_list0.sortedP.Cons
      elim!: linorder_list0.sortedP_Cons simp: ac_simps)
qed

lemma ccw'_sortedP_polychain_of_snd:
  assumes "ccw'.sortedP 0 xs"
  shows "ccw'.sortedP x0 (map snd (polychain_of x0 xs))"
  using assms
  by (metis ccw'_sortedP_polychain_of01 ccw'_sortedP_polychain_of2 ccw'_sortedP_polychain_of3
    list.exhaust)

lemma ccw'_sortedP_implies_distinct:
  assumes "ccw'.sortedP x qs"
  shows "distinct qs"
  using assms
proof induct
  case Cons thus ?case by (meson ccw'_contra distinct.simps(2))
qed simp

lemma ccw'_sortedP_implies_nonaligned:
  assumes "ccw'.sortedP x qs"
  assumes "y \<in> set qs" "z \<in> set qs" "y \<noteq> z"
  shows "\<not> coll x y z"
  using assms
  by induct (force simp: ccw'_def det3_def' algebra_simps)+

lemma list_all_mp: "list_all P xs \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> Q x) \<Longrightarrow> list_all Q xs"
  by (auto simp: list_all_iff)

lemma
  ccw'_scale_origin:
  assumes "e \<in> UNIV \<rightarrow> {0<..<1}"
  assumes "x \<in> set (polychain_of Pc (P # QRRs))"
  assumes "ccw'.sortedP 0 (P # QRRs)"
  assumes "ccw' (fst x) (snd x) (P + (Pc + (\<Sum>P\<in>set QRRs. e P *\<^sub>R P)))"
  shows "ccw' (fst x) (snd x) (e P *\<^sub>R P + (Pc + (\<Sum>P\<in>set QRRs. e P *\<^sub>R P)))"
proof -
  from assms(2) have "fst x = Pc \<and> snd x = Pc + P \<or> x \<in> set (polychain_of (Pc + P) QRRs)" by auto
  thus ?thesis
  proof
    assume x: "x \<in> set (polychain_of (Pc + P) QRRs)"
    define q where "q = snd x - fst x"
    from Polygon.in_set_polychain_of_imp_sum_list[OF x]
    obtain d where d: "fst x = (Pc + P + sum_list (take d QRRs))" by (auto simp: prod_eq_iff)
    from in_set_polychain_ofD[OF x]
    have q_in: "q \<in> set QRRs" by (simp add: q_def)
    define R where "R = set QRRs - {q}"
    hence QRRs: "set QRRs = R \<union> {q}" "q \<notin> R" "finite R" using q_in by auto
    have "ccw' 0 q (-P)"
      using assms(3)
      by (auto simp: ccw'.sortedP_Cons_iff q_in)
    hence "ccw' 0 q ((1 - e P) *\<^sub>R (-P))"
      using assms(1) by (subst ccw'.scaleR2_eq) (auto simp: algebra_simps)
    moreover
    from assms(4) have "ccw' 0 q ((\<Sum>P\<in>set QRRs. e P *\<^sub>R P) - sum_list (take d QRRs))"
      by (auto simp: q_def ccw'.translate_origin d)
    ultimately
    have "ccw' 0 q ((1 - e P) *\<^sub>R (-P) + ((\<Sum>P\<in>set QRRs. e P *\<^sub>R P) - sum_list (take d QRRs)))"
      by (intro ccw'.add3) auto
    thus ?thesis
      by (auto simp: ccw'.translate_origin q_def algebra_simps d)
  qed (metis (no_types, lifting) add.left_commute assms(4) ccw'.add3_self ccw'.scale_add3
    ccw'.translate)
qed

lemma polychain_of_ccw_convex:
  assumes "e \<in> UNIV \<rightarrow> {0 <..< 1}"
  assumes sorted: "linorder_list0.sortedP (ccw' 0) (P#Q#Ps)"
  shows "list_all
    (\<lambda>(xi, xj). ccw' xi xj (Pc + (\<Sum>P \<in> set (P#Q#Ps). e P *\<^sub>R P)))
    (polychain_of Pc (P#Q#Ps))"
  using assms(1) assms(2)
proof (induct Ps arbitrary: P Q Pc)
  case Nil
  have eq: "e P *\<^sub>R P + e Q *\<^sub>R Q - P = (1 - e P) *\<^sub>R (- P) + e Q *\<^sub>R Q"
    using \<open>e \<in> _\<close>
    by (auto simp add: algebra_simps)
  from Nil ccw'_sortedP_implies_distinct[OF Nil(2)]
  have "P \<noteq> Q" "e P < 1" "0 < e Q" "ccw' 0 P Q"
    by (auto elim!: linorder_list0.sortedP_Cons)
  thus ?case
    by (auto simp: ccw'_not_coll ccw'.translate_origin eq)
next
  case (Cons R Rs)
  hence "ccw' 0 P Q" "P \<noteq> Q" using ccw'_sortedP_implies_distinct[OF Cons(3)]
    by (auto elim!: linorder_list0.sortedP_Cons)
  have "list_all (\<lambda>(xi, xj). ccw' xi xj ((Pc + P) + (\<Sum>P\<in>set (Q # R # Rs). e P *\<^sub>R P)))
    (polychain_of (Pc + P) (Q # R # Rs))"
    using Cons(2-)
    by (intro Cons(1)) (auto elim: linorder_list0.sortedP_Cons)
  also have "polychain_of (Pc + P) (Q # R # Rs) = tl (polychain_of Pc (P # Q # R # Rs))"
    by simp
  finally have "list_all (\<lambda>(xi, xj). ccw' xi xj (Pc + P + (\<Sum>P\<in>set (Q # R # Rs). e P *\<^sub>R P)))
    (tl (polychain_of Pc (P # Q # R # Rs)))" .
  moreover
  have "list_all
      (\<lambda>(xi, xj). ccw' xi xj (P + (\<Sum>P\<in>set (Q # R # Rs). e P *\<^sub>R P)))
      (polychain_of P (Q # R # Rs))"
    using Cons(2-)
    by (intro Cons(1)) (auto elim: linorder_list0.sortedP_Cons)
  have "(\<lambda>(xi, xj). ccw' xi xj (Pc + P + (\<Sum>P\<in>set (Q # R # Rs). e P *\<^sub>R P)))
    (hd (polychain_of Pc (P # Q # R # Rs)))"
    using ccw'_sortedP_implies_nonaligned[OF Cons(3), of P Q]
      ccw'_sortedP_implies_nonaligned[OF Cons(3), of Q R]
      ccw'_sortedP_implies_nonaligned[OF Cons(3), of P R]
      Cons(2,3)
    by (auto simp add: Pi_iff add.assoc simp del: scaleR_Pair intro!: ccw'.sum
        elim!: linorder_list0.sortedP_Cons)
  ultimately
  have "list_all
      (\<lambda>(xi, xj). ccw' xi xj (P + (Pc + (\<Sum>P\<in>set (Q # R # Rs). e P *\<^sub>R P))))
      (polychain_of Pc (P # Q # R # Rs))"
    by (simp add: ac_simps)
  hence "list_all
      (\<lambda>(xi, xj). ccw' xi xj (e P *\<^sub>R P + (Pc + (\<Sum>P\<in>set (Q # R # Rs). e P *\<^sub>R P))))
      (polychain_of Pc (P # Q # R # Rs))"
    unfolding split_beta'
    by (rule list_all_mp, intro ccw'_scale_origin[OF assms(1)])
      (auto intro!: ccw'_scale_origin Cons(3))
  thus ?case
    using ccw'_sortedP_implies_distinct[OF Cons(3)] Cons
    by (simp add: ac_simps)
qed

lemma polychain_of_ccw:
  assumes "e \<in> UNIV \<rightarrow> {0 <..< 1}"
  assumes sorted: "ccw'.sortedP 0 qs"
  assumes qs: "length qs \<noteq> 1"
  shows "list_all (\<lambda>(xi, xj). ccw' xi xj (Pc + (\<Sum>P \<in> set qs. e P *\<^sub>R P))) (polychain_of Pc qs)"
  using assms
proof (cases qs)
  case (Cons Q Qs)
  note CQ = this
  show ?thesis using assms
  proof (cases Qs)
    case (Cons R Rs)
    thus ?thesis using assms
      unfolding CQ Cons
      by (intro polychain_of_ccw_convex) (auto simp: CQ Cons intro!: polychain_of_ccw_convex)
  qed (auto simp: CQ)
qed simp

lemma in_polychain_of_ccw:
  assumes "e \<in> UNIV \<rightarrow> {0 <..< 1}"
  assumes "ccw'.sortedP 0 qs"
  assumes "length qs \<noteq> 1"
  assumes "seg \<in> set (polychain_of Pc qs)"
  shows "ccw' (fst seg) (snd seg) (Pc + (\<Sum>P \<in> set qs. e P *\<^sub>R P))"
  using polychain_of_ccw[OF assms(1,2,3)] assms(4)
  by (simp add: list_all_iff split_beta)

lemma distinct_butlast_ne_last: "distinct xs \<Longrightarrow> x \<in> set (butlast xs) \<Longrightarrow> x \<noteq> last xs"
  by (metis append_butlast_last_id distinct_butlast empty_iff in_set_butlastD list.set(1)
    not_distinct_conv_prefix)

lemma
  ccw'_sortedP_convex_rotate_aux:
  assumes "ccw'.sortedP 0 (zs)" "ccw'.sortedP x (map snd (polychain_of x (zs)))"
  shows "ccw'.sortedP (snd (last (polychain_of x (zs)))) (map snd (butlast (polychain_of x (zs))))"
  using assms
proof (induct zs arbitrary: x rule: list.induct)
  case (Cons z zs)
  {
    assume "zs \<noteq> []"
    have "ccw'.sortedP (snd (last (polychain_of (x + z) zs)))
      (map snd (butlast (polychain_of (x + z) zs)))"
      using Cons.prems
      by (auto elim!: ccw'.sortedP_Cons intro!: ccw'_sortedP_polychain_of_snd Cons.hyps)
    from _ this
    have "linorder_list0.sortedP (ccw' (snd (last (polychain_of (x + z) zs))))
       ((x + z) # map snd (butlast (polychain_of (x + z) zs)))"
    proof (rule ccw'.sortedP.Cons, safe)
      fix c d
      assume cd: "(c, d) \<in> set (map snd (butlast (polychain_of (x + z) zs)))"
      then obtain a b where ab: "((a, b), c, d) \<in> set (butlast (polychain_of (x + z) zs))"
        by auto
      have cd': "(c, d) \<in> set (butlast (map snd (polychain_of (x + z) zs)))" using cd
        by (auto simp: map_butlast)
      have "ccw' (x + z) (c, d) (last (map snd (polychain_of (x + z) zs)))"
      proof (rule ccw'.sortedP_right_of_last)
        show "ccw'.sortedP (x + z) (map snd (polychain_of (x + z) zs))"
           using Cons
           by (force intro!: ccw'.sortedP.Cons ccw'.sortedP.Nil ccw'_sortedP_polychain_of_snd
             elim!: ccw'.sortedP_Cons)
        show "(c, d) \<in> set (map snd (polychain_of (x + z) zs))"
          using in_set_butlastD[OF ab]
          by force
        from Cons(3) cd'
        show "(c, d) \<noteq> last (map snd (polychain_of (x + z) zs))"
          by (intro distinct_butlast_ne_last ccw'_sortedP_implies_distinct[where x=x])
            (auto elim!: ccw'.sortedP_Cons)
      qed
      thus "ccw' (snd (last (polychain_of (x + z) zs))) (x + z) (c, d)"
         by (auto simp: last_map[symmetric, where f= snd] \<open>zs \<noteq> []\<close> intro: ccw'.cyclicI)
    qed
  }
  thus ?case
    by (auto simp: ccw'.sortedP.Nil)
qed (simp add: ccw'.sortedP.Nil)

lemma ccw'_polychain_of_sorted_center_last:
  assumes set_butlast: "(c, d) \<in> set (butlast (polychain_of x0 xs))"
  assumes sorted: "ccw'.sortedP 0 xs"
  assumes ne: "xs \<noteq> []"
  shows "ccw' x0 d (snd (last (polychain_of x0 xs)))"
proof -
  from ccw'_sortedP_polychain_of_snd[OF sorted, of x0]
  have "ccw'.sortedP x0 (map snd (polychain_of x0 xs))" .
  also
  from set_butlast obtain ys zs where "butlast (polychain_of x0 xs) = ys@((c, d)#zs)"
    by (auto simp add: in_set_conv_decomp)
  hence "polychain_of x0 xs = ys @ (c, d) # zs @ [last (polychain_of x0 xs)]"
    by (metis append_Cons append_assoc append_butlast_last_id ne polychain_of_eq_empty_iff)
  finally show ?thesis by (auto elim!: ccw'.sortedP_Cons simp: ccw'.sortedP_append_iff)
qed

end
