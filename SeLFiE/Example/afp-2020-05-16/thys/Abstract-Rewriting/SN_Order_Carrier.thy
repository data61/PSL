(*  Title:       Executable multivariate polynomials
    Author:      Christian Sternagel <christian.sternagel@uibk.ac.at>
                 Rene Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and Rene Thiemann
    License:     LGPL
*)

(*
Copyright 2010 Christian Sternagel and René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)

section \<open>Carriers of Strongly Normalizing Orders\<close>

theory SN_Order_Carrier
imports
  SN_Orders
  HOL.Rat
begin

text \<open>
  This theory shows that standard semirings can be used 
  in combination with polynomials, e.g. the naturals, integers,
  and arbitrary Archemedean fields by using delta-orders.
  
  It also contains the arctic integers and arctic delta-orders where
  0 is -infty, 1 is zero, + is max and * is plus.
\<close>

subsection \<open>The standard semiring over the naturals\<close>

instantiation nat :: large_ordered_semiring_1 
begin
instance by (intro_classes, auto)
end

definition nat_mono :: "nat \<Rightarrow> bool" where "nat_mono x \<equiv> x \<noteq> 0"

interpretation nat_SN: SN_strict_mono_ordered_semiring_1 1 "(>) :: nat \<Rightarrow> nat \<Rightarrow> bool" nat_mono
  by (unfold_locales, insert SN_nat_gt, auto simp: nat_mono_def)

interpretation nat_poly: poly_order_carrier 1 "(>) :: nat \<Rightarrow> nat \<Rightarrow> bool" True discrete
proof (unfold_locales)
  fix x y :: nat
  assume ge: "x \<ge> y"
  obtain k where k: "x - y = k" by auto
  show "\<exists> k. x = ((+) 1 ^^ k) y" 
  proof (rule exI[of _ k])
    from ge k have "x = k + y" by simp
    also have "\<dots> = ((+) 1 ^^ k) y" 
      by (induct k, auto)
    finally show "x = ((+) 1 ^^ k) y" .
  qed
qed (auto simp: field_simps power_strict_mono)
      

subsection \<open>The standard semiring over the Archimedean fields using delta-orderings\<close>

definition delta_gt :: "'a :: floor_ceiling \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where 
  "delta_gt \<delta> \<equiv> (\<lambda> x y. x - y \<ge> \<delta>)"

lemma non_inf_delta_gt: assumes delta: "\<delta> > 0"
  shows "non_inf {(a,b) . delta_gt \<delta> a b}" (is "non_inf ?r")
proof
  let ?gt = "delta_gt \<delta>"
  fix a :: 'a and f
  assume "\<And> i. (f i, f (Suc i)) \<in> ?r"
  hence gt: "\<And> i. ?gt (f i) (f (Suc i))" by simp
  {
    fix i
    have "f i \<le> f 0 - \<delta> * of_nat i"
    proof (induct i)
      case (Suc i)
      thus ?case using gt[of i, unfolded delta_gt_def] by (auto simp: field_simps)
    qed simp
  } note fi = this
  {
    fix r :: 'a
    have "of_nat (nat (ceiling r)) \<ge> r" 
      by (metis ceiling_le_zero le_of_int_ceiling less_le_not_le nat_0_iff not_less of_nat_0 of_nat_nat)
  } note ceil_elim = this
  define i where "i = nat (ceiling ((f 0 - a) / \<delta>))"
  from fi[of i] have "f i - f 0 \<le> - \<delta> * of_nat (nat (ceiling ((f 0 - a) / \<delta>)))" unfolding i_def by simp
  also have "\<dots> \<le> - \<delta> * ((f 0 - a) / \<delta>)" using ceil_elim[of "(f 0 - a) / \<delta>"] delta
    by (metis le_imp_neg_le minus_mult_commute mult_le_cancel_left_pos)
  also have "\<dots> = - f 0 + a" using delta by auto
  also have "\<dots> < - f 0 + a + \<delta>" using delta by auto
  finally have "\<not> ?gt (f i) a" unfolding delta_gt_def by arith
  thus "\<exists> i. (f i, a) \<notin> ?r" by blast
qed

lemma delta_gt_SN: assumes dpos: "\<delta> > 0" shows "SN {(x,y). 0 \<le> y \<and> delta_gt \<delta> x y}"
proof -
  from non_inf_imp_SN_bound[OF non_inf_delta_gt[OF dpos], of "- \<delta>"]
  show ?thesis unfolding delta_gt_def by auto
qed

definition delta_mono :: "'a :: floor_ceiling \<Rightarrow> bool" where "delta_mono x \<equiv> x \<ge> 1"

subclass (in floor_ceiling) large_ordered_semiring_1
proof
  fix x :: 'a
  from ex_le_of_int[of x] obtain z where x: "x \<le> of_int z" by auto
  have "z \<le> int (nat z)" by auto
  with x have "x \<le> of_int (int (nat z))"
    by (metis (full_types) le_cases of_int_0_le_iff of_int_of_nat_eq of_nat_0_le_iff of_nat_nat order_trans)
  also have "\<dots> = of_nat (nat z)" unfolding of_int_of_nat_eq ..
  finally 
  show "\<exists> y. x \<le> of_nat y" by blast
qed (auto simp: mult_right_mono mult_left_mono mult_right_mono_neg max_def) 


lemma delta_interpretation: assumes dpos: "\<delta> > 0" and default: "\<delta> \<le> def"
  shows "SN_strict_mono_ordered_semiring_1 def (delta_gt \<delta>) delta_mono"
proof -
  from dpos default have defz: "0 \<le> def" by auto
  show ?thesis
  proof (unfold_locales)
    show "SN {(x,y). y \<ge> 0 \<and> delta_gt \<delta> x y}" by (rule delta_gt_SN[OF dpos])
  next
    fix x y z :: 'a
    assume "delta_mono x" and yz: "delta_gt \<delta> y z"
    hence x: "1 \<le> x" unfolding delta_mono_def by simp
    have "\<exists> d > 0. delta_gt \<delta> = (\<lambda> x y. d \<le> x - y)" 
      by (rule exI[of _ \<delta>], auto simp: dpos delta_gt_def)
    from this obtain d where d: "0 < d" and rat: "delta_gt \<delta> = (\<lambda> x y. d \<le> x - y)" by auto
    from yz have yzd: "d \<le> y - z" by (simp add: rat)
    show "delta_gt \<delta> (x * y) (x * z)"
    proof (simp only: rat)
      let ?p = "(x - 1) * (y - z)"
      from x have x1: "0 \<le> x - 1" by auto
      from yzd d have yz0: "0 \<le> y - z" by auto
      have "0 \<le> ?p" 
        by (rule mult_nonneg_nonneg[OF x1 yz0])
      have "x * y - x * z = x * (y - z)" using right_diff_distrib[of x y z] by auto
      also have "\<dots> = ((x - 1) + 1) * (y - z)" by auto
      also have "\<dots> = ?p + 1 * ( y - z)" by (rule ring_distribs(2))
      also have "\<dots> = ?p + (y - z)" by simp
      also have "\<dots> \<ge> (0 + d)" using yzd \<open>0 \<le> ?p\<close> by auto
      finally 
      show "d \<le> x * y - x * z" by auto
    qed
  qed (insert dpos, auto simp: delta_gt_def default defz)
qed

lemma delta_poly: assumes dpos: "\<delta> > 0" and default: "\<delta> \<le> def"
  shows "poly_order_carrier def (delta_gt \<delta>) (1 \<le> \<delta>) False"
proof -
  from delta_interpretation[OF dpos default] 
  interpret SN_strict_mono_ordered_semiring_1 "def" "delta_gt \<delta>" delta_mono .
  interpret poly_order_carrier "def" "delta_gt \<delta>" False False
  proof(unfold_locales)
    fix y z x :: 'a
    assume gt: "delta_gt \<delta> y z" and ge: "x \<ge> 1"
    from ge have ge: "x \<ge> 0" and m: "delta_mono x" unfolding delta_mono_def by auto
    show "delta_gt \<delta> (y * x) (z * x)"
      using mono[OF m gt ge] by (auto simp: field_simps)
  next
    fix x y :: 'a and n :: nat
    assume False thus "delta_gt \<delta> (x ^ n) (y ^ n)" ..
  next
    fix x y :: 'a
    assume False
    thus "\<exists> k. x = ((+) 1 ^^ k) y" by simp
  qed
  show ?thesis
  proof(unfold_locales)
    fix x y :: 'a and n :: nat
    assume one: "1 \<le> \<delta>" and gt: "delta_gt \<delta> x y" and y: "y \<ge> 0" and n: "1 \<le> n"
    then obtain p where n: "n = Suc p" and x: "x \<ge> 1" and y2: "0 \<le> y" and xy: "x \<ge> y" by (cases n, auto simp: delta_gt_def)
    show "delta_gt \<delta> (x ^ n) (y ^ n)" 
    proof (simp only: n, induct p, simp add: gt)
      case (Suc p)
      from times_gt_mono[OF this x]
      have one: "delta_gt \<delta> (x ^ Suc (Suc p)) (x * y ^ Suc p)" by (auto simp: field_simps)
      also have "\<dots> \<ge> y * y ^ Suc p" 
        by (rule times_left_mono[OF _ xy], auto simp: zero_le_power[OF y2, of "Suc p", simplified])
      finally show ?case by auto
    qed
  next
    fix x y :: 'a
    assume False
    thus "\<exists> k. x = ((+) 1 ^^ k) y" by simp
  qed (rule times_gt_mono, auto)
qed


lemma delta_minimal_delta: assumes "\<And> x y. (x,y) \<in> set xys \<Longrightarrow> x > y"
  shows "\<exists> \<delta> > 0. \<forall> x y. (x,y) \<in> set xys \<longrightarrow> delta_gt \<delta> x y"
using assms 
proof (induct xys)
  case Nil
  show ?case by (rule exI[of _ 1], auto)
next
  case (Cons xy xys)
  show ?case
  proof (cases xy)
    case (Pair x y)
    with Cons have "x > y" by auto
    then obtain d1 where "d1 = x - y" and d1pos: "d1 > 0" and "d1 \<le> x - y" by auto
    hence xy: "delta_gt d1 x y" unfolding delta_gt_def by auto
    from Cons obtain d2 where d2pos: "d2 > 0" and xys: "\<forall> x y. (x, y) \<in> set xys \<longrightarrow> delta_gt d2 x y" by auto
    obtain d where d: "d = min d1 d2" by auto
    with d1pos d2pos xy have dpos: "d > 0" and "delta_gt d x y" unfolding delta_gt_def by auto
    with xys d Pair have "\<forall> x y. (x,y) \<in> set (xy # xys) \<longrightarrow> delta_gt d x y" unfolding delta_gt_def by force
    with dpos show ?thesis by auto 
  qed
qed

interpretation weak_delta_SN: weak_SN_strict_mono_ordered_semiring_1 "(>)" 1 delta_mono
proof
  fix xysp :: "('a \<times> 'a) list"
  assume orient: "\<forall> x y. (x,y) \<in> set xysp \<longrightarrow> x > y" 
  obtain xys where xsy: "xys = (1,0) # xysp" by auto
  with orient have "\<And> x y. (x,y) \<in> set xys \<Longrightarrow> x > y" by auto
  with delta_minimal_delta have "\<exists> \<delta> > 0. \<forall> x y. (x,y) \<in> set xys \<longrightarrow> delta_gt \<delta> x y" by auto
  then obtain \<delta> where dpos: "\<delta> > 0" and orient: "\<And> x y. (x,y) \<in> set xys \<Longrightarrow> delta_gt \<delta> x y" by auto
  from orient have orient1: "\<forall> x y. (x,y) \<in> set xysp \<longrightarrow> delta_gt \<delta> x y" and orient2: "delta_gt \<delta> 1 0" unfolding xsy by auto
  from orient2 have oned: "\<delta> \<le> 1" unfolding delta_gt_def by auto
  show " \<exists>gt. SN_strict_mono_ordered_semiring_1 1 gt delta_mono \<and> (\<forall>x y. (x, y) \<in> set xysp \<longrightarrow> gt x y)" 
    by (intro exI conjI, rule delta_interpretation[OF dpos oned], rule orient1)
qed


subsection \<open>The standard semiring over the integers\<close>

definition int_mono :: "int \<Rightarrow> bool" where "int_mono x \<equiv> x \<ge> 1"

instantiation int :: large_ordered_semiring_1
begin
instance 
proof 
  fix y :: int
  show "\<exists> x. of_nat x \<ge> y"
    by (rule exI[of _ "nat y"], simp) 
qed (auto simp: mult_right_mono mult_left_mono mult_right_mono_neg)
end

lemma non_inf_int_gt: "non_inf {(a,b :: int) . a > b}" (is "non_inf ?r")
  by (rule non_inf_image[OF non_inf_delta_gt, of 1 _ rat_of_int], auto simp: delta_gt_def)

interpretation int_SN: SN_strict_mono_ordered_semiring_1 1 "(>) :: int \<Rightarrow> int \<Rightarrow> bool" int_mono
proof (unfold_locales)
  have [simp]: "\<And> x :: int . (-1 < x) = (0 \<le> x)" by auto
  show "SN {(x,y). y \<ge> 0 \<and> (y :: int) < x}" 
    using non_inf_imp_SN_bound[OF non_inf_int_gt, of "-1"] by auto
qed (auto simp: mult_strict_left_mono int_mono_def)

interpretation int_poly: poly_order_carrier 1 "(>) :: int \<Rightarrow> int \<Rightarrow> bool" True discrete
proof (unfold_locales)
  fix x y :: int
  assume ge: "x \<ge> y"
  then obtain k where k: "x - y = k" and kp: "0 \<le> k" by auto
  then obtain nk where nk: "nk = nat k" and k: "x - y = int nk" by auto
  show "\<exists> k. x = ((+) 1 ^^ k) y"
  proof (rule exI[of _ nk])
    from k have "x = int nk + y" by simp
    also have "\<dots> = ((+) 1 ^^ nk) y"
      by (induct nk, auto)
    finally show "x = ((+) 1 ^^ nk) y" .
  qed
qed (auto simp: field_simps power_strict_mono)


subsection \<open>The arctic semiring over the integers\<close>
text \<open>plus is interpreted as max, times is interpreted as plus, 0 is -infinity, 1 is 0\<close>

datatype arctic = MinInfty | Num_arc int


instantiation arctic :: ord
begin
fun less_eq_arctic :: "arctic \<Rightarrow> arctic \<Rightarrow> bool" where 
  "less_eq_arctic MinInfty x = True"
| "less_eq_arctic (Num_arc _) MinInfty = False"
| "less_eq_arctic (Num_arc y) (Num_arc x) = (y \<le> x)"

fun less_arctic :: "arctic \<Rightarrow> arctic \<Rightarrow> bool" where 
  "less_arctic MinInfty x = True"
| "less_arctic (Num_arc _) MinInfty = False"
| "less_arctic (Num_arc y) (Num_arc x) = (y < x)"

instance ..
end

instantiation arctic :: ordered_semiring_1
begin
fun plus_arctic :: "arctic \<Rightarrow> arctic \<Rightarrow> arctic" where
  "plus_arctic MinInfty y = y"
| "plus_arctic x MinInfty = x"
| "plus_arctic (Num_arc x) (Num_arc y) = (Num_arc (max x y))"

fun times_arctic :: "arctic \<Rightarrow> arctic \<Rightarrow> arctic" where 
  "times_arctic MinInfty y = MinInfty"
| "times_arctic x MinInfty = MinInfty"
| "times_arctic (Num_arc x) (Num_arc y) = (Num_arc (x + y))"

definition zero_arctic :: arctic where 
  "zero_arctic = MinInfty"

definition one_arctic :: arctic where 
  "one_arctic = Num_arc 0"

instance
proof
  fix x y z :: arctic
  show "x + y = y + x"
    by (cases x, cases y, auto, cases y, auto)
  show "(x + y) + z = x + (y + z)"
    by (cases x, auto, cases y, auto, cases z, auto)
  show "(x * y) * z = x * (y * z)"
    by (cases x, auto, cases y, auto, cases z, auto)
  show "x * 0 = 0"
    by (cases x, auto simp: zero_arctic_def)
  show "x * (y + z) = x * y + x * z"
    by (cases x, auto, cases y, auto, cases z, auto)
  show "(x + y) * z = x * z + y * z"
    by (cases x, auto, cases y, cases z, auto, cases z, auto)
  show "1 * x = x"
    by (cases x, simp_all add: one_arctic_def)
  show "x * 1 = x"
    by (cases x, simp_all add: one_arctic_def)
  show "0 + x = x"
    by (simp add: zero_arctic_def)
  show "0 * x = 0"
    by (simp add: zero_arctic_def)
  show "(0 :: arctic) \<noteq> 1"
    by (simp add: zero_arctic_def one_arctic_def)
  show "x + 0 = x" by (cases x, auto simp: zero_arctic_def)
  show "x \<ge> x" 
    by (cases x, auto)
  show "(1 :: arctic) \<ge> 0"
    by (simp add: zero_arctic_def one_arctic_def)
  show "max x y = max y x" unfolding max_def
    by (cases x, (cases y, auto)+)
  show "max x y \<ge> x" unfolding max_def
    by (cases x, (cases y, auto)+)
  assume ge: "x \<ge> y" 
  from ge show "x + z \<ge> y + z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
  from ge show "x * z \<ge> y * z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
  from ge show "max x y = x" unfolding max_def
    by (cases x, (cases y, auto)+)
  from ge show "max z x \<ge> max z y" unfolding max_def
    by (cases z, cases x, auto, cases x, (cases y, auto)+)  
next
  fix x y z :: arctic
  assume "x \<ge> y" and "y \<ge> z"
  thus "x \<ge> z"
    by (cases x, cases y, auto, cases y, cases z, auto, cases z, auto)
next
  fix x y z :: arctic
  assume "y \<ge> z"
  thus "x * y \<ge> x * z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
next
  fix x y z :: arctic
  show "x \<ge> y \<Longrightarrow> 0 \<ge> z \<Longrightarrow> y * z \<ge> x * z"
    by (cases z, cases x, auto simp: zero_arctic_def)
qed
end



fun get_arctic_num :: "arctic \<Rightarrow> int"
where "get_arctic_num (Num_arc n) = n"

fun pos_arctic :: "arctic \<Rightarrow> bool"
where "pos_arctic MinInfty = False"
    | "pos_arctic (Num_arc n) = (0 <= n)"

interpretation arctic_SN: SN_both_mono_ordered_semiring_1 1 "(>)" pos_arctic
proof 
  fix x y z :: arctic
  assume "x \<ge> y" and "y > z"
  thus "x > z"
    by (cases z, simp, cases y, simp, cases x, auto)
next 
  fix x y z :: arctic
  assume "x > y" and "y \<ge> z"
  thus "x > z"
    by (cases z, simp, cases y, simp, cases x, auto)
next
  fix x y z :: arctic
  assume "x > y" 
  thus "x \<ge> y"
    by (cases x, (cases y, auto)+)
next
  fix x y z u :: arctic
  assume "x > y" and "z > u"
  thus "x + z > y + u"
    by (cases y, cases u, simp, cases z, auto, cases x, auto, cases u, auto, cases z, auto, cases x, auto, cases x, auto, cases z, auto, cases x, auto)
next
  fix x y z :: arctic
  assume "x > y"
  thus "x * z > y * z"
    by (cases y, simp, cases z, simp, cases x, auto)
next
  fix x :: arctic
  assume "0 > x"
  thus "x = 0"
    by (cases x, auto simp: zero_arctic_def)
next
  fix x :: arctic
  show "pos_arctic 1" unfolding one_arctic_def by simp
  show "x > 0" unfolding zero_arctic_def by simp
  show "(1 :: arctic) \<ge> 0" unfolding zero_arctic_def by simp
  show "x \<ge> 0" unfolding zero_arctic_def by simp
  show "\<not> pos_arctic 0" unfolding zero_arctic_def by simp
next
  fix x y
  assume "pos_arctic x" 
  thus "pos_arctic (x + y)" by (cases x, simp, cases y, auto)
next
  fix x y
  assume "pos_arctic x" and "pos_arctic y"
  thus "pos_arctic (x * y)" by (cases x, simp, cases y, auto)
next
  show "SN {(x,y). pos_arctic y \<and> x > y}" (is "SN ?rel")
  proof - {
    fix x
    assume "\<exists> f . f 0 = x \<and> (\<forall> i. (f i, f (Suc i)) \<in> ?rel)"
    from this obtain f where "f 0 = x" and seq: "\<forall> i. (f i, f (Suc i)) \<in> ?rel" by auto
    from seq have steps: "\<forall> i. f i > f (Suc i) \<and> pos_arctic (f (Suc i)) " by auto
    let ?g = "\<lambda> i. get_arctic_num (f i)"
    have "\<forall> i. ?g (Suc i) \<ge> 0 \<and> ?g i  > ?g (Suc i)"
    proof
      fix i
      from steps have i: "f i > f (Suc i) \<and> pos_arctic (f (Suc i))" by auto
      from i obtain n where fi: "f i = Num_arc n" by (cases "f (Suc i)", simp, cases "f i", auto)
      from i obtain m where fsi: "f (Suc i) = Num_arc m" by (cases "f (Suc i)", auto)
      with i have gz: "0 \<le> m" by simp
      from i fi fsi have "n > m" by auto
      with fi fsi gz
      show "?g (Suc i) \<ge> 0 \<and> ?g i > ?g (Suc i)" by auto
    qed
    from this obtain g where "\<forall> i. g (Suc i) \<ge> 0 \<and> ((>) :: int \<Rightarrow> int \<Rightarrow> bool) (g i) (g (Suc i))" by auto
    hence "\<exists> f. f 0 = g 0 \<and> (\<forall> i. (f i, f (Suc i)) \<in> {(x,y). y \<ge> 0 \<and> x > y})" by auto
    with int_SN.SN have False unfolding SN_defs by auto
  }
  thus ?thesis unfolding SN_defs by auto
  qed 
next
  fix y z x :: arctic
  assume "y > z"
  thus "x * y > x * z"
    by (cases x, simp, cases z, simp, cases y, auto)
next
  fix c d
  assume "pos_arctic d" 
  then obtain n where d: "d = Num_arc n" and n: "0 \<le> n"
    by (cases d, auto)  
  show "\<exists> e. e \<ge> 0 \<and> pos_arctic e \<and> \<not> c \<ge> d * e"
  proof (cases c)
    case MinInfty
    show ?thesis
      by (rule exI[of _ "Num_arc 0"],
        unfold d MinInfty zero_arctic_def, simp)
  next
    case (Num_arc m)
    show ?thesis
      by (rule exI[of _ "Num_arc (abs m  + 1)"], insert n,
        unfold d Num_arc zero_arctic_def, simp)
  qed
qed


subsection \<open>The arctic semiring over an arbitrary archimedean field\<close>

text \<open>completely analogous to the integers, where one has to use delta-orderings\<close>

datatype 'a arctic_delta = MinInfty_delta | Num_arc_delta 'a

instantiation arctic_delta :: (ord) ord
begin
fun less_eq_arctic_delta :: "'a arctic_delta \<Rightarrow> 'a arctic_delta \<Rightarrow> bool" where 
  "less_eq_arctic_delta MinInfty_delta x = True"
| "less_eq_arctic_delta (Num_arc_delta _) MinInfty_delta = False"
| "less_eq_arctic_delta (Num_arc_delta y) (Num_arc_delta x) = (y \<le> x)"

fun less_arctic_delta :: "'a arctic_delta \<Rightarrow> 'a arctic_delta \<Rightarrow> bool" where 
  "less_arctic_delta MinInfty_delta x = True"
| "less_arctic_delta (Num_arc_delta _) MinInfty_delta = False"
| "less_arctic_delta (Num_arc_delta y) (Num_arc_delta x) = (y < x)"

instance ..
end

instantiation arctic_delta :: (linordered_field) ordered_semiring_1
begin
fun plus_arctic_delta :: "'a arctic_delta \<Rightarrow> 'a arctic_delta \<Rightarrow> 'a arctic_delta" where
  "plus_arctic_delta MinInfty_delta y = y"
| "plus_arctic_delta x MinInfty_delta = x"
| "plus_arctic_delta (Num_arc_delta x) (Num_arc_delta y) = (Num_arc_delta (max x y))"

fun times_arctic_delta :: "'a arctic_delta \<Rightarrow> 'a arctic_delta \<Rightarrow> 'a arctic_delta" where 
  "times_arctic_delta MinInfty_delta y = MinInfty_delta"
| "times_arctic_delta x MinInfty_delta = MinInfty_delta"
| "times_arctic_delta (Num_arc_delta x) (Num_arc_delta y) = (Num_arc_delta (x + y))"

definition zero_arctic_delta :: "'a arctic_delta" where 
  "zero_arctic_delta = MinInfty_delta"

definition one_arctic_delta :: "'a arctic_delta" where 
  "one_arctic_delta = Num_arc_delta 0"

instance
proof
  fix x y z :: "'a arctic_delta"
  show "x + y = y + x"
    by (cases x, cases y, auto, cases y, auto)
  show "(x + y) + z = x + (y + z)"
    by (cases x, auto, cases y, auto, cases z, auto)
  show "(x * y) * z = x * (y * z)"
    by (cases x, auto, cases y, auto, cases z, auto)
  show "x * 0 = 0"
    by (cases x, auto simp: zero_arctic_delta_def)
  show "x * (y + z) = x * y + x * z"
    by (cases x, auto, cases y, auto, cases z, auto)
  show "(x + y) * z = x * z + y * z"
    by (cases x, auto, cases y, cases z, auto, cases z, auto)
  show "1 * x = x"
    by (cases x, simp_all add: one_arctic_delta_def)
  show "x * 1 = x"
    by (cases x, simp_all add: one_arctic_delta_def)
  show "0 + x = x"
    by (simp add: zero_arctic_delta_def)
  show "0 * x = 0"
    by (simp add: zero_arctic_delta_def)
  show "(0 :: 'a arctic_delta) \<noteq> 1"
    by (simp add: zero_arctic_delta_def one_arctic_delta_def)
  show "x + 0 = x" by (cases x, auto simp: zero_arctic_delta_def)
  show "x \<ge> x" 
    by (cases x, auto)
  show "(1 :: 'a arctic_delta) \<ge> 0"
    by (simp add: zero_arctic_delta_def one_arctic_delta_def)
  show "max x y = max y x" unfolding max_def
    by (cases x, (cases y, auto)+)
  show "max x y \<ge> x" unfolding max_def
    by (cases x, (cases y, auto)+)
  assume ge: "x \<ge> y" 
  from ge show "x + z \<ge> y + z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
  from ge show "x * z \<ge> y * z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
  from ge show "max x y = x" unfolding max_def
    by (cases x, (cases y, auto)+)
  from ge show "max z x \<ge> max z y" unfolding max_def
    by (cases z, cases x, auto, cases x, (cases y, auto)+)  
next
  fix x y z :: "'a arctic_delta"
  assume "x \<ge> y" and "y \<ge> z"
  thus "x \<ge> z"
    by (cases x, cases y, auto, cases y, cases z, auto, cases z, auto)
next
  fix x y z :: "'a arctic_delta"
  assume "y \<ge> z"
  thus "x * y \<ge> x * z"
    by (cases x, cases y, cases z, auto, cases y, cases z, auto, cases z, auto)
next
  fix x y z :: "'a arctic_delta"
  show "x \<ge> y \<Longrightarrow> 0 \<ge> z \<Longrightarrow> y * z \<ge> x * z"
    by (cases z, cases x, auto simp: zero_arctic_delta_def)
qed
end


text \<open>x >d y is interpreted as y = -inf or (x,y != -inf and x >d y)\<close>
fun gt_arctic_delta :: "'a :: floor_ceiling \<Rightarrow> 'a arctic_delta \<Rightarrow> 'a arctic_delta \<Rightarrow> bool"
where "gt_arctic_delta \<delta> _ MinInfty_delta = True"
   |  "gt_arctic_delta \<delta> MinInfty_delta (Num_arc_delta _) = False"
   |  "gt_arctic_delta \<delta> (Num_arc_delta x) (Num_arc_delta y) = delta_gt \<delta> x y"


fun get_arctic_delta_num :: "'a arctic_delta \<Rightarrow> 'a"
where "get_arctic_delta_num (Num_arc_delta n) = n"

fun pos_arctic_delta :: "('a :: floor_ceiling) arctic_delta \<Rightarrow> bool"
where "pos_arctic_delta MinInfty_delta = False"
    | "pos_arctic_delta (Num_arc_delta n) = (0 \<le> n)"

lemma arctic_delta_interpretation: assumes dpos: "\<delta> > 0" shows "SN_both_mono_ordered_semiring_1 1 (gt_arctic_delta \<delta>) pos_arctic_delta"
proof -
  from delta_interpretation[OF dpos] interpret SN_strict_mono_ordered_semiring_1 \<delta> "delta_gt \<delta>" delta_mono by simp
  show ?thesis 
  proof
    fix x y z :: "'a arctic_delta"
    assume "x \<ge> y" and "gt_arctic_delta \<delta> y z"
    thus "gt_arctic_delta \<delta> x z"
      by (cases z, simp, cases y, simp, cases x, simp, simp add: compat)
  next 
    fix x y z :: "'a arctic_delta"
    assume "gt_arctic_delta \<delta> x y" and "y \<ge> z"
    thus "gt_arctic_delta \<delta> x z"
      by (cases z, simp, cases y, simp, cases x, simp, simp add: compat2)
  next
    fix x y :: "'a arctic_delta"
    assume "gt_arctic_delta \<delta> x y" 
    thus "x \<ge> y"
      by (cases x, insert dpos, (cases y, auto simp: delta_gt_def)+)
  next
    fix x y z u
    assume "gt_arctic_delta \<delta> x y" and "gt_arctic_delta \<delta> z u"
    thus "gt_arctic_delta \<delta> (x + z) (y + u)"
      by (cases y, cases u, simp, cases z, simp, cases x, simp, simp add: delta_gt_def, 
        cases z, cases x, simp, cases u, simp, simp, cases x, simp, cases z, simp, cases u, simp add: delta_gt_def, simp add: delta_gt_def)
  next
    fix x y z
    assume "gt_arctic_delta \<delta> x y"
    thus "gt_arctic_delta \<delta> (x * z) (y * z)"
      by (cases y, simp, cases z, simp, cases x, simp, simp add: plus_gt_left_mono)
  next
    fix x
    assume "gt_arctic_delta \<delta> 0 x"
    thus "x = 0"
      by (cases x, auto simp: zero_arctic_delta_def)
  next
    fix x
    show "pos_arctic_delta 1" unfolding one_arctic_delta_def by simp
    show "gt_arctic_delta \<delta> x 0" unfolding zero_arctic_delta_def by simp
    show "(1 :: 'a arctic_delta) \<ge> 0" unfolding zero_arctic_delta_def by simp
    show "x \<ge> 0" unfolding zero_arctic_delta_def by simp
    show "\<not> pos_arctic_delta 0" unfolding zero_arctic_delta_def by simp
  next
    fix x y :: "'a arctic_delta"
    assume "pos_arctic_delta x" 
    thus "pos_arctic_delta (x + y)" by (cases x, simp, cases y, auto)
  next
    fix x y :: "'a arctic_delta"
    assume "pos_arctic_delta x" and "pos_arctic_delta y"
    thus "pos_arctic_delta (x * y)" by (cases x, simp, cases y, auto)
  next
    show "SN {(x,y). pos_arctic_delta y \<and> gt_arctic_delta \<delta> x y}" (is "SN ?rel")
    proof - {
      fix x
      assume "\<exists> f . f 0 = x \<and> (\<forall> i. (f i, f (Suc i)) \<in> ?rel)"
      from this obtain f where "f 0 = x" and seq: "\<forall> i. (f i, f (Suc i)) \<in> ?rel" by auto
      from seq have steps: "\<forall> i. gt_arctic_delta \<delta> (f i) (f (Suc i)) \<and> pos_arctic_delta (f (Suc i)) " by auto
      let ?g = "\<lambda> i. get_arctic_delta_num (f i)"
      have "\<forall> i. ?g (Suc i) \<ge> 0 \<and> delta_gt \<delta> (?g i) (?g (Suc i))"
      proof
        fix i
        from steps have i: "gt_arctic_delta \<delta> (f i) (f (Suc i)) \<and> pos_arctic_delta (f (Suc i))" by auto
        from i obtain n where fi: "f i = Num_arc_delta n" by (cases "f (Suc i)", simp, cases "f i", auto)
        from i obtain m where fsi: "f (Suc i) = Num_arc_delta m" by (cases "f (Suc i)", auto)
        with i have gz: "0 \<le> m" by simp
        from i fi fsi have "delta_gt \<delta> n m" by auto
        with fi fsi gz
        show "?g (Suc i) \<ge> 0 \<and> delta_gt \<delta> (?g i) (?g (Suc i))" by auto
      qed
      from this obtain g where "\<forall> i. g (Suc i) \<ge> 0 \<and> delta_gt \<delta> (g i) (g (Suc i))" by auto
      hence "\<exists> f. f 0 = g 0 \<and> (\<forall> i. (f i, f (Suc i)) \<in> {(x,y). y \<ge> 0 \<and> delta_gt \<delta> x y})" by auto
      with SN have False unfolding SN_defs by auto
    }
    thus ?thesis unfolding SN_defs by auto
    qed 
  next
    fix c d :: "'a arctic_delta"
    assume "pos_arctic_delta d" 
    then obtain n where d: "d = Num_arc_delta n" and n: "0 \<le> n"
      by (cases d, auto)  
    show "\<exists> e. e \<ge> 0 \<and> pos_arctic_delta e \<and> \<not> c \<ge> d * e"
    proof (cases c)
      case MinInfty_delta
      show ?thesis
        by (rule exI[of _ "Num_arc_delta 0"],
          unfold d MinInfty_delta zero_arctic_delta_def, simp)
    next
      case (Num_arc_delta m)
      show ?thesis
        by (rule exI[of _ "Num_arc_delta (abs m  + 1)"], insert n,
          unfold d Num_arc_delta zero_arctic_delta_def, simp)
    qed
  next
    fix x y z
    assume gt: "gt_arctic_delta \<delta> y z"
    {
      fix x y z
      assume gt: "delta_gt \<delta> y z"
      have "delta_gt \<delta> (x + y) (x + z)"
        using plus_gt_left_mono[OF gt] by (auto simp: field_simps)
    }
    with gt show "gt_arctic_delta \<delta> (x * y) (x * z)"
      by (cases x, simp, cases z, simp, cases y, simp_all)
  qed
qed

fun weak_gt_arctic_delta :: "('a :: floor_ceiling) arctic_delta \<Rightarrow> 'a arctic_delta \<Rightarrow> bool"
where "weak_gt_arctic_delta _ MinInfty_delta = True"
   |  "weak_gt_arctic_delta MinInfty_delta (Num_arc_delta _) = False"
   |  "weak_gt_arctic_delta (Num_arc_delta x) (Num_arc_delta y) = (x > y)"

interpretation weak_arctic_delta_SN: weak_SN_both_mono_ordered_semiring_1 weak_gt_arctic_delta 1 pos_arctic_delta
proof
  fix xys
  assume orient: "\<forall> x y. (x,y) \<in> set xys \<longrightarrow> weak_gt_arctic_delta x y"
  obtain xysp where xysp: "xysp = map (\<lambda> (ax, ay). (case ax of Num_arc_delta x \<Rightarrow> x , case ay of Num_arc_delta y \<Rightarrow> y)) (filter (\<lambda> (ax,ay). ax \<noteq> MinInfty_delta \<and> ay \<noteq> MinInfty_delta) xys)"
    (is "_ = map ?f _")
    by auto
  have "\<forall> x y. (x,y) \<in> set xysp \<longrightarrow> x > y" 
  proof (intro allI impI)
    fix x y
    assume "(x,y) \<in> set xysp"
    with xysp obtain ax ay where "(ax,ay) \<in> set xys" and "ax \<noteq> MinInfty_delta" and "ay \<noteq> MinInfty_delta" and "(x,y) = ?f (ax,ay)" by auto
    hence "(Num_arc_delta x, Num_arc_delta y) \<in> set xys" by (cases ax, simp, cases ay, auto)
    with orient show "x > y" by force
  qed
  with delta_minimal_delta[of xysp] obtain \<delta> where dpos: "\<delta> > 0" and orient2: "\<And> x y. (x, y) \<in> set xysp \<Longrightarrow> delta_gt \<delta> x y" by auto
  have orient: "\<forall> x y. (x,y) \<in> set xys \<longrightarrow> gt_arctic_delta \<delta> x y"
  proof(intro allI impI)
    fix ax ay
    assume axay: "(ax,ay) \<in> set xys"
    with orient have orient: "weak_gt_arctic_delta ax ay" by auto
    show "gt_arctic_delta \<delta> ax ay"
    proof (cases ay, simp)
      case (Num_arc_delta y) note ay = this
      show ?thesis
      proof (cases ax)
        case MinInfty_delta
        with ay orient show ?thesis by auto
      next
        case (Num_arc_delta x) note ax = this
        from ax ay axay have "(x,y) \<in> set xysp" unfolding xysp by force
        from ax ay orient2[OF this] show ?thesis by simp
      qed
    qed
  qed
  show "\<exists>gt. SN_both_mono_ordered_semiring_1 1 gt pos_arctic_delta \<and> (\<forall>x y. (x, y) \<in> set xys \<longrightarrow> gt x y)"
    by (intro exI conjI, rule arctic_delta_interpretation[OF dpos], rule orient)
qed  
    
end
