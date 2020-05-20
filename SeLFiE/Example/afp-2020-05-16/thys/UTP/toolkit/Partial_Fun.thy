(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Partial_Fun.thy                                                      *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Partial Functions \<close>

theory Partial_Fun
imports "Optics.Lenses" Map_Extra
begin

text \<open> I'm not completely satisfied with partial functions as provided by Map.thy, since they don't
        have a unique type and so we can't instantiate classes, make use of adhoc-overloading
        etc. Consequently I've created a new type and derived the laws. \<close>

subsection \<open> Partial function type and operations \<close>

typedef ('a, 'b) pfun = "UNIV :: ('a \<rightharpoonup> 'b) set" ..

setup_lifting type_definition_pfun

lift_definition pfun_app :: "('a, 'b) pfun \<Rightarrow> 'a \<Rightarrow> 'b" ("_'(_')\<^sub>p" [999,0] 999) is 
"\<lambda> f x. if (x \<in> dom f) then the (f x) else undefined" .

lift_definition pfun_upd :: "('a, 'b) pfun \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) pfun"
is "\<lambda> f k v. f(k := Some v)" .

lift_definition pdom :: "('a, 'b) pfun \<Rightarrow> 'a set" is dom .

lift_definition pran :: "('a, 'b) pfun \<Rightarrow> 'b set" is ran .

lift_definition pfun_comp :: "('b, 'c) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'c) pfun" (infixl "\<circ>\<^sub>p" 55) is map_comp .

lift_definition pfun_member :: "'a \<times> 'b \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" (infix "\<in>\<^sub>p" 50) is "(\<in>\<^sub>m)" .

lift_definition pId_on :: "'a set \<Rightarrow> ('a, 'a) pfun" is "\<lambda> A x. if (x \<in> A) then Some x else None" .

abbreviation pId :: "('a, 'a) pfun" where
"pId \<equiv> pId_on UNIV"

lift_definition plambda :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) pfun"
is "\<lambda> P f x. if (P x) then Some (f x) else None" .

lift_definition pdom_res :: "'a set \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" (infixl "\<lhd>\<^sub>p" 85)
is "\<lambda> A f. restrict_map f A" .

lift_definition pran_res :: "('a, 'b) pfun \<Rightarrow> 'b set \<Rightarrow> ('a, 'b) pfun" (infixl "\<rhd>\<^sub>p" 85)
is ran_restrict_map .

lift_definition pfun_graph :: "('a, 'b) pfun \<Rightarrow> ('a \<times> 'b) set" is map_graph .

lift_definition graph_pfun :: "('a \<times> 'b) set \<Rightarrow> ('a, 'b) pfun" is graph_map .

lift_definition pfun_entries :: "'k set \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> ('k, 'v) pfun" is
"\<lambda> d f x. if (x \<in> d) then Some (f x) else None" .
    
definition pcard :: "('a, 'b) pfun \<Rightarrow> nat"
where "pcard f = card (pdom f)"

instantiation pfun :: (type, type) zero
begin
lift_definition zero_pfun :: "('a, 'b) pfun" is "Map.empty" .
instance ..
end

abbreviation pempty :: "('a, 'b) pfun" ("{}\<^sub>p")
where "pempty \<equiv> 0"

instantiation pfun :: (type, type) plus
begin
lift_definition plus_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" is "(++)" .
instance ..
end

instantiation pfun :: (type, type) minus
begin
lift_definition minus_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" is "(--)" .
instance ..
end

instance pfun :: (type, type) monoid_add
  by (intro_classes, (transfer, auto)+)

instantiation pfun :: (type, type) inf
begin
lift_definition inf_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" is
"\<lambda> f g x. if (x \<in> dom(f) \<inter> dom(g) \<and> f(x) = g(x)) then f(x) else None" .
instance ..
end

abbreviation pfun_inter :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun" (infixl "\<inter>\<^sub>p" 80)
where "pfun_inter \<equiv> inf"

instantiation pfun :: (type, type) order
begin
  lift_definition less_eq_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" is
  "\<lambda> f g. f \<subseteq>\<^sub>m g" .
  lift_definition less_pfun :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" is
  "\<lambda> f g. f \<subseteq>\<^sub>m g \<and> f \<noteq> g" .
instance
  by (intro_classes, (transfer, auto intro: map_le_trans simp add: map_le_antisym)+)
end

abbreviation pfun_subset :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" (infix "\<subset>\<^sub>p" 50)
where "pfun_subset \<equiv> less"

abbreviation pfun_subset_eq :: "('a, 'b) pfun \<Rightarrow> ('a, 'b) pfun \<Rightarrow> bool" (infix "\<subseteq>\<^sub>p" 50)
where "pfun_subset_eq \<equiv> less_eq"

instance pfun :: (type, type) semilattice_inf
  by (intro_classes, (transfer, auto simp add: map_le_def dom_def)+)

lemma pfun_subset_eq_least [simp]:
  "{}\<^sub>p \<subseteq>\<^sub>p f"
  by (transfer, auto)

syntax
  "_PfunUpd"  :: "[('a, 'b) pfun, maplets] => ('a, 'b) pfun" ("_'(_')\<^sub>p" [900,0]900)
  "_Pfun"     :: "maplets => ('a, 'b) pfun"            ("(1{_}\<^sub>p)")
  "_plam"     :: "pttrn \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" ("\<lambda> _ | _ . _" [0,0,10] 10)

translations
  "_PfunUpd m (_Maplets xy ms)"  == "_PfunUpd (_PfunUpd m xy) ms"
  "_PfunUpd m (_maplet  x y)"    == "CONST pfun_upd m x y"
  "_Pfun ms"                     => "_PfunUpd (CONST pempty) ms"
  "_Pfun (_Maplets ms1 ms2)"     <= "_PfunUpd (_Pfun ms1) ms2"
  "_Pfun ms"                     <= "_PfunUpd (CONST pempty) ms"
  "\<lambda> x | P . e"                  => "CONST plambda (\<lambda> x. P) (\<lambda> x. e)"
  "\<lambda> x | P . e"                  <= "CONST plambda (\<lambda> x. P) (\<lambda> y. e)"
  "\<lambda> y | P . e"                  <= "CONST plambda (\<lambda> x. P) (\<lambda> y. e)"
  "\<lambda> y | f v y . e"              <= "CONST plambda (f v) (\<lambda> y. e)"

subsection \<open> Algebraic laws \<close>

lemma pfun_comp_assoc: "f \<circ>\<^sub>p (g \<circ>\<^sub>p h) = (f \<circ>\<^sub>p g) \<circ>\<^sub>p h"
  by (transfer, simp add: map_comp_assoc)

lemma pfun_comp_left_id [simp]: "pId \<circ>\<^sub>p f = f"
  by (transfer, auto)

lemma pfun_comp_right_id [simp]: "f \<circ>\<^sub>p pId = f"
  by (transfer, auto)

lemma pfun_override_dist_comp:
  "(f + g) \<circ>\<^sub>p h = (f \<circ>\<^sub>p h) + (g \<circ>\<^sub>p h)"
  apply (transfer)
  apply (rule ext)
  apply (auto simp add: map_add_def)
  apply (rename_tac f g h x)
  apply (case_tac "h x")
   apply (auto)
  apply (rename_tac f g h x y)
  apply (case_tac "g y")
   apply (auto)
  done

lemma pfun_minus_unit [simp]:
  fixes f :: "('a, 'b) pfun"
  shows "f - 0 = f"
  by (transfer, simp add: map_minus_def)

lemma pfun_minus_zero [simp]:
  fixes f :: "('a, 'b) pfun"
  shows "0 - f = 0"
  by (transfer, simp add: map_minus_def)

lemma pfun_minus_self [simp]:
  fixes f :: "('a, 'b) pfun"
  shows "f - f = 0"
  by (transfer, simp add: map_minus_def)

lemma pfun_plus_commute:
  "pdom(f) \<inter> pdom(g) = {} \<Longrightarrow> f + g = g + f"
  by (transfer, metis map_add_comm)

lemma pfun_plus_commute_weak:
  "(\<forall> k \<in> pdom(f) \<inter> pdom(g). f(k)\<^sub>p = g(k)\<^sub>p) \<Longrightarrow> f + g = g + f"
  by (transfer, simp, metis IntD1 IntD2 domD map_add_comm_weak option.sel)

lemma pfun_minus_plus_commute:
  "pdom(g) \<inter> pdom(h) = {} \<Longrightarrow> (f - g) + h = (f + h) - g"
  by (transfer, simp add: map_minus_plus_commute)

lemma pfun_plus_minus:
  "f \<subseteq>\<^sub>p g \<Longrightarrow> (g - f) + f = g"
  by (transfer, rule ext, auto simp add: map_le_def map_minus_def map_add_def option.case_eq_if)

lemma pfun_minus_common_subset:
  "\<lbrakk> h \<subseteq>\<^sub>p f; h \<subseteq>\<^sub>p g \<rbrakk> \<Longrightarrow> (f - h = g - h) = (f = g)"
  by (transfer, simp add: map_minus_common_subset)

lemma pfun_minus_plus:
  "pdom(f) \<inter> pdom(g) = {} \<Longrightarrow> (f + g) - g = f"
  by (transfer, simp add: map_add_def map_minus_def option.case_eq_if, rule ext, auto)
     (metis Int_commute domIff insert_disjoint(1) insert_dom)

lemma pfun_plus_pos: "x + y = {}\<^sub>p \<Longrightarrow> x = {}\<^sub>p"
  by (transfer, simp)

lemma pfun_le_plus: "pdom x \<inter> pdom y = {} \<Longrightarrow> x \<le> x + y"
  by (transfer, auto simp add: map_le_iff_add)

subsection \<open> Lambda abstraction \<close>

lemma plambda_app [simp]: "(\<lambda> x | P x . f x)(v)\<^sub>p = (if (P v) then (f v) else undefined)"
  by (transfer, auto)

lemma plambda_eta [simp]: "(\<lambda> x | x \<in> pdom(f). f(x)\<^sub>p) = f"
  by (transfer; auto simp add: domIff)

lemma plambda_id [simp]: "(\<lambda> x | P x . x) = pId_on {x. P x}"
  by (transfer, simp)

subsection \<open> Membership, application, and update \<close>

lemma pfun_ext: "\<lbrakk> \<And> x y. (x, y) \<in>\<^sub>p f \<longleftrightarrow> (x, y) \<in>\<^sub>p g \<rbrakk> \<Longrightarrow> f = g"
  by (transfer, simp add: map_ext)

lemma pfun_member_alt_def:
  "(x, y) \<in>\<^sub>p f \<longleftrightarrow> (x \<in> pdom f \<and> f(x)\<^sub>p = y)"
  by (transfer, auto simp add: map_member_alt_def map_apply_def)

lemma pfun_member_plus:
  "(x, y) \<in>\<^sub>p f + g \<longleftrightarrow> ((x \<notin> pdom(g) \<and> (x, y) \<in>\<^sub>p f) \<or> (x, y) \<in>\<^sub>p g)"
  by (transfer, simp add: map_member_plus)

lemma pfun_member_minus:
  "(x, y) \<in>\<^sub>p f - g \<longleftrightarrow> (x, y) \<in>\<^sub>p f \<and> (\<not> (x, y) \<in>\<^sub>p g)"
  by (transfer, simp add: map_member_minus)

lemma pfun_app_upd_1 [simp]: "x = y \<Longrightarrow> (f(x \<mapsto> v)\<^sub>p)(y)\<^sub>p = v"
  by (transfer, simp)

lemma pfun_app_upd_2 [simp]: "x \<noteq> y \<Longrightarrow> (f(x \<mapsto> v)\<^sub>p)(y)\<^sub>p = f(y)\<^sub>p"
  by (transfer, simp)

lemma pfun_upd_ext [simp]: "x \<in> pdom(f) \<Longrightarrow> f(x \<mapsto> f(x)\<^sub>p)\<^sub>p = f"
  by (transfer, simp add: domIff)

lemma pfun_app_add [simp]: "x \<in> pdom(g) \<Longrightarrow> (f + g)(x)\<^sub>p = g(x)\<^sub>p"
  by (transfer, auto)

lemma pfun_upd_add [simp]: "f + g(x \<mapsto> v)\<^sub>p = (f + g)(x \<mapsto> v)\<^sub>p"
  by (transfer, simp)

lemma pfun_upd_twice [simp]: "f(x \<mapsto> u, x \<mapsto> v)\<^sub>p = f(x \<mapsto> v)\<^sub>p"
  by (transfer, simp)

lemma pfun_upd_comm:
  assumes "x \<noteq> y"
  shows "f(y \<mapsto> u, x \<mapsto> v)\<^sub>p = f(x \<mapsto> v, y \<mapsto> u)\<^sub>p"
  using assms by (transfer, auto)

lemma pfun_upd_comm_linorder [simp]:
  fixes x y :: "'a :: linorder"
  assumes "x < y"
  shows "f(y \<mapsto> u, x \<mapsto> v)\<^sub>p = f(x \<mapsto> v, y \<mapsto> u)\<^sub>p"
  using assms by (transfer, auto)

lemma pfun_app_minus [simp]: "x \<notin> pdom g \<Longrightarrow> (f - g)(x)\<^sub>p = f(x)\<^sub>p"
  by (transfer, auto simp add: map_minus_def)

lemma pfun_app_empty [simp]: "{}\<^sub>p(x)\<^sub>p = undefined"
  by (transfer, simp)

lemma pfun_app_not_in_dom: 
  "x \<notin> pdom(f) \<Longrightarrow> f(x)\<^sub>p = undefined"
  by (transfer, simp)

lemma pfun_upd_minus [simp]:
  "x \<notin> pdom g \<Longrightarrow> (f - g)(x \<mapsto> v)\<^sub>p = (f(x \<mapsto> v)\<^sub>p - g)"
  by (transfer, auto simp add: map_minus_def)

lemma pdom_member_minus_iff [simp]:
  "x \<notin> pdom g \<Longrightarrow> x \<in> pdom(f - g) \<longleftrightarrow> x \<in> pdom(f)"
  by (transfer, simp add: domIff map_minus_def)

lemma psubseteq_pfun_upd1 [intro]:
  "\<lbrakk> f \<subseteq>\<^sub>p g; x \<notin> pdom(g) \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>p g(x \<mapsto> v)\<^sub>p"
  by (transfer, auto simp add: map_le_def dom_def)

lemma psubseteq_pfun_upd2 [intro]:
  "\<lbrakk> f \<subseteq>\<^sub>p g; x \<notin> pdom(f) \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>p g(x \<mapsto> v)\<^sub>p"
  by (transfer, auto simp add: map_le_def dom_def)

lemma psubseteq_pfun_upd3 [intro]:
  "\<lbrakk> f \<subseteq>\<^sub>p g; g(x)\<^sub>p = v \<rbrakk> \<Longrightarrow> f \<subseteq>\<^sub>p g(x \<mapsto> v)\<^sub>p"
  by (transfer, auto simp add: map_le_def dom_def)

lemma psubseteq_dom_subset:
  "f \<subseteq>\<^sub>p g \<Longrightarrow> pdom(f) \<subseteq> pdom(g)"
  by (transfer, auto simp add: map_le_def dom_def)

lemma psubseteq_ran_subset:
  "f \<subseteq>\<^sub>p g \<Longrightarrow> pran(f) \<subseteq> pran(g)"
  by (transfer, auto simp add: map_le_def dom_def ran_def, fastforce)

subsection \<open> Domain laws \<close>

lemma pdom_zero [simp]: "pdom 0 = {}"
  by (transfer, simp)

lemma pdom_pId_on [simp]: "pdom (pId_on A) = A"
  by (transfer, auto)

lemma pdom_plus [simp]: "pdom (f + g) = pdom f \<union> pdom g"
  by (transfer, auto)

lemma pdom_minus [simp]: "g \<le> f \<Longrightarrow> pdom (f - g) = pdom f - pdom g"
  apply (transfer, auto simp add: map_minus_def)
  apply (meson option.distinct(1))
  apply (metis domIff map_le_def option.simps(3))
  done

lemma pdom_inter: "pdom (f \<inter>\<^sub>p g) \<subseteq> pdom f \<inter> pdom g"
  by (transfer, auto simp add: dom_def)

lemma pdom_comp [simp]: "pdom (g \<circ>\<^sub>p f) = pdom (f \<rhd>\<^sub>p pdom g)"
  by (transfer, auto simp add: ran_restrict_map_def)

lemma pdom_upd [simp]: "pdom (f(k \<mapsto> v)\<^sub>p) = insert k (pdom f)"
  by (transfer, simp)

lemma pdom_plamda [simp]: "pdom (\<lambda> x | P x . f x) = {x. P x}"
  by (transfer, auto)

lemma pdom_pdom_res [simp]: "pdom (A \<lhd>\<^sub>p f) = A \<inter> pdom(f)"
  by (transfer, auto)

lemma pdom_graph_pfun [simp]: "pdom (graph_pfun R) = Domain R"
  by (transfer, simp add: Domain_fst graph_map_dom)

lemma pdom_pran_res_finite [simp]:
  "finite (pdom f) \<Longrightarrow> finite (pdom (f \<rhd>\<^sub>p A))"
  by (transfer, auto)

lemma pdom_pfun_graph_finite [simp]:
  "finite (pdom f) \<Longrightarrow> finite (pfun_graph f)"
  by (transfer, simp add: finite_dom_graph)

subsection \<open> Range laws \<close>

lemma pran_zero [simp]: "pran 0 = {}"
  by (transfer, simp)

lemma pran_pId_on [simp]: "pran (pId_on A) = A"
  by (transfer, auto simp add: ran_def)

lemma pran_upd [simp]: "pran (f(k \<mapsto> v)\<^sub>p) = insert v (pran ((- {k}) \<lhd>\<^sub>p f))"
  by (transfer, auto simp add: ran_def restrict_map_def)

lemma pran_plamda [simp]: "pran (\<lambda> x | P x . f x) = {f x | x. P x}"
  by (transfer, auto simp add: ran_def)

lemma pran_pran_res [simp]: "pran (f \<rhd>\<^sub>p A) = pran(f) \<inter> A"
  by (transfer, auto)

lemma pran_comp [simp]: "pran (g \<circ>\<^sub>p f) = pran (pran f \<lhd>\<^sub>p g)"
  by (transfer, auto simp add: ran_def restrict_map_def)

lemma pran_finite [simp]: "finite (pdom f) \<Longrightarrow> finite (pran f)"
  by (transfer, auto)

subsection \<open> Domain restriction laws \<close>

lemma pdom_res_zero [simp]: "A \<lhd>\<^sub>p {}\<^sub>p = {}\<^sub>p"
  by (transfer, auto)

lemma pdom_res_empty [simp]:
  "({} \<lhd>\<^sub>p f) = {}\<^sub>p"
  by (transfer, auto)

lemma pdom_res_pdom [simp]:
  "pdom(f) \<lhd>\<^sub>p f = f"
  by (transfer, auto)

lemma pdom_res_UNIV [simp]: "UNIV \<lhd>\<^sub>p f = f"
  by (transfer, auto)
    
lemma pdom_res_alt_def: "A \<lhd>\<^sub>p f =  f \<circ>\<^sub>p pId_on A"
  by (transfer, rule ext, auto simp add: restrict_map_def)

lemma pdom_res_upd_in [simp]:
  "k \<in> A \<Longrightarrow> A \<lhd>\<^sub>p f(k \<mapsto> v)\<^sub>p = (A \<lhd>\<^sub>p f)(k \<mapsto> v)\<^sub>p"
  by (transfer, auto)

lemma pdom_res_upd_out [simp]:
  "k \<notin> A \<Longrightarrow> A \<lhd>\<^sub>p f(k \<mapsto> v)\<^sub>p = A \<lhd>\<^sub>p f"
  by (transfer, auto)
    
lemma pfun_pdom_antires_upd [simp]:
  "k \<in> A \<Longrightarrow> ((- A) \<lhd>\<^sub>p m)(k \<mapsto> v)\<^sub>p =  ((- (A - {k})) \<lhd>\<^sub>p m)(k \<mapsto> v)\<^sub>p"
  by (transfer, simp)

lemma pdom_antires_insert_notin [simp]:
  "k \<notin> pdom(f) \<Longrightarrow> (- insert k A) \<lhd>\<^sub>p f = (- A) \<lhd>\<^sub>p f"
  by (transfer, auto simp add: restrict_map_def)
 
lemma pdom_res_override [simp]: "A \<lhd>\<^sub>p (f + g) = (A \<lhd>\<^sub>p f) + (A \<lhd>\<^sub>p g)"
  by (simp add: pdom_res_alt_def pfun_override_dist_comp)

lemma pdom_res_minus [simp]: "A \<lhd>\<^sub>p (f - g) = (A \<lhd>\<^sub>p f) - g"
  by (transfer, auto simp add: map_minus_def restrict_map_def)

lemma pdom_res_swap: "(A \<lhd>\<^sub>p f) \<rhd>\<^sub>p B = A \<lhd>\<^sub>p (f \<rhd>\<^sub>p B)"
  by (transfer, auto simp add: restrict_map_def ran_restrict_map_def)

lemma pdom_res_twice [simp]: "A \<lhd>\<^sub>p (B \<lhd>\<^sub>p f) = (A \<inter> B) \<lhd>\<^sub>p f"
  by (transfer, auto simp add: Int_commute)

lemma pdom_res_comp [simp]: "A \<lhd>\<^sub>p (g \<circ>\<^sub>p f) =  g \<circ>\<^sub>p (A \<lhd>\<^sub>p f)"
  by (simp add: pdom_res_alt_def pfun_comp_assoc)

lemma pdom_res_apply [simp]:
  "x \<in> A \<Longrightarrow> (A \<lhd>\<^sub>p f)(x)\<^sub>p = f(x)\<^sub>p"
  by (transfer, auto)
    
subsection \<open> Range restriction laws \<close>

lemma pran_res_zero [simp]: "{}\<^sub>p \<rhd>\<^sub>p A = {}\<^sub>p"
  by (transfer, auto simp add: ran_restrict_map_def)

lemma pran_res_upd_1 [simp]: "v \<in> A \<Longrightarrow> f(x \<mapsto> v)\<^sub>p \<rhd>\<^sub>p A = (f \<rhd>\<^sub>p A)(x \<mapsto> v)\<^sub>p"
  by (transfer, auto simp add: ran_restrict_map_def)

lemma pran_res_upd_2 [simp]: "v \<notin> A \<Longrightarrow> f(x \<mapsto> v)\<^sub>p \<rhd>\<^sub>p A = ((- {x}) \<lhd>\<^sub>p f) \<rhd>\<^sub>p A"
  by (transfer, auto simp add: ran_restrict_map_def)

lemma pran_res_alt_def: "f \<rhd>\<^sub>p A = pId_on A \<circ>\<^sub>p f"
  by (transfer, rule ext, auto simp add: ran_restrict_map_def)

lemma pran_res_override: "(f + g) \<rhd>\<^sub>p A \<subseteq>\<^sub>p (f \<rhd>\<^sub>p A) + (g \<rhd>\<^sub>p A)"
  apply (transfer, auto simp add: map_add_def ran_restrict_map_def map_le_def)
  apply (rename_tac f g A a y x)
  apply (case_tac "g a")
   apply (auto)
  done

subsection \<open> Graph laws \<close>

lemma pfun_graph_inv: "graph_pfun (pfun_graph f) = f"
  by (transfer, simp)

lemma pfun_graph_zero: "pfun_graph 0 = {}"
  by (transfer, simp add: map_graph_def)

lemma pfun_graph_pId_on: "pfun_graph (pId_on A) = Id_on A"
  by (transfer, auto simp add: map_graph_def)

lemma pfun_graph_minus: "pfun_graph (f - g) = pfun_graph f - pfun_graph g"
  by (transfer, simp add: map_graph_minus)

lemma pfun_graph_inter: "pfun_graph (f \<inter>\<^sub>p g) = pfun_graph f \<inter> pfun_graph g"
  apply (transfer, auto simp add: map_graph_def)
   apply (metis option.discI)+
  done

subsection \<open> Entries \<close>
  
lemma pfun_entries_empty [simp]: "pfun_entries {} f = {}\<^sub>p"
  by (transfer, simp)

lemma pfun_entries_apply_1 [simp]: 
  "x \<in> d \<Longrightarrow> (pfun_entries d f)(x)\<^sub>p = f x"
  by (transfer, auto)

lemma pfun_entries_apply_2 [simp]: 
  "x \<notin> d \<Longrightarrow> (pfun_entries d f)(x)\<^sub>p = undefined"
  by (transfer, auto)

subsection \<open> Summation \<close>
    
definition pfun_sum :: "('k, 'v::comm_monoid_add) pfun \<Rightarrow> 'v" where
"pfun_sum f = sum (pfun_app f) (pdom f)"
    
lemma pfun_sum_empty [simp]: "pfun_sum {}\<^sub>p = 0"
  by (simp add: pfun_sum_def)

lemma pfun_sum_upd_1:
  assumes "finite(pdom(m))" "k \<notin> pdom(m)"
  shows "pfun_sum (m(k \<mapsto> v)\<^sub>p) = pfun_sum m + v"
  by (simp_all add: pfun_sum_def assms, metis add.commute assms(2) pfun_app_upd_2 sum.cong)

lemma pfun_sums_upd_2:
  assumes "finite(pdom(m))"
  shows "pfun_sum (m(k \<mapsto> v)\<^sub>p) = pfun_sum ((- {k}) \<lhd>\<^sub>p m) + v"
proof (cases "k \<notin> pdom(m)")
  case True
  then show ?thesis 
    by (simp add: pfun_sum_upd_1 assms)
next
  case False
  then show ?thesis
    using assms pfun_sum_upd_1[of "((- {k}) \<lhd>\<^sub>p m)" k v]
    by (simp add: pfun_sum_upd_1)
qed

lemma pfun_sum_dom_res_insert [simp]: 
  assumes "x \<in> pdom f" "x \<notin> A" "finite A" 
  shows "pfun_sum ((insert x A) \<lhd>\<^sub>p f) = f(x)\<^sub>p + pfun_sum (A \<lhd>\<^sub>p f)"
  using assms by (simp add: pfun_sum_def)
  
lemma pfun_sum_pdom_res:
  fixes f :: "('a,'b::ab_group_add) pfun"
  assumes "finite(pdom f)"
  shows "pfun_sum (A \<lhd>\<^sub>p f) = pfun_sum f - (pfun_sum ((- A) \<lhd>\<^sub>p f))"
proof -
  have 1:"A \<inter> pdom(f) = pdom(f) - (pdom(f) - A)"
    by (auto)
  show ?thesis
    apply (simp add: pfun_sum_def)
    apply (subst 1)
    apply (subst sum_diff)
      apply (auto simp add: sum_diff Diff_subset Int_commute boolean_algebra_class.diff_eq assms)
    done
qed
  
lemma pfun_sum_pdom_antires [simp]:
  fixes f :: "('a,'b::ab_group_add) pfun"
  assumes "finite(pdom f)"
  shows "pfun_sum ((- A) \<lhd>\<^sub>p f) = pfun_sum f - pfun_sum (A \<lhd>\<^sub>p f)"
  by (subst pfun_sum_pdom_res, simp_all add: assms)

subsection \<open> Partial Function Lens \<close>

definition pfun_lens :: "'a \<Rightarrow> ('b \<Longrightarrow> ('a, 'b) pfun)" where
[lens_defs]: "pfun_lens i = \<lparr> lens_get = \<lambda> s. s(i)\<^sub>p, lens_put = \<lambda> s v. s(i \<mapsto> v)\<^sub>p \<rparr>"

lemma pfun_lens_mwb [simp]: "mwb_lens (pfun_lens i)"
  by (unfold_locales, simp_all add: pfun_lens_def)

lemma pfun_lens_src: "\<S>\<^bsub>pfun_lens i\<^esub> = {f. i \<in> pdom(f)}"
  by (auto simp add: lens_defs lens_source_def, transfer, force)

text \<open> Hide implementation details for partial functions \<close>

lifting_update pfun.lifting
lifting_forget pfun.lifting

end