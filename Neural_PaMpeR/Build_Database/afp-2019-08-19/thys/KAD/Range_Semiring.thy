(* Title:      Range and Antirange Semirings
   Author:     Victor B. F. Gomes, Walter Guttmann, Peter Höfner, Georg Struth, Tjark Weber
   Maintainer: Walter Guttmann <walter.guttman at canterbury.ac.nz>
               Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Range and Antirange Semirings\<close>

theory Range_Semiring
imports Antidomain_Semiring
begin

subsection \<open>Range Semirings\<close>

text \<open>We set up the duality between domain and antidomain semirings on the one hand and range and antirange semirings on the other hand.\<close>

class range_op =
  fixes range_op :: "'a \<Rightarrow> 'a" ("r")

class range_semiring = semiring_one_zero + plus_ord + range_op +
  assumes rsr1 [simp]: "x + (x \<cdot> r x) = x \<cdot> r x"
  and rsr2 [simp]: "r (r x \<cdot> y) = r(x \<cdot> y)"
  and rsr3 [simp]: "r x + 1 = 1"
  and rsr4 [simp]: "r 0 = 0"
  and rsr5 [simp]: "r (x + y) = r x + r y"

begin

definition bd :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<langle>_| _" [61,81] 82) where
  "\<langle>x| y = r (y \<cdot> x)"

no_notation range_op ("r")

end

sublocale range_semiring \<subseteq> rdual: domain_semiring "(+)" "\<lambda>x y. y \<cdot> x" 1 0 range_op "(\<le>)" "(<)"
  rewrites "rdual.fd x y = \<langle>x| y"
proof -
  show "class.domain_semiring (+) (\<lambda>x y. y \<cdot> x) 1 0 range_op (\<le>) (<)"
    by (standard, auto simp: mult_assoc distrib_left)
  then interpret rdual: domain_semiring "(+)" "\<lambda>x y. y \<cdot> x" 1 0 range_op "(\<le>)" "(<)" .
  show "rdual.fd x y = \<langle>x| y"
    unfolding rdual.fd_def bd_def by auto
qed

sublocale domain_semiring \<subseteq> ddual: range_semiring "(+)" "\<lambda>x y. y \<cdot> x" 1 0 domain_op "(\<le>)" "(<)"
  rewrites "ddual.bd x y = domain_semiringl_class.fd x y"
proof -
  show "class.range_semiring (+) (\<lambda>x y. y \<cdot> x) 1 0 domain_op (\<le>) (<)"
    by (standard, auto simp: mult_assoc distrib_left)
  then interpret ddual: range_semiring "(+)" "\<lambda>x y. y \<cdot> x" 1 0 domain_op "(\<le>)" "(<)" .
  show "ddual.bd x y = domain_semiringl_class.fd x y"
    unfolding ddual.bd_def fd_def by auto
qed

subsection \<open>Antirange Semirings\<close>

class antirange_op =
  fixes antirange_op :: "'a \<Rightarrow> 'a" ("ar _" [999] 1000)

class antirange_semiring = semiring_one_zero + plus_ord + antirange_op +
  assumes ars1 [simp]: "x \<cdot> ar x = 0"
  and ars2 [simp]: "ar (x \<cdot> y) + ar (ar ar x \<cdot> y) = ar (ar ar x \<cdot> y)"
  and ars3 [simp]: "ar ar x + ar x = 1"

begin

no_notation bd ("\<langle>_| _" [61,81] 82)

definition ars_r :: "'a \<Rightarrow> 'a" ("r") where
  "r x = ar (ar x)"

definition bdia :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("\<langle>_| _" [61,81] 82) where
  "\<langle>x| y = ar ar (y \<cdot> x)"

definition bbox :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" ("[_| _" [61,81] 82) where
  "[x| y = ar (ar y \<cdot> x)"

end

sublocale antirange_semiring \<subseteq> ardual: antidomain_semiring antirange_op "(+)" "\<lambda>x y. y \<cdot> x" 1 0 "(\<le>)" "(<)"
  rewrites "ardual.ads_d x = r x"
  and "ardual.fdia x y = \<langle>x| y"
  and "ardual.fbox x y = [x| y"
proof -
  show "class.antidomain_semiring antirange_op (+) (\<lambda>x y. y \<cdot> x) 1 0 (\<le>) (<)"
    by (standard, auto simp: mult_assoc distrib_left)
  then interpret ardual: antidomain_semiring antirange_op "(+)" "\<lambda>x y. y \<cdot> x" 1 0 "(\<le>)" "(<)" .
  show "ardual.ads_d x = r x"
    by (simp add: ardual.ads_d_def local.ars_r_def)
  show "ardual.fdia x y = \<langle>x| y"
    unfolding ardual.fdia_def bdia_def by auto
  show "ardual.fbox x y = [x| y"
    unfolding ardual.fbox_def bbox_def by auto
qed

context antirange_semiring

begin

sublocale rs: range_semiring "(+)" "(\<cdot>)" 1 0 "\<lambda>x. ar ar x" "(\<le>)" "(<)"
  by unfold_locales

end

sublocale antidomain_semiring \<subseteq> addual: antirange_semiring "(+)" "\<lambda>x y. y \<cdot> x" 1 0 antidomain_op "(\<le>)" "(<)"
  rewrites "addual.ars_r x = d x"
  and "addual.bdia x y = |x\<rangle> y"
  and "addual.bbox x y = |x] y"
proof -
  show "class.antirange_semiring (+) (\<lambda>x y. y \<cdot> x) 1 0 antidomain_op (\<le>) (<)"
    by (standard, auto simp: mult_assoc distrib_left)
  then interpret addual: antirange_semiring "(+)" "\<lambda>x y. y \<cdot> x" 1 0 antidomain_op "(\<le>)" "(<)" .
  show "addual.ars_r x = d x"
    by (simp add: addual.ars_r_def local.ads_d_def)
  show "addual.bdia x y = |x\<rangle> y"
    unfolding addual.bdia_def fdia_def by auto
  show "addual.bbox x y = |x] y"
    unfolding addual.bbox_def fbox_def by auto
qed

subsection \<open>Antirange Kleene Algebras\<close>

class antirange_kleene_algebra = antirange_semiring + kleene_algebra

sublocale antirange_kleene_algebra \<subseteq> dual: antidomain_kleene_algebra antirange_op "(+)" "\<lambda>x y. y \<cdot> x" 1 0 "(\<le>)" "(<)" "star"
  by (standard, auto simp: local.star_inductr' local.star_inductl)


sublocale antidomain_kleene_algebra \<subseteq> dual: antirange_kleene_algebra "(+)" "\<lambda>x y. y \<cdot> x" 1 0 "(\<le>)" "(<)" "star" antidomain_op
  by (standard, simp_all add: star_inductr star_inductl)

text \<open>Hence all range theorems have been derived by duality in a generic way.\<close>

end
