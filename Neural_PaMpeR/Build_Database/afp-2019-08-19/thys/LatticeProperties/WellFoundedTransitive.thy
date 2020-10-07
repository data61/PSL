section \<open>Well founded and transitive relations\<close>

theory WellFoundedTransitive
imports Main
begin

class transitive = ord +
  assumes order_trans1: "x < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  and less_eq_def: "x \<le> y \<longleftrightarrow> x = y \<or> x < y"
begin

lemma eq_less_eq [simp]:
  "x = y \<Longrightarrow> x \<le> y"
  by (simp add: less_eq_def)

lemma order_trans2 [simp]:
  "x \<le> y \<Longrightarrow> y < z \<Longrightarrow> x < z"
  apply (simp add: less_eq_def)
  apply auto
  apply (erule less_eq_def order_trans1)
  by assumption

lemma order_trans3:
  "x < y \<Longrightarrow> y \<le> z \<Longrightarrow> x < z"
  apply (simp add: less_eq_def)
  apply auto
  apply (erule less_eq_def order_trans1)
  by assumption
end

class well_founded = ord +
  assumes less_induct1 [case_names less]: "(!!x . (!!y . y < x \<Longrightarrow> P y) \<Longrightarrow> P x) \<Longrightarrow> P a"

class well_founded_transitive = transitive + well_founded

instantiation prod:: (ord, ord) ord
begin

definition
  less_pair_def: "a < b \<longleftrightarrow>  fst a  < fst b \<or> (fst a = fst b \<and> snd a < snd b)"

definition
  less_eq_pair_def: "(a::('a::ord * 'b::ord)) <= b \<longleftrightarrow> a = b \<or> a < b"
instance proof qed
end

instantiation prod:: (transitive, transitive) transitive
begin
instance proof
  fix x y z :: "('a::transitive * 'b::transitive)"
  assume "x < y" and "y < z" then  show  "x < z"
    apply (simp add: less_pair_def)
    apply auto
    apply (drule  order_trans1)
    apply auto
    apply (drule  order_trans1)
    apply auto
    apply (drule  order_trans1)
    apply auto
    done
next
  fix x y :: "'a * 'b"
  show  "x \<le> y \<longleftrightarrow> x = y \<or> x < y"
    by (simp add: less_eq_pair_def)
qed
end

instantiation prod:: (well_founded, well_founded) well_founded
begin
instance proof
  fix P::"('a * 'b) \<Rightarrow> bool"
  have a:  "\<forall>P. (\<forall>x::'a . (\<forall>y. y < x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>a . P a)"
    apply safe
    apply (rule less_induct1)
    by blast
  have b:  "\<forall>P. (\<forall>x::'b. (\<forall>y . y < x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>a . P a)"
    apply safe
    apply (rule less_induct1)
    by blast
  from a and b have c: "(\<forall>x. (\<forall>y. y < x \<longrightarrow> P y) \<longrightarrow> P x) \<longrightarrow> (\<forall>a. P a)"
    apply (unfold less_pair_def)
    apply (rule impI)
    apply (simp (no_asm_use) only: split_paired_All)
    apply (unfold fst_conv snd_conv)
    apply (drule spec)
    apply (erule mp)
    apply (rule allI)
    apply (rule impI)
    apply (drule spec)
    apply (erule mp)
    by blast
  assume A: "(!! x. (!! y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x)"
  fix a
  from c A show "P a" by blast
qed
end

instantiation prod:: (well_founded_transitive, well_founded_transitive) well_founded_transitive
begin
instance proof qed
end

instantiation "nat" :: transitive
begin

instance proof
  fix x y z::nat
  assume "x < y" and "y < z" then show "x < z" by simp
  next
  fix x y::nat show "(x \<le> y) \<longleftrightarrow> (x = y \<or> x < y)"
    apply (unfold le_less)
    by safe
  qed
end

instantiation "nat":: well_founded
begin
instance proof
  fix P::"nat \<Rightarrow> bool" 
  fix a
  assume A: "(\<And>x . (\<And>y . y < x \<Longrightarrow> P y) \<Longrightarrow> P x)"
  show "P a"
  by (rule less_induct, rule A, simp)
  qed
end

instantiation "nat":: well_founded_transitive
begin
instance proof qed
end

end
