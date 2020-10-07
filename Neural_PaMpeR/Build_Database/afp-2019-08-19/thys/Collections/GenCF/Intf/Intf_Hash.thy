section \<open>\isaheader{Hashable Interface}\<close>
theory Intf_Hash
imports 
    Main
    "../../Lib/HashCode"
    "../../Lib/Code_Target_ICF"
    Automatic_Refinement.Automatic_Refinement
begin

type_synonym 'a eq = "'a \<Rightarrow> 'a \<Rightarrow> bool"
type_synonym 'k bhc = "nat \<Rightarrow> 'k \<Rightarrow> nat"

subsection \<open>Abstract and concrete hash functions\<close>

definition is_bounded_hashcode :: "('c\<times>'a) set \<Rightarrow> 'c eq \<Rightarrow> 'c bhc \<Rightarrow> bool"
  where "is_bounded_hashcode R eq bhc \<equiv> 
             ((eq,(=)) \<in> R \<rightarrow> R \<rightarrow> bool_rel) \<and>
             (\<forall>n. \<forall> x \<in> Domain R. \<forall> y \<in> Domain R. eq x y \<longrightarrow> bhc n x = bhc n y) \<and>
             (\<forall>n x. 1 < n \<longrightarrow> bhc n x < n)"
definition abstract_bounded_hashcode :: "('c\<times>'a) set \<Rightarrow> 'c bhc \<Rightarrow> 'a bhc"
  where "abstract_bounded_hashcode Rk bhc n x' \<equiv> 
             if x' \<in> Range Rk 
                 then THE c. \<exists>x. (x,x') \<in> Rk \<and> bhc n x = c
                 else 0"

lemma is_bounded_hashcodeI[intro]:
  "((eq,(=)) \<in> R \<rightarrow> R \<rightarrow> bool_rel) \<Longrightarrow>
   (\<And>x y n. x \<in> Domain R \<Longrightarrow> y \<in> Domain R \<Longrightarrow> eq x y \<Longrightarrow> bhc n x = bhc n y) \<Longrightarrow>
   (\<And>x n. 1 < n \<Longrightarrow> bhc n x < n) \<Longrightarrow> is_bounded_hashcode R eq bhc"
  unfolding is_bounded_hashcode_def by force

lemma is_bounded_hashcodeD[dest]:
  assumes "is_bounded_hashcode R eq bhc"
  shows "(eq,(=)) \<in> R \<rightarrow> R \<rightarrow> bool_rel" and
        "\<And>n x y. x \<in> Domain R \<Longrightarrow> y \<in> Domain R \<Longrightarrow> eq x y \<Longrightarrow> bhc n x = bhc n y" and
        "\<And>n x. 1 < n \<Longrightarrow> bhc n x < n"
  using assms unfolding is_bounded_hashcode_def by simp_all

lemma bounded_hashcode_welldefined:
  assumes BHC: "is_bounded_hashcode Rk eq bhc" and
          R1: "(x1,x') \<in> Rk" and R2: "(x2,x') \<in> Rk"
  shows "bhc n x1 = bhc n x2"
proof-
  from is_bounded_hashcodeD[OF BHC] have "(eq,(=)) \<in> Rk \<rightarrow> Rk \<rightarrow> bool_rel" by simp
  with R1 R2 have "eq x1 x2" by (force dest: fun_relD)
  thus ?thesis using R1 R2 BHC by blast
qed

lemma abstract_bhc_correct[intro]:
  assumes "is_bounded_hashcode Rk eq bhc"
  shows "(bhc, abstract_bounded_hashcode Rk bhc) \<in> 
      nat_rel \<rightarrow> Rk \<rightarrow> nat_rel" (is "(bhc, ?bhc') \<in> _")
proof (intro fun_relI)
  fix n n' x x'
  assume A: "(n,n') \<in> nat_rel" and B: "(x,x') \<in> Rk"
  hence C: "n = n'" and D: "x' \<in> Range Rk" by auto
  have "?bhc' n' x' = bhc n x" 
      unfolding abstract_bounded_hashcode_def
      apply (simp add: C D, rule)
      apply (intro exI conjI, fact B, rule refl)
      apply (elim exE conjE, hypsubst,
          erule bounded_hashcode_welldefined[OF assms _ B])
      done
  thus "(bhc n x, ?bhc' n' x') \<in> nat_rel" by simp
qed

lemma abstract_bhc_is_bhc[intro]:
  fixes Rk :: "('c\<times>'a) set"
  assumes bhc: "is_bounded_hashcode Rk eq bhc"
  shows "is_bounded_hashcode Id (=) (abstract_bounded_hashcode Rk bhc)"
      (is "is_bounded_hashcode _ (=) ?bhc'")
proof
  fix x'::'a and y'::'a and n'::nat assume "x' = y'"
  thus "?bhc' n' x' = ?bhc' n' y'" by simp
next
  fix x'::'a and n'::nat assume "1 < n'"
  from abstract_bhc_correct[OF bhc] show "?bhc' n' x' < n'"
  proof (cases "x' \<in> Range Rk")
    case False
      with \<open>1 < n'\<close> show ?thesis 
          unfolding abstract_bounded_hashcode_def by simp
  next
    case True
      then obtain x where "(x,x') \<in> Rk" ..
      have "(n',n') \<in> nat_rel" ..
      from abstract_bhc_correct[OF assms] have "?bhc' n' x' = bhc n' x"
        apply -
        apply (drule fun_relD[OF _ \<open>(n',n') \<in> nat_rel\<close>],
               drule fun_relD[OF _ \<open>(x,x') \<in> Rk\<close>], simp)
        done
      also from \<open>1 < n'\<close> and bhc have "... < n'" by blast
      finally show "?bhc' n' x' < n'" .
  qed
qed simp

(*lemma hashable_bhc_is_bhc[autoref_ga_rules]:
  "\<lbrakk>STRUCT_EQ_tag eq (=;) REL_IS_ID R\<rbrakk> \<Longrightarrow> is_bounded_hashcode R eq bounded_hashcode"
  unfolding is_bounded_hashcode_def
  by (simp add: bounded_hashcode_bounds)*)

(* TODO: This is a hack that causes the relation to be instantiated to Id, if it is not
    yet fixed! *)
lemma hashable_bhc_is_bhc[autoref_ga_rules]:
  "\<lbrakk>STRUCT_EQ_tag eq (=); REL_FORCE_ID R\<rbrakk> \<Longrightarrow> is_bounded_hashcode R eq bounded_hashcode_nat"
  unfolding is_bounded_hashcode_def
  by (simp add: bounded_hashcode_nat_bounds)


subsection \<open>Default hash map size\<close>

definition is_valid_def_hm_size :: "'k itself \<Rightarrow> nat \<Rightarrow> bool"
    where "is_valid_def_hm_size type n \<equiv> n > 1"

lemma hashable_def_size_is_def_size[autoref_ga_rules]:
  shows "is_valid_def_hm_size TYPE('k::hashable) (def_hashmap_size TYPE('k))"
    unfolding is_valid_def_hm_size_def by (fact def_hashmap_size)

end
