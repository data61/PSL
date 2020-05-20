section \<open>Commonly used Lemmas\<close>
theory Common
imports 
  Main
  "HOL-Library.Extended_Nat" 
  "HOL-Eisbach.Eisbach"
begin

declare [[coercion_enabled = false]]

subsection \<open>Miscellaneous\<close>

lemma split_sym_rel: 
  fixes G :: "'a rel"
  assumes "sym G" "irrefl G"
  obtains E where "E\<inter>E\<inverse> = {}" "G = E \<union> E\<inverse>"  
proof -
  obtain R :: "'a rel" 
  where WO: "well_order_on UNIV R" using Zorn.well_order_on ..

  let ?E = "G \<inter> R"
  
  from \<open>irrefl G\<close> have [simp, intro!]: "(x,x)\<notin>G" for x 
    by (auto simp: irrefl_def)
  
  have "?E \<inter> ?E\<inverse> = {}"
    using WO 
    unfolding well_order_on_def linear_order_on_def 
      partial_order_on_def antisym_def
    by fastforce 
  moreover  
  have "G = ?E \<union> ?E\<inverse>" 
    apply safe
    apply (simp_all add: symD[OF \<open>sym G\<close>])
    using WO unfolding well_order_on_def linear_order_on_def total_on_def
    by force
  ultimately show ?thesis by (rule that)  
qed


lemma least_antimono: "X\<noteq>{} \<Longrightarrow> X\<subseteq>Y \<Longrightarrow> (LEAST y::_::wellorder. y\<in>Y) \<le> (LEAST x. x\<in>X)"
  by (metis LeastI_ex Least_le equals0I rev_subsetD)
  
lemma distinct_map_snd_inj: "distinct (map snd l) \<Longrightarrow> (a,b)\<in>set l \<Longrightarrow> (a',b)\<in>set l \<Longrightarrow> a=a'"
  by (metis distinct_map inj_onD prod.sel(2) prod.simps(1))
  
lemma map_add_apply: "(m\<^sub>1 ++ m\<^sub>2) k = (case m\<^sub>2 k of None \<Rightarrow> m\<^sub>1 k | Some x \<Rightarrow> Some x)"
  by (auto simp: map_add_def)

lemma map_eq_append_conv: "map f xs = ys\<^sub>1@ys\<^sub>2 
  \<longleftrightarrow> (\<exists>xs\<^sub>1 xs\<^sub>2. xs = xs\<^sub>1@xs\<^sub>2 \<and> map f xs\<^sub>1 = ys\<^sub>1 \<and> map f xs\<^sub>2 = ys\<^sub>2)"
  apply rule
  subgoal
    apply (rule exI[where x="take (length ys\<^sub>1) xs"])
    apply (rule exI[where x="drop (length ys\<^sub>1) xs"])
    apply (drule sym)
    by (auto simp: append_eq_conv_conj take_map drop_map)
  subgoal by auto
  done
  
  
lemma prod_case_const[simp]: "case_prod (\<lambda>_ _. c) = (\<lambda>_. c)" by auto

lemma card2_eq: "card e = 2 \<longleftrightarrow> (\<exists>u v. u\<noteq>v \<and> e={u,v})"
  by (auto simp: eval_nat_numeral card_Suc_eq)

lemma in_ranE:
  assumes "v \<in> ran m"  
  obtains k where "m k = Some v"
  using assms unfolding ran_def by auto
  
  
lemma Inf_in:
  fixes A :: "'a::{linorder,complete_lattice} set"
  assumes "finite A" "A\<noteq>{}" 
  shows "Inf A \<in> A" 
  using assms 
  proof (induction A rule: finite_induct)
    case empty
    then show ?case by simp
  next
    have [simp]: "inf a b = (if a\<le>b then a else b)" for a b :: 'a
      by (meson inf_absorb2 le_iff_inf linear)
  
    case (insert x F)
    show ?case proof cases
      assume "F={}" thus ?thesis by auto
    next
      assume "F\<noteq>{}"
      with insert.IH have "Inf F \<in> F" .
      then show ?thesis
        using le_less_linear[of x "Inf F"]
        by auto 
    
  qed
qed  

lemma INF_of_enat_infty_iff1: "(INF x \<in> A. enat (f x)) = \<infinity> \<longleftrightarrow> A={}"
  apply (cases "A={}")
  subgoal by (simp add: top_enat_def)
  subgoal by safe (metis INF_top_conv(2) enat.distinct(1) top_enat_def)+
  done

lemma INF_of_enat_infty_iff2: 
  "\<infinity> = (INF x \<in> A. enat (f x)) \<longleftrightarrow> A={}"  
  by (metis INF_of_enat_infty_iff1)

lemmas INF_of_enat_infty_iff[simp] = INF_of_enat_infty_iff1 INF_of_enat_infty_iff2
    
lemma INF_of_enat_nat_conv1: 
  assumes "finite A"  
  shows "(INF x \<in> A. enat (f x)) = enat d \<longleftrightarrow> (\<exists>x\<in>A. d = f x \<and> (\<forall>y\<in>A. f x \<le> f y))"  
proof -
  from assms have F: "finite (enat`f`A)" by auto

  show ?thesis proof (cases "A={}")
    case True thus ?thesis by (auto simp: top_enat_def)
  next
    case [simp]: False  
    note * = Inf_in[OF F, simplified]
    show ?thesis
      apply (rule iffI)
      subgoal by (smt False Inf_in assms enat.inject enat_ord_simps(1) finite_imageI imageE image_is_empty le_INF_iff order_refl)
      subgoal by clarsimp (meson INF_greatest INF_lower antisym enat_ord_simps(1))
      done
  qed
qed      
      
lemma INF_of_enat_nat_conv2: 
  assumes "finite A"  
  shows "enat d = (INF x \<in> A. enat (f x)) \<longleftrightarrow> (\<exists>x\<in>A. d = f x \<and> (\<forall>y\<in>A. f x \<le> f y))"  
  using INF_of_enat_nat_conv1[OF assms] by metis

lemmas INF_of_enat_nat_conv = INF_of_enat_nat_conv1 INF_of_enat_nat_conv2
  
lemma finite_inf_linorder_ne_ex:
  fixes f :: "_ \<Rightarrow> _::{complete_lattice,linorder}"
  assumes "finite S"
  assumes "S\<noteq>{}"
  shows "\<exists>x\<in>S. (INF x \<in> S. f x) = f x"
  using assms
  by (meson Inf_in finite_imageI imageE image_is_empty)
  
  

lemma finite_linorder_eq_INF_conv: "finite S 
  \<Longrightarrow> a = (INF x \<in> S. f x) \<longleftrightarrow> (if S={} then a=top else \<exists>x\<in>S. a=f x \<and> (\<forall>y\<in>S. a \<le> f y))"
  for a :: "_::{complete_lattice,linorder}"
  by (auto 
    simp: INF_greatest INF_lower  
    intro: finite_inf_linorder_ne_ex antisym)
  
lemma sym_inv_eq[simp]: "sym E \<Longrightarrow> E\<inverse> = E" unfolding sym_def by auto 

lemma insert_inv[simp]: "(insert e E)\<inverse> = insert (prod.swap e) (E\<inverse>)"
  by (cases e) auto
  
lemma inter_compl_eq_diff[simp]: "x \<inter> - s = x - s"  
  by auto

lemma inter_same_diff[simp]: "A\<inter>(A-S) = A-S" by blast  
  
lemma minus_inv_sym_aux[simp]: "(- {(a, b), (b, a)})\<inverse> = -{(a,b),(b,a)}" 
  by auto
    

subsection \<open>The-Default\<close>
fun the_default :: "'a \<Rightarrow> 'a option \<Rightarrow> 'a" where
  "the_default d None = d"
| "the_default _ (Some x) = x"

lemma the_default_alt: "the_default d x = (case x of None \<Rightarrow> d | Some v \<Rightarrow> v)" by (auto split: option.split)


subsection \<open>Implementing \<open>enat\<close> by Option\<close>

text \<open>Our maps are functions to \<open>nat option\<close>,which are interpreted as \<open>enat\<close>,
  \<open>None\<close> being \<open>\<infinity>\<close>\<close>

fun enat_of_option :: "nat option \<Rightarrow> enat" where
  "enat_of_option None = \<infinity>" 
| "enat_of_option (Some n) = enat n"  
  
lemma enat_of_option_inj[simp]: "enat_of_option x = enat_of_option y \<longleftrightarrow> x=y"
  by (cases x; cases y; simp)

lemma enat_of_option_simps[simp]:
  "enat_of_option x = enat n \<longleftrightarrow> x = Some n"
  "enat_of_option x = \<infinity> \<longleftrightarrow> x = None"
  "enat n = enat_of_option x \<longleftrightarrow> x = Some n"
  "\<infinity> = enat_of_option x \<longleftrightarrow> x = None"
  by (cases x; auto; fail)+
  
lemma enat_of_option_le_conv: "enat_of_option m \<le> enat_of_option n \<longleftrightarrow> (case (m,n) of 
    (_,None) \<Rightarrow> True
  | (Some a, Some b) \<Rightarrow> a\<le>b
  | (_, _) \<Rightarrow> False
)"
  by (auto split: option.split)

  
subsection \<open>Foldr-Refine\<close>
lemma foldr_refine:
  assumes "I s"
  assumes "\<And>s x. I s \<Longrightarrow> x\<in>set l \<Longrightarrow> I (f x s) \<and> \<alpha> (f x s) = f' x (\<alpha> s)"
  shows "I (foldr f l s) \<and> \<alpha> (foldr f l s) = foldr f' l (\<alpha> s)"
  using assms
  by (induction l arbitrary: s) auto
  
end
