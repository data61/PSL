(*<*)
theory Szpilrajn
  imports Main
begin
  (*>*)



section "Introduction"


text \<open>
  We formalize the Szpilrajn extension theorem~\cite{Szpilrajn:1930}, also known
as order-extension principal:
  Every strict partial order can be extended to strict linear order. 
This is a formalization of the proof presented in the Wikipedia article~\cite{wiki}.


A strict partial order is a transitive and irreflexive relation:\<close>


definition "strict_partial_order r \<equiv> trans r \<and> irrefl r"

lemma show_strict_partial_order[intro]: 
  assumes "trans r" and "irrefl r" 
  shows "strict_partial_order r"
  by (simp add: assms strict_partial_order_def)

lemma strict_partial_order_acyclic:
  assumes "strict_partial_order r"
  shows "acyclic r"
  by (metis acyclic_irrefl assms strict_partial_order_def trancl_id)

text \<open>A typical example is \<^term>\<open>(\<subset>)\<close> on sets:\<close>

lemma strict_partial_order_subset:
  "strict_partial_order {(x,y). x \<subset> y}"
proof
  show "trans {(x,y). x \<subset> y}"
    by (auto simp add: trans_def)
  show "irrefl {(x, y). x \<subset> y}"
    by (simp add: irrefl_def)
qed

text \<open>A strict linear order has all the properties of a strict partial order, but is also total: \<close>

lemma strict_linear_order_def: 
  "strict_linear_order r \<longleftrightarrow> strict_partial_order r \<and> total r"
  by (simp add: strict_linear_order_on_def strict_partial_order_def)


section "The Proof"

text \<open>A relation \<^term>\<open>r\<close> is a strict extension of a base relation \<^term>\<open>base_r\<close>
if \<^term>\<open>r\<close> is a strict partial order and \<^term>\<open>r\<close> includes \<^term>\<open>base_r\<close>:\<close>

definition "strict_ext base_r r \<equiv> strict_partial_order r \<and>  base_r \<subseteq> r"

text \<open>We start by proving that a strict partial order with two incomparable elements
\<^term>\<open>x\<close> and \<^term>\<open>y\<close> can be extended to a strict partial order where \<^term>\<open>x < y\<close>. \<close>

lemma can_extend_partial_order: 
  assumes spo: "strict_partial_order r"
    and no1: "(x,y) \<notin> r"
    and no2: "(y,x) \<notin> r"
    and neq: "x\<noteq>y"
  shows "strict_ext r ((r \<union> {(x,y)})\<^sup>+)"
  unfolding strict_ext_def proof (intro conjI show_strict_partial_order)
  show "trans ((r \<union> {(x, y)})\<^sup>+)"
    by simp
  show "r \<subseteq> (r \<union> {(x, y)})\<^sup>+" by auto

  from spo have "trans r" and "irrefl r" 
    by (auto simp add: strict_partial_order_def)

  show "irrefl ((r \<union> {(x, y)})\<^sup>+)"
  proof (clarsimp simp add: acyclic_irrefl[symmetric], intro conjI)
    show "acyclic r"
      by (simp add: spo strict_partial_order_acyclic)
    show "(y, x) \<notin> r\<^sup>*"
      using \<open>trans r\<close> neq no2 rtranclD by fastforce
  qed  
qed

text \<open>With this, we can start the proof of the Szpilrajn extension theorem.
For this we will use a variant of Zorns Lemma, which only considers nonempty chains:\<close>

lemma Zorns_po_lemma_nonempty:
  assumes po: "Partial_order r"
    and u: "\<And>C. \<lbrakk>C \<in> Chains r; C\<noteq>{}\<rbrakk> \<Longrightarrow> \<exists>u\<in>Field r. \<forall>a\<in>C. (a, u) \<in> r"
    and ne: "r \<noteq> {}"
  shows "\<exists>m\<in>Field r. \<forall>a\<in>Field r. (m, a) \<in> r \<longrightarrow> a = m"
proof -
  from `r\<noteq>{}` obtain x where "x\<in>Field r"
    using FieldI2 by fastforce
  with assms show ?thesis
    using Zorns_po_lemma by (metis empty_iff)  
qed


theorem Szpilrajn:
  assumes "strict_partial_order base_r"
  shows "\<exists>r. strict_linear_order r \<and> base_r \<subseteq> r" 
proof -
  text \<open>We define an order on the set of strict extensions of the base relation \<^term>\<open>base_r\<close>, 
    where \<^term>\<open>r \<le> s\<close> iff \<^term>\<open>r \<subseteq> s\<close>:\<close>

  define order_of_orders :: "('a rel) rel" where order_of_orders_def: 
    "order_of_orders = {(r,s). r\<subseteq>s \<and> strict_ext base_r r \<and> strict_ext base_r s }"

  have ord_Field: "Field order_of_orders = {r. strict_ext base_r r}"
    by (auto simp add: Field_def order_of_orders_def)


  text \<open>We now show that this set has a maximum and that any maximum of this set is 
    a strict linear order and as thus is one of the extensions we are looking for.\<close>

  text \<open>We begin by showing the existence of a maximal element \<^term>\<open>m\<close> using Zorns Lemma:\<close>

  have "\<exists>m\<in>Field order_of_orders. 
      \<forall>a\<in>Field order_of_orders. (m, a) \<in> order_of_orders \<longrightarrow> a = m"
  proof (rule Zorns_po_lemma_nonempty)




    text \<open>Zorns Lemma requires us to prove that our \<^term>\<open>order_of_orders\<close> is a nonempty  partial order
   and that every nonempty chain has an upper bound. 
   The partial order property is trivial, since we used \<^term>\<open>(\<subseteq>)\<close> for the relation:\<close>



    show "Partial_order order_of_orders"
      by (auto simp add: order_of_orders_def order_on_defs refl_on_def Field_def trans_def antisym_def)

    text \<open>Also, our order is obviously not empty since it contains \<^term>\<open>(base_r, base_r)\<close>:\<close>

    have "(base_r, base_r)\<in>order_of_orders"
      using assms strict_ext_def by (auto simp add: order_of_orders_def)
    thus "order_of_orders \<noteq> {}" by force


    text \<open>Next we show that each chain has an upper bound.
    For the upper bound we take the union of all relations in the chain. \<close>

    show "\<exists>u\<in>Field order_of_orders. \<forall>a\<in>C. (a, u) \<in> order_of_orders" 
      if C_def: "C \<in> Chains order_of_orders" and C_nonemtpy: "C \<noteq> {}"
      for C
    proof (rule bexI[where x="\<Union>C"])

      text \<open>Obviously each element in the chain is a strict extension of \<^term>\<open>base_r\<close> by definition
      and as such it is transitive, irreflexive and extends the base relation.\<close>

      have r_se: "strict_ext base_r r" if "r \<in> C" for r
        using `r \<in> C` C_def by (auto simp add: Chains_def order_of_orders_def)

      hence r_trans: "trans r" 
        and r_irrefl: "irrefl r" 
        and r_extends_base: "base_r \<subseteq> r" 
        if "r \<in> C" for r
        using that by (auto simp add: strict_ext_def strict_partial_order_def)

      text \<open>Because a chain is ordered, the union of the chain is also transitive:\<close>

      have C_ordered: "r\<subseteq>s \<or> s\<subseteq>r" if "r \<in> C" and "s \<in> C" for r s
        using C_def that by (auto simp add: Chains_def order_of_orders_def)

      hence "trans (\<Union>C)"
        by (simp add: chain_subset_def chain_subset_trans_Union r_trans)

      text \<open>The other properties also can be transferred from the single relations 
       to the union of the chain.
       Therefore the union is also a strict extension of \<^term>\<open>base_r\<close>: \<close>

      moreover have "irrefl (\<Union>C)"
        using irrefl_def r_irrefl by auto

      moreover have "base_r \<subseteq> (\<Union>C)" 
        by (simp add: less_eq_Sup r_extends_base that)

      ultimately have "strict_ext base_r (\<Union>C)" 
        by (simp add: show_strict_partial_order strict_ext_def that)

      show "(\<Union>C) \<in> Field order_of_orders"
        by (simp add: \<open>strict_ext base_r (\<Union> C)\<close> ord_Field)

      text \<open>The union is obviously an upper bound for the chain: \<close>
      show "\<forall>a\<in>C. (a, \<Union> C) \<in> order_of_orders"
        by (simp add: Sup_upper \<open>strict_ext base_r (\<Union> C)\<close> order_of_orders_def r_se)
    qed
  qed

  text \<open>Let our maximal element be named \<^term>\<open>max\<close>:\<close>

  from this obtain max 
    where max_field: "max\<in>Field order_of_orders"
      and is_max: 
        "\<forall>a\<in>Field order_of_orders. (max, a) \<in> order_of_orders \<longrightarrow> a = max"
    by auto

  from max_field have max_se: "strict_ext base_r max"
    using ord_Field by auto
  hence max_spo: "strict_partial_order max"
    and "base_r \<subseteq> max"
    using strict_ext_def by auto


  text \<open>We still have to show, that \<^term>\<open>max\<close> is a strict linear order, 
  meaning that it is also a total order: \<close>

  have "total max"
  proof
    fix x y :: 'a
    assume "x\<noteq>y"


    show "(x, y) \<in> max \<or> (y, x) \<in> max"
    proof (rule ccontr, auto)

      text \<open>Assume that \<^term>\<open>max\<close> is not total, and \<^term>\<open>x\<close> and \<^term>\<open>y\<close> are incomparable.
      Then we can extend \<^term>\<open>max\<close> by setting $x < y$:\<close>

      assume "(x, y) \<notin> max" and "(y, x) \<notin> max"
      let ?max' = "((max \<union> {(x, y)})\<^sup>+)"

      from max_spo `(x, y) \<notin> max` `(y, x) \<notin> max` `x\<noteq>y` 
      have max'_se_max: "strict_ext max ?max'" by (rule can_extend_partial_order)

      hence max'_se: "strict_ext base_r ?max'"
        by (meson \<open>base_r \<subseteq> max\<close> strict_ext_def subset_trans)

      text \<open>The extended relation is greater than \<^term>\<open>max\<close>, which is a contradiction.\<close>

      have "(max, ?max')\<in>order_of_orders"
        using max'_se by (auto simp add: order_of_orders_def max_se)
      thus False
        using FieldI2 \<open>(x, y) \<notin> max\<close> is_max by fastforce
    qed
  qed

  with max_spo have "strict_linear_order max"
    by (auto simp add: strict_linear_order_def)

  with \<open>base_r \<subseteq> max\<close>
  show "\<exists>r. strict_linear_order r \<and> base_r \<subseteq> r" by auto
qed

text \<open>As a corollary, we can also show that we can extend any \<^term>\<open>acyclic\<close> relation
to a strict linear order: \<close>

corollary can_extend_acyclic_order_to_strict_linear:
  assumes "acyclic base_r"
  shows "\<exists>r. strict_linear_order r \<and> base_r \<subseteq> r" 
proof -
  have "strict_partial_order (base_r\<^sup>+)"
    using acyclic_irrefl assms trans_trancl by blast
  thus ?thesis
    by (meson Szpilrajn r_into_trancl' subset_iff)
qed

text \<open>Let us conclude with an example, showing that there exists a strict linear 
order on sets, which includes the subset relation:\<close>

lemma exists_strict_partial_order_on_sets:
  shows "\<exists>r. strict_linear_order r \<and> {(x,y). x \<subset> y} \<subseteq> r"
  using strict_partial_order_subset by (rule Szpilrajn)

(*<*)
end
(*>*)
