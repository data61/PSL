(*  Title:      NatInt.thy
    Author:     Sven Linker, University of Liverpool

Intervals based on natural numbers. Defines a 
bottom element (empty set), infimum (set intersection),
partial order (subset relation), cardinality (set cardinality).

The union of intervals i and j can only be created, if they are consecutive, i.e.,
max i +1 = min j (or vice versa). To express consecutiveness, we employ the 
predicate consec.

Also contains a "chopping" predicate N_Chop(i,j,k): i can be divided into
consecutive intervals j and k.
*)

section \<open>Discrete Intervals based on Natural Numbers\<close>

text\<open>We define a type of intervals based on the natural numbers. To that 
end, we employ standard operators of Isabelle, but in addition prove some
structural properties of the intervals. In particular, we show that this type
constitutes a meet-semilattice with a bottom element and equality.

Furthermore, we show that this semilattice allows for a constrained join, i.e.,
the union of two intervals is defined, if either one of them is empty, or they are
consecutive. Finally, we define the notion of \emph{chopping} an interval into
two consecutive subintervals.\<close>

theory NatInt
  imports Main 
begin

text \<open>A discrete interval is a set of consecutive natural numbers, or the empty 
set.\<close>

typedef nat_int = "{S . (\<exists> (m::nat) n . {m..n }=S) }"  
  by auto
setup_lifting type_definition_nat_int

subsection \<open>Basic properties of discrete intervals.\<close>
  
locale nat_int 
interpretation nat_int_class?: nat_int .

context nat_int
begin
  
lemma un_consec_seq: "(m::nat)\<le> n \<and> n+1 \<le> l \<longrightarrow> {m..n} \<union> {n+1..l} = {m..l}" 
  by auto
    
lemma int_conseq_seq: " {(m::nat)..n} \<inter> {n+1..l} = {}"
  by auto
        
lemma empty_type: "{} \<in> { S . \<exists> (m:: nat) n . {m..n}=S}"
  by auto
    
lemma inter_result: "\<forall>x \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }. 
         \<forall>y \<in> {S . (\<exists> (m::nat) n . {m..n }=S) }. 
           x \<inter> y \<in>{S . (\<exists> (m::nat) n .  {m..n }=S)}" 
  using Int_atLeastAtMost by blast      
    
lemma union_result: "\<forall>x \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }. 
         \<forall>y \<in> {S . (\<exists> (m::nat) n .  {m..n }=S)  }. 
           x \<noteq> {} \<and> y \<noteq> {} \<and> Max x +1 = Min y 
            \<longrightarrow> x \<union> y \<in>{S . (\<exists> (m::nat) n . {m..n }=S)  }"  
proof (rule ballI)+
  fix x y
  assume "x\<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }" 
    and "y\<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }"
  then have x_def:"(\<exists>m n.  {m..n} = x) "  
    and y_def:"(\<exists>m n.  {m..n} = y) " by blast+    
  show   " x \<noteq> {} \<and> y \<noteq> {} \<and>   Max x+1 = Min y 
            \<longrightarrow> x \<union>  y \<in> {S. (\<exists>m n.  {m..n} = S) }"
  proof
    assume pre:"x \<noteq> {} \<and> y \<noteq> {} \<and> Max x + 1 = Min y"
    then have x_int:"\<exists>m n. m \<le> n \<and> {m..n} = x" 
          and y_int:"(\<exists>m n. m \<le> n \<and> {m..n} = y)"
      using  x_def y_def by force+      
    {
      fix ya yb xa xb
      assume y_prop:"ya \<le> yb \<and> {ya..yb} = y"
      assume x_prop:"xa \<le> xb \<and> {xa..xb} = x"          
      from  x_prop have upper_x:"Max x = xb" 
        by (metis Sup_nat_def cSup_atLeastAtMost)
      from y_prop have lower_y:"Min y = ya" 
        by (metis Inf_fin.coboundedI Inf_fin_Min Min_in add.right_neutral finite_atLeastAtMost
            le_add1 ord_class.atLeastAtMost_iff order_class.antisym pre)
      from upper_x and lower_y and pre have upper_eq_lower: "xb+1 = ya" 
        by blast
      hence "y= {xb+1 .. yb}" using y_prop by blast
      hence "x \<union> y = {xa..yb}" 
        using un_consec_seq upper_eq_lower x_prop y_prop by blast
      then have " x \<union> y \<in> {S.(\<exists>m n.  {m..n} = S) }"
        by auto
    }      
    then show "x \<union> y \<in> {S.(\<exists>m n.  {m..n} = S)}" 
      using x_int y_int by blast
  qed
qed
  
  

lemma union_empty_result1: "\<forall>i \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }.
                                  i \<union> {} \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) }" 
  by blast   

lemma union_empty_result2: "\<forall>i \<in> {S . (\<exists> (m::nat) n . {m..n }=S)  }.
                                  {} \<union> i \<in> {S . (\<exists> (m::nat) n . {m..n }=S)  }" 
  by blast 
    
lemma finite:" \<forall>i \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) } . (finite i)"
  by blast
    
lemma not_empty_means_seq:"\<forall>i \<in> {S . (\<exists> (m::nat) n .  {m..n }=S) } . i \<noteq> {}
                            \<longrightarrow> ( \<exists>m n . m \<le> n \<and> {m..n} = i)" 
  using atLeastatMost_empty_iff 
  by force   
end
  
text \<open>The empty set is the bottom element of the type. The infimum/meet of 
the semilattice is set intersection. The order is given by the subset relation.
\<close>

instantiation nat_int :: bot
begin
lift_definition bot_nat_int :: "nat_int" is Set.empty by force
instance by standard
end

instantiation nat_int ::  inf
begin
lift_definition inf_nat_int  ::"nat_int \<Rightarrow> nat_int \<Rightarrow> nat_int" is Set.inter  by force
instance
proof qed
end

instantiation nat_int :: "order_bot"
begin
lift_definition less_eq_nat_int :: "nat_int \<Rightarrow> nat_int \<Rightarrow> bool" is Set.subset_eq .
lift_definition less_nat_int :: "nat_int \<Rightarrow> nat_int \<Rightarrow> bool" is Set.subset .
instance
proof
  fix i j k ::nat_int
  show "(i < j) = (i \<le> j \<and> \<not> j \<le> i)" 
    by (simp add: less_eq_nat_int.rep_eq less_le_not_le less_nat_int.rep_eq)
  show "i \<le> i" by (simp add:less_eq_nat_int.rep_eq) 
  show " i \<le> j \<Longrightarrow> j \<le> k \<Longrightarrow> i \<le> k" by (simp add:less_eq_nat_int.rep_eq)
  show "i \<le> j \<Longrightarrow> j \<le> i \<Longrightarrow> i = j"  
    by (simp add: Rep_nat_int_inject less_eq_nat_int.rep_eq )
  show "bot \<le> i" using  less_eq_nat_int.rep_eq 
    using bot_nat_int.rep_eq by blast
qed
end  

instantiation nat_int ::  "semilattice_inf"
begin
instance 
proof
  fix i j k :: nat_int
  show "i \<le> j \<Longrightarrow> i \<le> k \<Longrightarrow> i \<le> inf j k" 
    by (simp add: inf_nat_int.rep_eq less_eq_nat_int.rep_eq)
  show " inf i   j \<le> i" 
    by (simp add: inf_nat_int.rep_eq less_eq_nat_int.rep_eq) 
  show "inf i  j \<le> j" 
    by (simp add: inf_nat_int.rep_eq less_eq_nat_int.rep_eq) 
qed      
end

instantiation nat_int:: "equal"
begin
definition equal_nat_int :: "nat_int \<Rightarrow> nat_int \<Rightarrow> bool"  
  where "equal_nat_int i  j \<equiv> i \<le> j \<and> j \<le> i"
instance 
proof
  fix i j :: nat_int
  show " equal_class.equal i j = (i = j)" using equal_nat_int_def  by auto
qed
end
  
  
context nat_int 
begin
abbreviation subseteq :: "nat_int \<Rightarrow> nat_int\<Rightarrow> bool" (infix "\<sqsubseteq>" 30)
  where  "i \<sqsubseteq> j == i \<le> j "
abbreviation empty :: "nat_int" ("\<emptyset>")
  where "\<emptyset> \<equiv> bot"
    
notation inf (infix "\<sqinter>" 70)


text \<open>The union of two intervals is only defined, if it is also
a discrete interval.\<close>
definition union :: "nat_int \<Rightarrow> nat_int \<Rightarrow> nat_int" (infix "\<squnion>" 65)
  where "i \<squnion> j = Abs_nat_int (Rep_nat_int i \<union> Rep_nat_int j)"

text \<open>Non-empty intervals contain a minimal and maximal element. 
Two non-empty intervals \(i\) and \(j\) are 
consecutive, if the minimum of \(j\) is the successor of the
maximum of \(i\).
Furthermore, the interval \(i\) can be chopped into the intervals \(j\)
and \(k\), if the union of \(j\) and \(k\) equals \(i\), and if \(j\)
and \(k\) are not-empty, they must be consecutive. Finally, we define
the cardinality of discrete intervals by lifting the cardinality of
sets. 
\<close>
definition maximum :: "nat_int \<Rightarrow> nat"
  where maximum_def: "i \<noteq> \<emptyset> \<Longrightarrow> maximum (i) =   Max (Rep_nat_int i)" 
    
definition minimum :: "nat_int \<Rightarrow> nat"
  where minimum_def: "i \<noteq> \<emptyset> \<Longrightarrow> minimum(i) = Min (Rep_nat_int i)"

definition consec:: "nat_int\<Rightarrow>nat_int \<Rightarrow> bool" 
  where "consec i j \<equiv> (i\<noteq>\<emptyset> \<and> j \<noteq> \<emptyset> \<and> (maximum(i)+1 = minimum j))"
    
definition N_Chop :: "nat_int \<Rightarrow> nat_int \<Rightarrow> nat_int \<Rightarrow> bool" ("N'_Chop'(_,_,_')" 51)
  where nchop_def :
    "N_Chop(i,j,k) \<equiv> (i =  j \<squnion> k   \<and> (j = \<emptyset> \<or>  k = \<emptyset> \<or> consec j k))"

lift_definition card' ::"nat_int \<Rightarrow> nat"  ( "|_|" 70) is card .


text\<open>For convenience, we also lift the membership relation and its negation
to discrete intervals.\<close>

lift_definition el::"nat \<Rightarrow> nat_int \<Rightarrow> bool" (infix "\<^bold>\<in>" 50) is "Set.member" .

lift_definition not_in ::"nat \<Rightarrow> nat_int \<Rightarrow> bool" (infix "\<^bold>\<notin>" 40)  is Set.not_member . 
end
  
lemmas[simp] = nat_int.el.rep_eq nat_int.not_in.rep_eq nat_int.card'.rep_eq

context nat_int 
begin
  
lemma in_not_in_iff1 :"n \<^bold>\<in> i \<longleftrightarrow> \<not> n\<^bold>\<notin> i" by simp
lemma in_not_in_iff2: "n\<^bold>\<notin> i \<longleftrightarrow> \<not> n \<^bold>\<in> i" by simp
    
    
lemma rep_non_empty_means_seq:"i \<noteq>\<emptyset> 
                                \<longrightarrow> (\<exists>m n. m \<le> n \<and> ({m..n} =( Rep_nat_int i)))" 
  by (metis Rep_nat_int Rep_nat_int_inject bot_nat_int.rep_eq nat_int.not_empty_means_seq)
  
lemma non_empty_max: "i \<noteq> \<emptyset> \<longrightarrow> (\<exists>m . maximum(i) = m)" 
  by auto
    
lemma non_empty_min: "i \<noteq> \<emptyset> \<longrightarrow> (\<exists>m . minimum(i) = m)" 
  by auto
    
lemma minimum_in: "i \<noteq> \<emptyset> \<longrightarrow> minimum i \<^bold>\<in> i"
  by (metis Min_in atLeastatMost_empty_iff2 finite_atLeastAtMost minimum_def
      el.rep_eq rep_non_empty_means_seq)
    
lemma maximum_in: "i \<noteq> \<emptyset> \<longrightarrow> maximum i \<^bold>\<in> i"
  by (metis Max_in atLeastatMost_empty_iff2 finite_atLeastAtMost maximum_def 
      el.rep_eq rep_non_empty_means_seq)
    
lemma non_empty_elem_in:"i \<noteq> \<emptyset> \<longleftrightarrow> (\<exists>n. n \<^bold>\<in> i)"   
proof
  assume assm:"i \<noteq> \<emptyset>"
  show "\<exists>n . n \<^bold>\<in> i" 
    by (metis assm Rep_nat_int_inverse all_not_in_conv el.rep_eq bot_nat_int_def)
next
  assume assm:"\<exists>n. n \<^bold>\<in> i"
  show "i \<noteq> \<emptyset>" 
    using Abs_nat_int_inverse assm el.rep_eq bot_nat_int_def by fastforce
qed
  
lemma leq_nat_non_empty:"(m::nat) \<le> n \<longrightarrow> Abs_nat_int{m..n} \<noteq> \<emptyset>"  
proof
  assume assm:"m \<le>n"
  then have non_empty:"{m..n} \<noteq> {} " 
    using atLeastatMost_empty_iff by blast
  with assm have "{m..n} \<in> {S . (\<exists> (m::nat) n .  {m..n }=S)  }" by blast
  then show "Abs_nat_int {m..n} \<noteq> \<emptyset>" 
    using Abs_nat_int_inject empty_type non_empty bot_nat_int_def 
    by (simp add: bot_nat_int.abs_eq)
qed
  
lemma leq_max_sup:"(m::nat) \<le> n \<longrightarrow> Max {m..n} = n" 
  by (metis Sup_nat_def cSup_atLeastAtMost)
    
lemma leq_min_inf: "(m::nat) \<le> n \<longrightarrow> Min {m..n} = m"
  by (meson Min_in Min_le antisym atLeastAtMost_iff atLeastatMost_empty_iff 
      eq_imp_le finite_atLeastAtMost)
    
lemma leq_max_sup':"(m::nat) \<le> n \<longrightarrow> maximum(Abs_nat_int{m..n}) = n" 
proof 
  assume assm:"m \<le> n"
  hence in_type:"{m..n} \<in> {S . (\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={} }" by blast
  from assm have "Abs_nat_int{m..n} \<noteq> \<emptyset>" using leq_nat_non_empty by blast
  hence max:"maximum(Abs_nat_int{m..n}) = Max (Rep_nat_int (Abs_nat_int {m..n}))"
    using maximum_def by blast
  from in_type have " (Rep_nat_int (Abs_nat_int {m..n})) = {m..n}" 
    using Abs_nat_int_inverse by blast
  hence  "Max (Rep_nat_int (Abs_nat_int{m..n})) = Max {m..n}" by simp
  with max have simp_max:"maximum(Abs_nat_int{m..n}) = Max {m..n}" by simp
  from assm have "Max {m..n} = n" using leq_max_sup by blast
  with simp_max show "maximum(Abs_nat_int{m..n}) = n" by simp
qed
  
lemma leq_min_inf':"(m::nat) \<le> n \<longrightarrow> minimum(Abs_nat_int{m..n}) = m" 
proof 
  assume assm:"m \<le> n"
  hence in_type:"{m..n} \<in> {S . (\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={} }" by blast
  from assm have "Abs_nat_int{m..n} \<noteq> \<emptyset>" using leq_nat_non_empty by blast
  hence min:"minimum(Abs_nat_int{m..n}) = Min(Rep_nat_int (Abs_nat_int {m..n}))"
    using  minimum_def by blast
  from in_type have " (Rep_nat_int (Abs_nat_int {m..n})) = {m..n}" 
    using Abs_nat_int_inverse by blast
  hence  "Min (Rep_nat_int (Abs_nat_int{m..n})) = Min {m..n}" by simp
  with min have simp_min:"minimum(Abs_nat_int{m..n}) = Min {m..n}" by simp
  from assm have "Min {m..n} = m" using leq_min_inf by blast
  with simp_min show "minimum(Abs_nat_int{m..n}) = m" by simp
qed
  
lemma in_refl:"(n::nat)  \<^bold>\<in> Abs_nat_int {n}"
proof -
  have "(n::nat) \<le> n" by simp
  hence "{n} \<in> {S . (\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={} }" by auto
  then show "n \<^bold>\<in> Abs_nat_int {n}" 
    by (simp add: Abs_nat_int_inverse el_def)
qed
  
lemma in_singleton:" m \<^bold>\<in> Abs_nat_int{n} \<longrightarrow> m = n"
proof
  assume assm:" m \<^bold>\<in> Abs_nat_int{n}"
  have "(n::nat) \<le> n" by simp
  hence "{n} \<in> {S . (\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={} }" by auto
  with assm show "m=n" by (simp add: Abs_nat_int_inverse el_def)
qed

subsection \<open>Algebraic properties of intersection and union.\<close>
  
lemma inter_empty1:"(i::nat_int) \<sqinter> \<emptyset> = \<emptyset>" 
  using Rep_nat_int_inject inf_nat_int.rep_eq bot_nat_int.abs_eq bot_nat_int.rep_eq 
  by fastforce 
    
lemma inter_empty2:"\<emptyset> \<sqinter> (i::nat_int) = \<emptyset>" 
  by (metis inf_commute nat_int.inter_empty1)
        
lemma un_empty_absorb1:"i \<squnion> \<emptyset> = i" 
  using  Abs_nat_int_inverse Rep_nat_int_inverse union_def empty_type bot_nat_int.rep_eq
  by auto
    
lemma un_empty_absorb2:"\<emptyset> \<squnion> i = i" 
  using  Abs_nat_int_inverse Rep_nat_int_inverse union_def empty_type bot_nat_int.rep_eq
  by auto

text \<open>Most properties of the union of two intervals depends on them being consectuive,
to ensure that their union exists.\<close>

lemma consec_un:"consec i j \<and> n \<notin> Rep_nat_int(i) \<union> Rep_nat_int j 
                  \<longrightarrow> n \<^bold>\<notin>  (i \<squnion> j)"
proof
  assume assm:"consec i j \<and> n \<notin>  Rep_nat_int i \<union> Rep_nat_int j" 
  thus "n \<^bold>\<notin> (i \<squnion> j)" 
  proof -
    have f1: "Abs_nat_int (Rep_nat_int (i \<squnion> j)) 
              = Abs_nat_int (Rep_nat_int i \<union> Rep_nat_int j)"
      using Rep_nat_int_inverse union_def by presburger
    have "i \<noteq> \<emptyset> \<and> j \<noteq> \<emptyset> \<and> maximum i + 1 = minimum j"
      using assm consec_def by auto
    then have "\<exists>n na. {n..na} = Rep_nat_int i \<union> Rep_nat_int j" 
      by (metis (no_types) leq_max_sup leq_min_inf maximum_def minimum_def 
          rep_non_empty_means_seq un_consec_seq)
    then show ?thesis
      using f1 Abs_nat_int_inject Rep_nat_int not_in.rep_eq assm by auto
  qed
qed
    
lemma un_subset1: "consec i j \<longrightarrow> i \<sqsubseteq> i \<squnion> j" 
proof
  assume "consec i j"
  then have assm:"i \<noteq> \<emptyset> \<and> j \<noteq> \<emptyset> \<and> maximum i+1 = minimum j" 
    using consec_def by blast
  have "Rep_nat_int i \<union> Rep_nat_int j =  {minimum i.. maximum j}" 
    by (metis assm nat_int.leq_max_sup nat_int.leq_min_inf nat_int.maximum_def 
        nat_int.minimum_def nat_int.rep_non_empty_means_seq nat_int.un_consec_seq)
  then show "i \<sqsubseteq> i \<squnion> j" using Abs_nat_int_inverse Rep_nat_int 
    by (metis (mono_tags, lifting) Un_upper1 less_eq_nat_int.rep_eq mem_Collect_eq
        nat_int.union_def)
qed
  
lemma un_subset2: "consec i j \<longrightarrow> j \<sqsubseteq> i \<squnion> j"
proof
  assume "consec i j"
  then have assm:"i \<noteq> \<emptyset> \<and> j \<noteq> \<emptyset> \<and> maximum i+1 = minimum j" 
    using consec_def by blast
  have "Rep_nat_int i \<union> Rep_nat_int j =  {minimum i.. maximum j}" 
    by (metis assm nat_int.leq_max_sup nat_int.leq_min_inf nat_int.maximum_def 
        nat_int.minimum_def nat_int.rep_non_empty_means_seq nat_int.un_consec_seq)
  then show "j \<sqsubseteq> i \<squnion> j" using Abs_nat_int_inverse Rep_nat_int
    by (metis (mono_tags, lifting) Un_upper2 less_eq_nat_int.rep_eq mem_Collect_eq
        nat_int.union_def)
qed
 
lemma inter_distr1:"consec j k \<longrightarrow> i \<sqinter> (j \<squnion> k) = (i \<sqinter> j) \<squnion> (i \<sqinter> k)"  
  unfolding consec_def
proof  
  assume assm:"j \<noteq> \<emptyset> \<and> k \<noteq> \<emptyset> \<and> maximum j +1 = minimum k"
  then show " i \<sqinter> (j \<squnion> k) = (i \<sqinter> j) \<squnion> (i \<sqinter> k)"  
  proof -
    have f1: "\<forall>n. n = \<emptyset> \<or> maximum n = Max (Rep_nat_int n)"
      using nat_int.maximum_def by auto
    have f2: "Rep_nat_int j \<noteq> {}"
      using assm nat_int.maximum_in by auto
    have f3: "maximum j = Max (Rep_nat_int j)"
      using f1 by (meson assm)
    have "maximum k \<^bold>\<in> k"
      using assm nat_int.maximum_in by blast
    then have "Rep_nat_int k \<noteq> {}"
      by fastforce
    then have "Rep_nat_int (j \<squnion> k) = Rep_nat_int j \<union> Rep_nat_int k"
      using f3 f2 Abs_nat_int_inverse Rep_nat_int assm nat_int.minimum_def 
        nat_int.union_def union_result 
        by auto
    then show ?thesis
      by (metis Rep_nat_int_inverse inf_nat_int.rep_eq inf_sup_distrib1 nat_int.union_def)
  qed
qed
  
lemma inter_distr2:"consec j k \<longrightarrow> (j \<squnion> k) \<sqinter> i = (j \<sqinter> i) \<squnion> (k \<sqinter> i)"
  by (simp add: inter_distr1 inf_commute)
    
lemma consec_un_not_elem1:"consec i j \<and> n\<^bold>\<notin> i \<squnion> j \<longrightarrow>  n \<^bold>\<notin> i"
  using un_subset1 less_eq_nat_int.rep_eq not_in.rep_eq by blast 
    
lemma consec_un_not_elem2:"consec i j \<and> n\<^bold>\<notin> i \<squnion> j \<longrightarrow>  n \<^bold>\<notin> j"
  using  un_subset2 less_eq_nat_int.rep_eq not_in.rep_eq by blast
    
lemma consec_un_element1:"consec i j \<and> n \<^bold>\<in> i \<longrightarrow> n \<^bold>\<in> i \<squnion> j" 
  using less_eq_nat_int.rep_eq nat_int.el.rep_eq nat_int.un_subset1 by blast
    
lemma consec_un_element2:"consec i j \<and> n \<^bold>\<in> j \<longrightarrow> n \<^bold>\<in> i \<squnion> j"
  using less_eq_nat_int.rep_eq nat_int.el.rep_eq nat_int.un_subset2 by blast
    
lemma consec_lesser:" consec i j  \<longrightarrow> (\<forall>n m. (n \<^bold>\<in> i \<and> m \<^bold>\<in> j \<longrightarrow> n < m))" 
proof (rule allI|rule impI)+
  assume "consec i j"
  fix n and m  
  assume assump:"n \<^bold>\<in> i \<and> m \<^bold>\<in> j "
  then have  max:"n \<le> maximum i" 
    by (metis \<open>consec i j\<close> atLeastAtMost_iff leq_max_sup maximum_def consec_def
        el.rep_eq rep_non_empty_means_seq)
  from assump have min: "m \<ge> minimum j" 
    by (metis Min_le \<open>consec i j\<close> finite_atLeastAtMost minimum_def consec_def
        el.rep_eq rep_non_empty_means_seq)
  from min and max show less:"n < m" 
    using One_nat_def Suc_le_lessD \<open>consec i j\<close> add.right_neutral add_Suc_right
      dual_order.trans leD leI consec_def by auto
qed

lemma consec_in_exclusive1:"consec i j \<and> n \<^bold>\<in> i \<longrightarrow> n \<^bold>\<notin> j" 
  using nat_int.consec_lesser nat_int.in_not_in_iff2 by blast

lemma consec_in_exclusive2:"consec i j \<and> n \<^bold>\<in> j \<longrightarrow> n \<^bold>\<notin> i"
  using consec_in_exclusive1 el.rep_eq not_in.rep_eq by blast

lemma consec_un_max:"consec i j \<longrightarrow> maximum j = maximum (i \<squnion> j)"
proof
  assume assm:"consec i j"
  then have "(\<forall>n m. (n \<^bold>\<in> i \<and> m \<^bold>\<in> j \<longrightarrow> n < m))" 
    using nat_int.consec_lesser by blast
  then have "\<forall>n . (n \<^bold>\<in> i \<longrightarrow> n < maximum j)" 
    using assm local.consec_def nat_int.maximum_in by auto
  then have "\<forall>n. (n \<^bold>\<in> i \<squnion> j \<longrightarrow> n \<le> maximum j)" 
    by (metis (no_types, lifting) Rep_nat_int Rep_nat_int_inverse Un_iff assm atLeastAtMost_iff
        bot_nat_int.rep_eq less_imp_le_nat local.consec_def local.not_empty_means_seq 
        nat_int.consec_un nat_int.el.rep_eq nat_int.in_not_in_iff1 nat_int.leq_max_sup')
  then show "maximum j = maximum (i \<squnion> j)" 
    by (metis Rep_nat_int_inverse assm atLeastAtMost_iff bot.extremum_uniqueI
        le_antisym local.consec_def nat_int.consec_un_element2 nat_int.el.rep_eq
        nat_int.leq_max_sup' nat_int.maximum_in nat_int.un_subset2 rep_non_empty_means_seq)
qed

lemma consec_un_min:"consec i j \<longrightarrow> minimum i = minimum (i \<squnion> j)"
proof
  assume assm:"consec i j"
  then have "(\<forall>n m. (n \<^bold>\<in> i \<and> m \<^bold>\<in> j \<longrightarrow> n < m))" 
    using nat_int.consec_lesser by blast
  then have "\<forall>n . (n \<^bold>\<in> j \<longrightarrow> n > minimum i)" 
    using assm local.consec_def nat_int.minimum_in by auto
  then have 1:"\<forall>n. (n \<^bold>\<in> i \<squnion> j \<longrightarrow> n \<ge> minimum i)"  
    using Rep_nat_int Rep_nat_int_inverse Un_iff assm atLeastAtMost_iff bot_nat_int.rep_eq
      less_imp_le_nat local.consec_def local.not_empty_means_seq nat_int.consec_un 
      nat_int.el.rep_eq nat_int.in_not_in_iff1
    by (metis (no_types, lifting) leq_min_inf local.minimum_def)
  from assm have "i \<squnion> j \<noteq> \<emptyset>" 
    by (metis bot.extremum_uniqueI nat_int.consec_def nat_int.un_subset2)
  then show "minimum i = minimum (i \<squnion> j)" 
    by (metis "1" antisym assm atLeastAtMost_iff leq_min_inf nat_int.consec_def 
        nat_int.consec_un_element1 nat_int.el.rep_eq nat_int.minimum_def nat_int.minimum_in
        rep_non_empty_means_seq)
qed

lemma consec_un_defined:
  "consec i j \<longrightarrow> (Rep_nat_int (i \<squnion> j) \<in> {S . (\<exists> (m::nat) n . {m..n }=S) })"
  using Rep_nat_int by auto

lemma consec_un_min_max:
  "consec i j \<longrightarrow> Rep_nat_int(i \<squnion> j) = {minimum i .. maximum j}"
proof
  assume assm:"consec i j"
  then have 1:"minimum j = maximum i +1" 
    by (simp add: nat_int.consec_def)
  have i:"Rep_nat_int i = {minimum i..maximum i}" 
    by (metis Rep_nat_int_inverse assm nat_int.consec_def nat_int.leq_max_sup' nat_int.leq_min_inf'
        rep_non_empty_means_seq)
  have j:"Rep_nat_int j = {minimum j..maximum j}" 
    by (metis Rep_nat_int_inverse assm nat_int.consec_def nat_int.leq_max_sup' nat_int.leq_min_inf'
        rep_non_empty_means_seq)
  show "Rep_nat_int(i \<squnion> j) = {minimum i .. maximum j}" 
    by (metis Rep_nat_int_inverse antisym assm bot.extremum i nat_int.consec_un_max
        nat_int.consec_un_min nat_int.leq_max_sup' nat_int.leq_min_inf' nat_int.un_subset1
        rep_non_empty_means_seq)
qed

lemma consec_un_equality: 
  "(consec i j \<and> k \<noteq> \<emptyset>) 
    \<longrightarrow>( minimum (i \<squnion> j) = minimum (k) \<and> maximum (i \<squnion> j) = maximum (k))
      \<longrightarrow> i \<squnion> j = k"
proof (rule impI)+
  assume cons:"consec i j \<and> k \<noteq> \<emptyset>"
  assume endpoints:" minimum(i \<squnion> j) = minimum(k) \<and> maximum(i \<squnion> j) = maximum(k)"
  have "Rep_nat_int( i \<squnion> j) = {minimum(i \<squnion> j)..maximum(i \<squnion> j)}" 
    by (metis cons leq_max_sup leq_min_inf local.consec_def nat_int.consec_un_element2
        nat_int.maximum_def nat_int.minimum_def nat_int.non_empty_elem_in rep_non_empty_means_seq)
  then have 1:"Rep_nat_int( i \<squnion> j) = {minimum(k) .. maximum(k)}" 
    using endpoints by simp
  have "Rep_nat_int( k) = {minimum(k) .. maximum(k)}" 
    by (metis cons leq_max_sup leq_min_inf nat_int.maximum_def nat_int.minimum_def
        rep_non_empty_means_seq)
  then  show " i \<squnion> j = k" using 1 
    by (metis Rep_nat_int_inverse)
qed

lemma consec_trans_lesser:
  "consec i j \<and> consec j k \<longrightarrow> (\<forall>n m. (n \<^bold>\<in> i \<and> m \<^bold>\<in> k \<longrightarrow> n < m))"
proof (rule allI|rule impI)+
  assume cons:" consec i j \<and> consec j k"
  fix n and m
  assume assump:"n \<^bold>\<in> i \<and> m \<^bold>\<in> k "
  have "\<forall>k . k \<^bold>\<in> j \<longrightarrow> k < m" using consec_lesser assump cons by blast
  hence m_greater:"maximum j < m" using cons maximum_in consec_def by blast
  then show "n < m" 
    by (metis assump cons consec_def dual_order.strict_trans nat_int.consec_lesser
        nat_int.maximum_in)      
qed
  
lemma consec_inter_empty:"consec i j \<Longrightarrow> i \<sqinter> j = \<emptyset>" 
proof -
  assume "consec i j"
  then have "i \<noteq> bot \<and> j \<noteq> bot \<and> maximum i + 1 = minimum j"
    using consec_def by force
  then show ?thesis
    by (metis (no_types) Rep_nat_int_inverse bot_nat_int_def inf_nat_int.rep_eq int_conseq_seq
        nat_int.leq_max_sup nat_int.leq_min_inf nat_int.maximum_def nat_int.minimum_def
        nat_int.rep_non_empty_means_seq)
qed 
  
lemma consec_intermediate1:"consec j k \<and> consec i (j \<squnion> k) \<longrightarrow> consec i j "
proof
  assume assm:"consec j k \<and> consec i (j \<squnion> k)"
  hence min_max_yz:"maximum j +1=minimum k" using consec_def by blast 
  hence min_max_xyz:"maximum i +1 = minimum (j \<squnion> k)" 
      using consec_def assm by blast
  have min_y_yz:"minimum j = minimum (j \<squnion> k)" 
    by (simp add: assm nat_int.consec_un_min)
  hence min_max_xy:"maximum i+1 = minimum j" 
    using min_max_xyz by simp
  thus consec_x_y:"consec i j" using assm consec_def by auto
qed
  
lemma consec_intermediate2:"consec i j \<and> consec (i \<squnion> j) k \<longrightarrow> consec j k "
proof
  assume assm:"consec i j \<and> consec (i \<squnion> j) k"
  hence min_max_yz:"maximum i +1=minimum j" using consec_def by blast 
  hence min_max_xyz:"maximum (i \<squnion> j) +1 = minimum ( k)" 
      using consec_def assm by blast
  have min_y_yz:"maximum j = maximum (i \<squnion> j)" 
    using assm nat_int.consec_un_max by blast
  then have min_max_xy:"maximum j+1 = minimum k" 
    using min_max_xyz by simp
  thus consec_x_y:"consec j k" using assm consec_def by auto
qed

lemma un_assoc: "consec i j \<and> consec j k \<longrightarrow> (i \<squnion> j) \<squnion> k = i \<squnion> (j \<squnion> k)" 
proof 
  assume assm:"consec i j \<and> consec j k"
  from assm have 3:"maximum (i \<squnion> j) = maximum j" 
    using nat_int.consec_un_max by auto
  from assm have 4:"minimum (j \<squnion> k) = minimum (j)" 
    using nat_int.consec_un_min by auto
  have "i \<squnion> j  = Abs_nat_int{minimum i .. maximum j}" 
    by (metis Rep_nat_int_inverse assm nat_int.consec_un_min_max)
  then have 5:"(i \<squnion> j) \<squnion> k = Abs_nat_int{minimum i .. maximum k}" 
    by (metis (no_types, hide_lams) "3" Rep_nat_int_inverse antisym assm bot.extremum
        nat_int.consec_def nat_int.consec_un_min nat_int.consec_un_min_max nat_int.un_subset1)
  have "j \<squnion> k = Abs_nat_int{minimum j .. maximum k}" 
    by (metis Rep_nat_int_inverse assm nat_int.consec_un_min_max)
  then have 6:"i \<squnion> (j \<squnion> k) = Abs_nat_int{minimum i .. maximum k}" 
    by (metis (no_types, hide_lams) "4" Rep_nat_int_inverse antisym assm bot.extremum
        nat_int.consec_def nat_int.consec_un_max nat_int.consec_un_min_max nat_int.un_subset2)
  from 5 and 6 show " (i \<squnion> j) \<squnion> k = i \<squnion> (j \<squnion> k)" by simp
qed

lemma consec_assoc1:"consec j k \<and> consec i (j \<squnion> k) \<longrightarrow> consec (i \<squnion> j) k "
proof
  assume assm:"consec j k \<and> consec i (j \<squnion> k)"
  hence min_max_yz:"maximum j +1=minimum k" using consec_def by blast 
  hence min_max_xyz:"maximum i +1 = minimum (j \<squnion> k)" 
      using consec_def assm by blast
  have min_y_yz:"minimum j = minimum (j \<squnion> k)" 
    by (simp add: assm nat_int.consec_un_min) 
  hence min_max_xy:"maximum i+1 = minimum j" using min_max_xyz by simp
  hence consec_x_y:"consec i j" using assm _consec_def by auto
  hence max_y_xy:"maximum j = maximum (i \<squnion> j)" using consec_lesser assm 
    by (simp add: nat_int.consec_un_max)
  have none_empty:"i \<noteq> \<emptyset> \<and> j \<noteq> \<emptyset> \<and> k \<noteq> \<emptyset>" using assm by (simp add: consec_def)
  hence un_non_empty:"i\<squnion>j \<noteq> \<emptyset>" 
    using bot.extremum_uniqueI consec_x_y nat_int.un_subset2 by force
  have max:"maximum (i\<squnion>j) +1 = minimum k" 
    using min_max_yz max_y_xy by auto  
  thus "consec (i \<squnion> j) k"  using max un_non_empty none_empty consec_def by blast
qed
  
lemma consec_assoc2:"consec i j \<and> consec (i\<squnion> j) k \<longrightarrow> consec i  (j\<squnion> k) "
proof
  assume assm:"consec i j \<and> consec (i\<squnion> j) k"
  hence consec_y_z:"consec j k" using assm consec_def consec_intermediate2 
    by blast
  hence max_y_xy:"maximum j = maximum (i \<squnion> j)" 
    by (simp add: assm nat_int.consec_un_max)  
  have min_y_yz:"minimum j = minimum (j \<squnion> k)" 
    by (simp add: consec_y_z nat_int.consec_un_min)
  have none_empty:"i \<noteq> \<emptyset> \<and> j \<noteq> \<emptyset> \<and> k \<noteq> \<emptyset>" using assm by (simp add: consec_def)
  then have un_non_empty:"j\<squnion>k \<noteq> \<emptyset>" 
    by (metis  bot_nat_int.rep_eq Rep_nat_int_inject consec_y_z  less_eq_nat_int.rep_eq
        un_subset1 subset_empty)
  have max:"maximum (i) +1 = minimum (j\<squnion> k)" 
    using assm min_y_yz consec_def by auto
  thus "consec i ( j \<squnion> k)"  using max un_non_empty none_empty consec_def by blast
qed
  
  
lemma consec_assoc_mult:
  "(i2=\<emptyset>\<or> consec i1 i2 ) \<and> (i3 =\<emptyset> \<or> consec i3 i4) \<and> (consec (i1 \<squnion> i2) (i3 \<squnion> i4)) 
      \<longrightarrow> (i1 \<squnion> i2) \<squnion> (i3 \<squnion> i4) = (i1 \<squnion> (i2 \<squnion> i3)) \<squnion> i4"
proof
  assume assm:"(i2=\<emptyset>\<or> consec i1 i2 ) \<and> (i3 =\<emptyset> \<or> consec i3 i4) 
                \<and> (consec (i1 \<squnion> i2) (i3 \<squnion> i4))"
  hence "(i2=\<emptyset>\<or> consec i1 i2 )" by simp
  thus " (i1 \<squnion> i2) \<squnion> (i3 \<squnion> i4) = (i1 \<squnion> (i2 \<squnion> i3)) \<squnion> i4" 
  proof
    assume empty2:"i2 = \<emptyset>"
    hence only_l1:"(i1 \<squnion> i2) = i1" using un_empty_absorb1 by simp
    from assm have "(i3 =\<emptyset> \<or> consec i3 i4)" by simp
    thus " (i1 \<squnion> i2) \<squnion> (i3 \<squnion> i4) = (i1 \<squnion> (i2 \<squnion> i3)) \<squnion> i4" 
      by (metis Rep_nat_int_inverse assm bot_nat_int.rep_eq empty2 local.union_def 
          nat_int.consec_intermediate1 nat_int.un_assoc only_l1 sup_bot.left_neutral)
  next
    assume consec12:" consec i1 i2"
    from assm have "(i3 =\<emptyset> \<or> consec i3 i4)" by simp
    thus " (i1 \<squnion> i2) \<squnion> (i3 \<squnion> i4) = (i1 \<squnion> (i2 \<squnion> i3)) \<squnion> i4" 
    proof
      assume empty3:"i3 = \<emptyset>"
      hence only_l4:"(i3 \<squnion> i4) = i4 " using un_empty_absorb2 by simp
      have "(i1 \<squnion> (i2 \<squnion> i3)) = i1 \<squnion> i2" using empty3 by (simp add: un_empty_absorb1)
      thus ?thesis by (simp add: only_l4)
    next
      assume  consec34:" consec i3 i4"
      have consec12_3:"consec (i1 \<squnion> i2) i3" 
        using assm consec34 consec_intermediate1 by blast
      show ?thesis 
        by (metis consec12 consec12_3 consec34 consec_intermediate2 un_assoc)
    qed
  qed
qed
  
lemma card_subset_le: "i \<sqsubseteq> i' \<longrightarrow> |i| \<le> |i'|"  
  by (metis bot_nat_int.rep_eq card_mono finite.intros(1) finite_atLeastAtMost 
      less_eq_nat_int.rep_eq local.card'.rep_eq rep_non_empty_means_seq)
  
lemma card_subset_less:"(i::nat_int) < i' \<longrightarrow> |i|<|i'|"  
  by (metis bot_nat_int.rep_eq finite.intros(1) finite_atLeastAtMost less_nat_int.rep_eq
      local.card'.rep_eq psubset_card_mono rep_non_empty_means_seq) 
  
lemma card_empty_zero:"|\<emptyset>| = 0"  
  using Abs_nat_int_inverse empty_type card'.rep_eq bot_nat_int.rep_eq by auto
    
lemma card_non_empty_geq_one:"i \<noteq> \<emptyset> \<longleftrightarrow> |i| \<ge> 1" 
proof
  assume "i \<noteq> \<emptyset>"
  hence "Rep_nat_int i \<noteq> {}" by (metis Rep_nat_int_inverse bot_nat_int.rep_eq)
  hence "card (Rep_nat_int i) > 0" 
    by (metis \<open>i \<noteq> \<emptyset>\<close> card_0_eq finite_atLeastAtMost gr0I rep_non_empty_means_seq)
  thus "|i| \<ge> 1" by (simp add: card'_def) 
next
  assume "|i| \<ge> 1" thus "i \<noteq>\<emptyset>" 
    using card_empty_zero by auto
qed

lemma card_min_max:"i \<noteq> \<emptyset> \<longrightarrow> |i| = (maximum i - minimum i) + 1" 
proof
  assume assm:"i \<noteq> \<emptyset>"
  then have "Rep_nat_int i = {minimum i .. maximum i}" 
    by (metis leq_max_sup leq_min_inf nat_int.maximum_def nat_int.minimum_def
        rep_non_empty_means_seq) 
  then have "card (Rep_nat_int i) = maximum i - minimum i + 1" 
    using Rep_nat_int_inject assm bot_nat_int.rep_eq by fastforce
  then show " |i| = (maximum i - minimum i) + 1"  by simp
qed

lemma card_un_add: " consec i j \<longrightarrow> |i \<squnion> j| = |i| + |j|"
proof 
  assume assm:"consec i j" 
  then have 0:"i \<sqinter> j = \<emptyset>" 
    using nat_int.consec_inter_empty by auto
  then have "(Rep_nat_int i) \<inter> (Rep_nat_int j) = {}" 
    by (metis bot_nat_int.rep_eq inf_nat_int.rep_eq)
  then have 1: 
    "card((Rep_nat_int i)\<union>(Rep_nat_int j))=card(Rep_nat_int i)+card(Rep_nat_int j)"
    by (metis Int_iff add.commute add.left_neutral assm card.infinite card_Un_disjoint
        emptyE le_add1 le_antisym local.consec_def nat_int.card'.rep_eq
        nat_int.card_min_max nat_int.el.rep_eq nat_int.maximum_in nat_int.minimum_in)
  then show "|i \<squnion> j| = |i| + |j|" 
  proof -
    have f1: "i \<noteq> \<emptyset> \<and> j \<noteq> \<emptyset> \<and> maximum i + 1 = minimum j"
      using assm nat_int.consec_def by blast
    then have f2: "Rep_nat_int i \<noteq> {}"
      using Rep_nat_int_inject bot_nat_int.rep_eq by auto
    have "Rep_nat_int j \<noteq> {}"
      using f1 Rep_nat_int_inject bot_nat_int.rep_eq by auto
    then show ?thesis
      using f2 f1 Abs_nat_int_inverse Rep_nat_int 1 local.union_result
        nat_int.union_def nat_int_class.maximum_def nat_int_class.minimum_def
        by force
  qed
qed

lemma singleton:"|i| = 1 \<longrightarrow> (\<exists>n. Rep_nat_int i = {n})"
  using card_1_singletonE card'.rep_eq by fastforce
    
lemma singleton2:" (\<exists>n. Rep_nat_int i = {n}) \<longrightarrow> |i| = 1"
  using card_1_singletonE card'.rep_eq by fastforce
    
    
lemma card_seq:"
  \<forall>i .|i| = x \<longrightarrow> (Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n..n+(x-1)}))" 
proof (induct x)
  show IB:
    "\<forall>i. |i| = 0 \<longrightarrow> (Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n..n+(0-1)}))" 
    by (metis  card_non_empty_geq_one bot_nat_int.rep_eq  not_one_le_zero)
  fix x
  assume IH:
      "\<forall>i. |i| = x \<longrightarrow> Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n..n+(x-1)})"
  show   " \<forall>i. |i| = Suc x \<longrightarrow>
             Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n.. n + (Suc x - 1)})"
  proof (rule allI|rule impI)+
    fix i
    assume assm_IS:"|i| = Suc x"
    show " Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n.. n + (Suc x -1)})"
    proof (cases "x = 0")
      assume "x=0"
      hence "|i| = 1" 
        using assm_IS by auto 
      then have "\<exists>n'. Rep_nat_int i = {n'}" 
        using nat_int.singleton by blast 
      hence "\<exists>n'. Rep_nat_int i = {n'.. n' + (Suc x) -1}"
        by (simp add: \<open>x = 0\<close>)
      thus "Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i = {n.. n + (Suc x - 1)})"
        by simp
    next
      assume x_neq_0:"x \<noteq>0 "
      hence x_ge_0:"x > 0" using gr0I by blast
      from assm_IS have i_is_seq:"\<exists>n m. n \<le> m \<and> Rep_nat_int i = {n..m}" 
        by (metis One_nat_def Suc_le_mono card_non_empty_geq_one le0 rep_non_empty_means_seq)
      obtain n and m where seq_def:" n  \<le> m \<and> Rep_nat_int i = {n..m}" 
        using i_is_seq by auto
      have n_le_m:"n < m"
      proof (rule ccontr)
        assume "\<not>n < m"
        hence "n = m" by (simp add: less_le seq_def)
        hence "Rep_nat_int i = {n}" by (simp add: seq_def)
        hence "x = 0" using assm_IS card'.rep_eq by auto
        thus False by (simp add: x_neq_0)
      qed
      hence "n \<le> (m-1)" by simp
      obtain i' where  i_def:"i' = Abs_nat_int {n..m-1}" by blast
      then have card_i':"|i'| = x" 
        using assm_IS leq_nat_non_empty n_le_m
          nat_int_class.card_min_max nat_int_class.leq_max_sup' nat_int_class.leq_min_inf'
          seq_def by auto
      hence "Rep_nat_int i' = {} \<or> (\<exists>n. Rep_nat_int i' = {n.. n + (x - 1)})" 
        using IH by auto
      hence " (\<exists>n. Rep_nat_int i' = {n.. n + (x - 1)})" using x_neq_0 
        using card.empty card_i' card'.rep_eq by auto
      hence "m-1 = n + x -1" using assm_IS card'.rep_eq seq_def by auto
      hence "m = n +x" using n_le_m x_ge_0 by linarith
      hence "( Rep_nat_int i = {n.. n + (Suc x -1) })" using seq_def by (simp )
      hence "\<exists>n. (Rep_nat_int i = {n.. n + (Suc x -1) })" ..
      then show "Rep_nat_int i = {} \<or> (\<exists>n. Rep_nat_int i ={n.. n + (Suc x-1)})"
        by blast
    qed
  qed
qed
    
lemma rep_single: "Rep_nat_int (Abs_nat_int {m..m}) = {m}"
  by (simp add: Abs_nat_int_inverse)

lemma chop_empty_right: "\<forall>i. N_Chop(i,i,\<emptyset>)"  
  using bot_nat_int.abs_eq nat_int.inter_empty1 nat_int.nchop_def nat_int.un_empty_absorb1
  by auto
    
lemma chop_empty_left: "\<forall>i. N_Chop(i, \<emptyset>, i)"
  using bot_nat_int.abs_eq nat_int.inter_empty2 nat_int.nchop_def nat_int.un_empty_absorb2
  by auto
    
lemma chop_empty : "N_Chop(\<emptyset>,\<emptyset>,\<emptyset>)"
  by (simp add: chop_empty_left)
    
lemma chop_always_possible:"\<forall>i.\<exists> j k. N_Chop(i,j,k)" 
  by (metis  chop_empty_right)
    
lemma chop_add1: "N_Chop(i,j,k) \<longrightarrow> |i| = |j| + |k|"
  using card_empty_zero card_un_add un_empty_absorb1 un_empty_absorb2 nchop_def by auto
    
lemma chop_add2:"|i| = x+y \<longrightarrow> (\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y)" 
proof
  assume assm:"|i| = x+y"
  show "(\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y)"
  proof (cases "x+y = 0")
    assume "x+y =0"
    then show "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" 
      using assm chop_empty_left nat_int.chop_add1 by fastforce
  next 
    assume "x+y \<noteq> 0"
    show "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" 
    proof (cases "x = 0")
      assume x_eq_0:"x=0"
      then show "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" 
        using assm nat_int.card_empty_zero nat_int.chop_empty_left by auto
    next
      assume x_neq_0:"x \<noteq>0"
      show "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" 
      proof (cases "y = 0")
        assume y_eq_0:"y=0"
        then show "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" 
          using assm nat_int.card_empty_zero nat_int.chop_empty_right by auto
      next
        assume y_neq_0:"y \<noteq> 0"
        have rep_i:"\<exists>n. Rep_nat_int i = {n..n + (x+y)-1}" 
          using assm card'.rep_eq card_seq x_neq_0 by fastforce
        obtain n where n_def:"Rep_nat_int i = {n..n + (x+y) -1}" 
          using rep_i by auto
        have n_le:"n \<le> n+(x-1)" by simp
        have x_le:"n+(x) \<le> n + (x+y)-1" using y_neq_0 by linarith
        obtain j  where j_def:" j = Abs_nat_int {n..n+(x-1)}" by blast
        from n_le have j_in_type:
          "{n..n+(x-1)} \<in> {S . (\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={}}"
          by blast
        obtain k where k_def:" k =Abs_nat_int {n+x..n+(x+y)-1}" by blast
        from x_le have k_in_type:
          "{n+x..n+(x+y)-1} \<in> {S.(\<exists> (m::nat) n . m \<le> n \<and> {m..n }=S) \<or> S={}}"
          by blast
        have consec: "consec j k" 
          by (metis j_def k_def One_nat_def Suc_leI add.assoc diff_add n_le consec_def
              leq_max_sup' leq_min_inf' leq_nat_non_empty neq0_conv x_le x_neq_0)
        have union:"i = j \<squnion> k" 
          by (metis Rep_nat_int_inverse consec j_def k_def n_def n_le nat_int.consec_un_min_max
              nat_int.leq_max_sup' nat_int.leq_min_inf' x_le)
        have disj:"j \<sqinter> k = \<emptyset>" using consec by (simp add: consec_inter_empty)
        have chop:"N_Chop(i,j,k)" using consec union disj nchop_def by simp
        have card_j:"|j| = x" 
          using Abs_nat_int_inverse j_def n_le card'.rep_eq x_neq_0 by auto
        have card_k:"|k| = y"
          using Abs_nat_int_inverse k_def x_le card'.rep_eq x_neq_0 y_neq_0 by auto
        have "N_Chop(i,j,k) \<and> |j| = x \<and> |k| = y" using chop card_j card_k by blast
        then show "\<exists> j k. N_Chop(i,j,k) \<and> |j|=x \<and> |k|=y" by blast
      qed
    qed
  qed
qed
  
lemma chop_single:"(N_Chop(i,j,k) \<and> |i| = 1) \<longrightarrow> ( |j| =0 \<or> |k|=0)"
  using chop_add1 by force
    
lemma chop_leq_max:"N_Chop(i,j,k) \<and> consec j k \<longrightarrow> 
  (\<forall>n . n \<in> Rep_nat_int i \<and> n \<le> maximum j \<longrightarrow> n \<in> Rep_nat_int j)" 
  by (metis Un_iff le_antisym less_imp_le_nat nat_int.consec_def nat_int.consec_lesser
      nat_int.consec_un nat_int.el.rep_eq nat_int.maximum_in nat_int.nchop_def
      nat_int.not_in.rep_eq)
    
lemma chop_geq_min:"N_Chop(i,j,k) \<and> consec j k \<longrightarrow> 
  (\<forall>n . n \<in> Rep_nat_int i \<and> minimum k \<le> n \<longrightarrow> n \<in> Rep_nat_int k)" 
  by (metis atLeastAtMost_iff bot_nat_int.rep_eq equals0D leq_max_sup leq_min_inf 
      nat_int.consec_def nat_int.consec_un_max nat_int.maximum_def nat_int.minimum_def
      nat_int.nchop_def rep_non_empty_means_seq)
     
lemma chop_min:"N_Chop(i,j,k) \<and> consec j k \<longrightarrow> minimum i = minimum j" 
  using nat_int.consec_un_min nat_int.nchop_def by auto
  
lemma chop_max:"N_Chop(i,j,k) \<and> consec j k \<longrightarrow> maximum i = maximum k"
  using nat_int.consec_un_max nat_int.nchop_def by auto
  
lemma chop_assoc1:
  "N_Chop(i,i1,i2) \<and> N_Chop(i2,i3,i4) 
    \<longrightarrow> (N_Chop(i, i1 \<squnion> i3, i4) \<and> N_Chop(i1 \<squnion> i3, i1, i3))" 
proof 
  assume assm:"N_Chop(i,i1,i2) \<and> N_Chop(i2,i3,i4)"
  then have chop_def:"(i =  i1 \<squnion> i2   \<and>
        (i1 = \<emptyset> \<or>  i2 = \<emptyset> \<or> ( consec i1 i2)))"
    using nchop_def by blast
  hence "(i1 = \<emptyset> \<or>  i2 = \<emptyset> \<or> ( consec i1 i2))" by simp 
  then show "N_Chop(i, i1 \<squnion> i3, i4) \<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
  proof 
    assume empty:"i1 = \<emptyset>"
    then show "N_Chop(i,i1 \<squnion> i3, i4) \<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
      by (simp add: assm chop_def nat_int.chop_empty_left nat_int.un_empty_absorb2)
  next
    assume "i2 = \<emptyset> \<or> ( consec i1 i2)"
    then show "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
    proof 
      assume empty:"i2 = \<emptyset>"
      then show "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
        by (metis assm bot.extremum_uniqueI nat_int.chop_empty_right nat_int.nchop_def
            nat_int.un_empty_absorb2 nat_int.un_subset1)
    next
      assume " consec i1 i2"
      then have consec_i1_i2:"i1 \<noteq>\<emptyset> \<and> i2 \<noteq>\<emptyset> \<and> maximum i1 +1 = minimum i2" 
        using consec_def by blast
      from assm have "i3 = \<emptyset> \<or> i4 = \<emptyset> \<or> consec i3 i4" 
        using nchop_def by blast
      then show "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
      proof
        assume i3_empty:"i3 = \<emptyset>"
        then show "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
          using assm nat_int.chop_empty_right nat_int.nchop_def nat_int.un_empty_absorb2
            by auto
      next 
        assume "i4 = \<emptyset> \<or> consec i3 i4"
        then show "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
        proof
          assume i4_empty:"i4 = \<emptyset>"
          then show "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
            using assm nat_int.chop_empty_right nat_int.nchop_def by auto
        next
          assume consec_i3_i4:"consec i3 i4"
          then show "N_Chop(i, i1 \<squnion> i3, i4)\<and> N_Chop(i1 \<squnion> i3, i1, i3)" 
            by (metis \<open>consec i1 i2\<close> assm nat_int.consec_assoc1 nat_int.consec_intermediate1
                nat_int.nchop_def nat_int.un_assoc)
        qed
      qed
    qed
  qed
qed
  
lemma chop_assoc2:
  "N_Chop(i,i1,i2) \<and> N_Chop(i1,i3,i4) 
    \<longrightarrow> N_Chop(i, i3, i4 \<squnion> i2) \<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
proof 
  assume assm: "N_Chop(i,i1,i2) \<and> N_Chop(i1,i3,i4)"
  hence "(i1 = \<emptyset> \<or>  i2 = \<emptyset> \<or> ( consec i1 i2))" 
    using nchop_def by blast 
  then show "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)"
  proof
    assume i1_empty:"i1 = \<emptyset>"
   then show "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
     by (metis assm nat_int.chop_empty_left nat_int.consec_un_not_elem1 nat_int.in_not_in_iff1
         nat_int.nchop_def nat_int.non_empty_elem_in nat_int.un_empty_absorb1)
  next
    assume "i2 = \<emptyset> \<or> consec i1 i2"
    then show "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)"
    proof
      assume i2_empty:"i2=\<emptyset>"
      then show "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
        using assm nat_int.chop_empty_right nat_int.nchop_def by auto
    next
      assume consec_i1_i2:"consec i1 i2"
      from assm have "(i3 = \<emptyset> \<or>  i4 = \<emptyset> \<or> ( consec i3 i4))" 
        by (simp add: nchop_def)
      then show "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)"
      proof
        assume i3_empty:"i3=\<emptyset>"
        then show "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
          using assm nat_int.chop_empty_left nat_int.nchop_def by auto
      next
        assume " i4 = \<emptyset> \<or> ( consec i3 i4)"
        then show "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
        proof
          assume i4_empty:"i4=\<emptyset>"
          then show "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
            using assm nat_int.nchop_def nat_int.un_empty_absorb1 nat_int.un_empty_absorb2
            by auto
        next
          assume consec_i3_i4:"consec i3 i4"
          then show "N_Chop(i, i3, i4 \<squnion> i2)\<and> N_Chop(i4 \<squnion> i2, i4,i2)" 
            by (metis assm consec_i1_i2 nat_int.consec_assoc2 nat_int.consec_intermediate2
                nat_int.nchop_def nat_int.un_assoc)
        qed
      qed
    qed
  qed
qed
  
lemma chop_subset1:"N_Chop(i,j,k) \<longrightarrow> j \<sqsubseteq> i"
  using nat_int.chop_empty_right nat_int.nchop_def nat_int.un_subset1 by auto
    
lemma chop_subset2:"N_Chop(i,j,k) \<longrightarrow> k \<sqsubseteq> i" 
  using nat_int.chop_empty_left nat_int.nchop_def nat_int.un_subset2 by auto
    
end
end
