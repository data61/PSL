subsection \<open>Definition of \texorpdfstring{$\Psi$}{Psi}\label{sec:psi}\<close>

theory Psi
  imports SortKeys "HOL-Eisbach.Eisbach"
begin

fun extended_size :: "('a sort_key) extended \<Rightarrow> nat"
  where
    "extended_size \<lbrakk>x\<rbrakk> = size x" |
    "extended_size _ = 0"

lemma extended_simps [simp]:
  "(\<turnstile> < x) = (x \<noteq> \<turnstile>)"
  "(\<lbrakk>x'\<rbrakk> < \<lbrakk>y'\<rbrakk>) = (x' < y')"
  "\<lbrakk>x'\<rbrakk> < \<stileturn>"
  "\<not>(\<lbrakk>x'\<rbrakk> < \<turnstile>)"
  "\<not>(\<stileturn> < x)"
  "\<turnstile> \<le> x"
  "(\<lbrakk>x'\<rbrakk> \<le> \<lbrakk>y'\<rbrakk>) = ((x' :: 'a :: linorder) \<le> y')"
  "x \<le> \<stileturn>"
  "\<not>(\<lbrakk>x'\<rbrakk> \<le> \<turnstile>)"
  "(\<stileturn> \<le> x) = (x = \<stileturn>)"
  by (case_tac [!] x, simp_all add:less_extended_def less_eq_extended_def le_less)

fun int_size where "int_size (l,u) = max (extended_size l) (extended_size u)"

lemma position_cases:
  assumes "\<And> y z. x = \<lbrakk>NonFinal (y,Left) z\<rbrakk> \<Longrightarrow> p"
  assumes "\<And> y z. x = \<lbrakk>NonFinal (y,Right) z\<rbrakk> \<Longrightarrow> p"
  assumes "\<And> y. x = \<lbrakk>Final y\<rbrakk> \<Longrightarrow> p"
  assumes "x = \<turnstile> \<Longrightarrow> p"
  assumes "x = \<stileturn> \<Longrightarrow> p"
  shows "p"
  by (metis assms embed_dir.cases extended_size.cases sort_key_embedding.cases)

fun derive_pos ::
  "('a :: linorder) \<times> sort_dir \<Rightarrow> 'a sort_key extended \<Rightarrow> 'a sort_key extended"
  where
    "derive_pos h \<lbrakk>NonFinal x y\<rbrakk> = 
      (if h < x then \<stileturn> else (if x < h then \<turnstile> else \<lbrakk>y\<rbrakk>))" |
    "derive_pos h \<lbrakk>Final x\<rbrakk> = 
      (if fst h < x \<or> fst h = x \<and> snd h = Left then \<stileturn> else \<turnstile>)" |
    "derive_pos _ \<turnstile> = \<turnstile>" |
    "derive_pos _ \<stileturn> = \<stileturn>"

lemma derive_pos_mono: "x \<le> y \<Longrightarrow> derive_pos h x \<le> derive_pos h y"
  apply (cases h, cases "snd h")
  apply (rule_tac [!] position_cases [where x=x])
  apply (rule_tac [!] position_cases [where x=y])
  by (simp_all, auto)

fun \<gamma> :: "('a :: linorder) position \<Rightarrow> sort_dir \<Rightarrow> 'a \<times> sort_dir"
  where
    "\<gamma> \<lbrakk>NonFinal x y\<rbrakk> _ = x" |
    "\<gamma> \<lbrakk>Final x\<rbrakk> d = (x,d)" |
    "\<gamma> \<turnstile> _ = undefined" |
    "\<gamma> \<stileturn> _ = undefined"

fun derive_left  where
  "derive_left (l, u) = (derive_pos (\<gamma> l Right) l, derive_pos (\<gamma> l Right) u)"

fun derive_right where
  "derive_right (l, u) = (derive_pos (\<gamma> u Left) l, derive_pos (\<gamma> u Left) u)"

fun is_interval where "is_interval (l,u) = (l < u)"

fun elem where "elem x (l,u) = (l < x \<and> x < u)"

fun subset where "subset (l,u) (l',u') = (l' \<le> l \<and> u \<le> u')"

method interval_split for x :: "('a :: linorder) position \<times> 'a position" = 
  (case_tac [!] x, 
   rule_tac [!] position_cases [where x="fst x"], 
   rule_tac [!] position_cases [where x="snd x"])

lemma derive_size:
  "\<lbrakk>Final i\<rbrakk> \<le> fst x \<and> is_interval x \<Longrightarrow> int_size (derive_left x) < int_size x" 
  "snd x \<le> \<lbrakk>Final i\<rbrakk> \<and> is_interval x \<Longrightarrow> int_size (derive_right x) < int_size x"
  by (interval_split x, simp_all add:less_SucI)

lemma derive_interval:
  "\<lbrakk>Final i\<rbrakk> \<le> fst x \<Longrightarrow> is_interval x \<Longrightarrow> is_interval (derive_left x)"
  "snd x \<le> \<lbrakk>Final i\<rbrakk> \<Longrightarrow> is_interval x \<Longrightarrow> is_interval (derive_right x)"
  by (interval_split x, simp_all, auto)

function \<Psi> :: "('a :: linorder) position \<times> 'a position \<Rightarrow> 'a \<Rightarrow> 'a sort_key"
  where
    "\<Psi> (l,u) i = Final i"
      if "l < \<lbrakk>Final i\<rbrakk> \<and> \<lbrakk>Final i\<rbrakk> < u" |
    "\<Psi> (l,u) i = NonFinal (\<gamma> l Right) (\<Psi> (derive_left (l,u)) i)" 
      if "\<lbrakk>Final i\<rbrakk> \<le> l \<and> l < u" |
    "\<Psi> (l,u) i = NonFinal (\<gamma> u Left) (\<Psi> (derive_right (l,u)) i)" 
      if "u \<le> \<lbrakk>Final i\<rbrakk> \<and> l < u" |
    "\<Psi> (l,u) i = undefined" if "u \<le> l"
  by (metis leI old.prod.exhaust, auto)

termination
  apply (relation "measure (\<lambda>(p,i). int_size p)", simp)
  using derive_size by fastforce+

proposition psi_elem: "is_interval x \<Longrightarrow> elem \<lbrakk>\<Psi> x i\<rbrakk> x"
proof (induct "int_size x" arbitrary:x rule: nat_less_induct)
  case 1
  consider (a) "\<lbrakk>Final i\<rbrakk> \<le> fst x" | (b) "elem \<lbrakk>Final i\<rbrakk> x" | (c) "snd x \<le> \<lbrakk>Final i\<rbrakk>"
    using not_le by (metis elem.simps prod.collapse)
  then show ?case
  proof (cases)
    case a
    hence "elem  \<lbrakk>\<Psi> (derive_left x) i\<rbrakk> (derive_left x)"
      by (metis 1 derive_size(1) derive_interval(1))
    then show ?thesis using a "1"(2)
      by (interval_split x, simp_all del:\<Psi>.simps, auto)
  next
    case b
    then show ?thesis by (cases x, simp)
  next
    case c 
    hence "elem  \<lbrakk>\<Psi> (derive_right x) i\<rbrakk> (derive_right x)"
      by (metis 1 derive_size(2) derive_interval(2))
    then show ?thesis using c "1"(2)
      by (interval_split x, simp_all del:\<Psi>.simps, auto)
  qed
qed

proposition psi_mono:
  assumes "i1 < i2"
  shows "is_interval x \<Longrightarrow> \<Psi> x i1 < \<Psi> x i2"
proof (induct "int_size x" arbitrary:x rule: nat_less_induct)
  case 1
  have a:"\<lbrakk>Final i1\<rbrakk> < \<lbrakk>Final i2\<rbrakk>"
    using assms by auto
  then consider 
    (a) "\<lbrakk>Final i1\<rbrakk> \<le> fst x \<and> \<lbrakk>Final i2\<rbrakk> \<le> fst x" | 
    (b) "\<lbrakk>Final i1\<rbrakk> \<le> fst x \<and> elem \<lbrakk>Final i2\<rbrakk> x" | 
    (c) "\<lbrakk>Final i1\<rbrakk> \<le> fst x \<and> snd x \<le> \<lbrakk>Final i2\<rbrakk>" |
    (d) "elem \<lbrakk>Final i1\<rbrakk> x  \<and> elem \<lbrakk>Final i2\<rbrakk> x" |
    (e) "elem \<lbrakk>Final i1\<rbrakk> x \<and> snd x \<le> \<lbrakk>Final i2\<rbrakk>" |
    (f) "snd x \<le> \<lbrakk>Final i2\<rbrakk> \<and> snd x \<le> \<lbrakk>Final i1\<rbrakk>" 
    using assms "1"(2) apply (cases x) 
    by (metis (mono_tags, hide_lams) dual_order.strict_trans elem.simps
        fst_conv leI snd_conv)
  then show ?case
  proof (cases)
    case a
    hence "\<Psi> (derive_left x) i1  < \<Psi> (derive_left x) i2"
      by (metis 1 derive_size(1) derive_interval(1))
    thus ?thesis using a "1"(2) by (cases x, simp)
  next
    case b
    thus ?thesis using "1"(2) apply (cases x, simp) 
      by (rule_tac [!] position_cases [where x="fst x"], simp_all)
  next
    case c
    show ?thesis
    proof (cases "\<gamma> (fst x) Right = \<gamma> (snd x) Left")
      case True 
      have e:"is_interval (derive_left x)" using c "1"(2) derive_interval(1) by blast
      have f:"derive_left x = derive_right x" using True by (cases x, simp)
      have h:"\<Psi> (derive_left x) i1 < \<Psi> (derive_right x) i2"
        apply (cases x, simp only: f) 
        by (metis "1.hyps" "1.prems" c derive_size(2) e f)
      show ?thesis using c "1"(2) h True by (cases x, simp)
    next
      case False
      hence "\<gamma> (fst x) Right < \<gamma> (snd x) Left" using "1"(2) c
      by (interval_split x, simp_all, auto)
      then show ?thesis using c "1"(2) by (cases x, simp)
    qed
  next
    case d
    thus ?thesis using "1"(2) a by (cases x, simp)
  next
    case e
    thus ?thesis using "1"(2) apply (cases x, simp) 
      by (rule_tac [!] position_cases [where x="snd x"], simp_all del:\<Psi>.simps)
  next
    case f
    hence b:"\<Psi> (derive_right x) i1  < \<Psi> (derive_right x) i2" 
      by (metis 1 derive_size(2) derive_interval(2))
    thus ?thesis using f "1"(2) by (cases x, simp)
  qed
qed

proposition psi_narrow:
  "elem \<lbrakk>\<Psi> x' i\<rbrakk> x \<Longrightarrow> subset x x' \<Longrightarrow> \<Psi> x' i = \<Psi> x i" 
proof (induct "int_size x'" arbitrary: x x' rule: nat_less_induct)
  case 1
  have a: "is_interval x" using "1"(2)
    by (metis dual_order.strict_trans elem.elims(2) is_interval.simps)
  have d: "is_interval x'" using a "1"(3) apply (cases x', cases x, simp) by auto
  consider
    (before) "\<lbrakk>Final i\<rbrakk> \<le> fst x'" |
    (between) "elem \<lbrakk>Final i\<rbrakk> x'" | 
    (after) "snd x' \<le> \<lbrakk>Final i\<rbrakk>" using 1 apply simp
    by (metis elem.simps leI prod.collapse)
  then show ?case
  proof (cases)
    case before
    have b: "\<lbrakk>Final i\<rbrakk> \<le> fst x" using before 1 apply (cases x)
      by (metis dual_order.trans fst_conv subset.elims(2))
    obtain z where z_def: "\<Psi> x' i = NonFinal (\<gamma> (fst x') Right) z" 
      using before d apply (cases x') by simp
    have c:"\<gamma> (fst x') Right = \<gamma> (fst x) Right"
      using "1"(3) z_def "1"(2) apply (cases x, cases x', simp)
      apply (rule_tac [!] position_cases [where x="fst x"])
      apply (rule_tac [!] position_cases [where x="fst x'"])
      using before by (simp_all del:\<Psi>.simps, auto)
    have c1:"subset (derive_left x) (derive_left x')"
      using c "1"(3) by (cases x, cases x', simp add:derive_pos_mono)
    have g:"z = \<Psi> (derive_left x') i" using z_def before d by (cases x', simp)
    have "elem \<lbrakk>NonFinal (\<gamma> (fst x) Right) z\<rbrakk> x" 
      using "1"(2) z_def by (simp add: c)
    hence "elem \<lbrakk>z\<rbrakk> (derive_left x)" using before b
      by (interval_split x, simp_all del:\<Psi>.simps, auto)
    hence "\<Psi> (derive_left x') i = \<Psi> (derive_left x) i"
      using "1"(1) before d c1 apply (simp only:g)
      by (metis (no_types) derive_size(1))
    thus ?thesis using before b a d c by (cases x, cases x', simp)
  next
    case between
    thus ?thesis using 1 by (cases x, cases x', auto) 
  next
    case after
    have b: "snd x \<le> \<lbrakk>Final i\<rbrakk>" using after 1 apply (cases x) 
      by (metis (mono_tags, hide_lams) dual_order.trans prod.exhaust_sel
          subset.simps)
    obtain z where z_def:"\<Psi> x' i = NonFinal (\<gamma> (snd x') Left) z" 
      using after d by (cases x', simp)
    have c:"\<gamma> (snd x') Left = \<gamma> (snd x) Left"
      using "1"(3) z_def "1"(2) apply (simp, cases x, cases x')
      apply (rule_tac [!] position_cases [where x="snd x"])
      apply (rule_tac [!] position_cases [where x="snd x'"]) using after
      by (simp_all del:\<Psi>.simps, auto)
    have c1:"subset (derive_right x) (derive_right x')"
      using c "1"(3) by (cases x, cases x', simp add:derive_pos_mono)
    have g:"z = \<Psi> (derive_right x') i" using z_def after d by (cases x', simp)
    have "elem \<lbrakk>NonFinal (\<gamma> (snd x) Left) z\<rbrakk> x" 
      using "1"(2) z_def by (simp add: c)
    hence "elem \<lbrakk>z\<rbrakk> (derive_right x)" using after b
      by (interval_split x, simp_all del:\<Psi>.simps, auto)
    hence "\<Psi> (derive_right x') i = \<Psi> (derive_right x) i"
      using "1"(1) after d c1 apply (simp only:g)   
      by (metis (no_types) derive_size(2))
    thus ?thesis using after b a d c by (cases x, cases x', simp)
  qed
qed

definition preserve_order :: "'a :: linorder \<Rightarrow> 'a \<Rightarrow> 'b :: linorder \<Rightarrow> 'b \<Rightarrow> bool"
  where "preserve_order x y u v \<equiv> (x < y \<longrightarrow> u < v) \<and> (x > y \<longrightarrow> u > v)"

proposition psi_preserve_order:
  fixes l l' u u' i i'
  assumes "elem \<lbrakk>\<Psi> (l, u) i\<rbrakk> (l',u')"
  assumes "elem \<lbrakk>\<Psi> (l', u') i'\<rbrakk> (l, u)"
  shows "preserve_order i i' \<lbrakk>\<Psi> (l,u) i\<rbrakk> \<lbrakk>\<Psi> (l', u') i'\<rbrakk>"
proof -
  have "l < u" using assms(2) by auto
  hence a:"elem \<lbrakk>\<Psi> (l, u) i\<rbrakk> (max l l', min u u')"
    using assms(1) psi_elem by fastforce
  hence b:"\<Psi> (l,u) i = \<Psi> (max l l', min u u') i"
    by (simp add: psi_narrow)
  have "l' < u'" using assms(1) by auto
  hence "elem \<lbrakk>\<Psi> (l',u') i'\<rbrakk> (max l l', min u u')"
    using assms(2) psi_elem by fastforce
  hence c:"\<Psi> (l',u') i' = \<Psi> (max l l', min u u') i'"
    by (simp add: psi_narrow)
  hence "max l l' < min u u'" using a min_def by auto
  then show ?thesis apply (simp only: preserve_order_def b c)
    using psi_mono extended_simps(2) is_interval.simps by blast
qed

end
