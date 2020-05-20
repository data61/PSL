(*  Title:      ListPre.thy
    Author:     Ludovic Henrio and Florian Kammuller, 2006

List lemmata and other general stuff as preparation for ASP.
*)

section \<open>List features\<close>

theory ListPre
imports Main
begin

lemma drop_lem[rule_format]: 
  fixes n :: nat and l :: "'a list" and g :: "'a list"
  assumes "drop n l = drop n g" and "length l = length g" and "n < length g"
  shows "l!n = g!n"
proof -
  from assms(2-3) have "n < length l" by simp
  from Cons_nth_drop_Suc[OF this] Cons_nth_drop_Suc[OF assms(3)] assms(1) 
  have "l!n # drop (Suc n) l = g!n # drop (Suc n) g" by simp
  thus ?thesis by simp
qed

lemma mem_append_lem': "x \<in> set (l @ [y]) \<Longrightarrow> x \<in> set l \<or> x = y"
  by auto

lemma nth_last: "length l = n \<Longrightarrow> (l @ [x])!n = x"
  by auto

lemma take_n:
  fixes n :: nat and l :: "'a list" and g :: "'a list"
  assumes "take n l = take n g" and "Suc n \<le> length g" and "length l = length g"
  shows "take (Suc n) (l[n := g!n]) = take (Suc n) g"
proof -
  from assms(2) have ng: "n < length g" by simp
  with assms(3) have nlupd: "n < length (l[n := g!n])" by simp
  hence nl: "n < length l" by simp
  from 
    sym[OF assms(1)] id_take_nth_drop[OF ng] take_Suc_conv_app_nth[OF nlupd]
    nth_list_update_eq[OF nl] take_Suc_conv_app_nth[OF ng]
    upd_conv_take_nth_drop[OF nl] assms(2-3)
  show ?thesis by simp
qed

lemma drop_n_lem:
  fixes n :: nat and l :: "'a list"
  assumes "Suc n \<le> length l"
  shows "drop (Suc n) (l[n := x]) = drop (Suc n) l"
proof -
  from assms have "n < length l" by simp
  from 
    upd_conv_take_nth_drop[OF this] drop_Suc[of n "l[n := x]"] 
    drop_Suc[of n l] assms
  show ?thesis by (simp,(subst drop_tl)+, simp)
qed

lemma drop_n: 
  fixes n :: nat and l :: "'a list" and g :: "'a list"
  assumes "drop n l = drop n g" and "Suc n \<le> length g" and "length l = length g"
  shows "drop (Suc n) (l[n := g!n]) = drop (Suc n) g"
proof -
  from assms(2-3) have "Suc n \<le> length l" by simp
  from drop_n_lem[OF this] assms(1) show ?thesis
    by (simp, (subst drop_Suc)+, (subst drop_tl)+, simp)
qed

lemma nth_fst[rule_format]: "length l = n + 1 \<longrightarrow> (l @ [x])!0 = l!0" 
  by (induct l, simp_all)

lemma nth_zero_app: 
  fixes l :: "'a list" and x :: 'a and y :: 'a
  assumes "l \<noteq> []" and "l!0 = x"
  shows"(l @ [y])!0 = x"
proof -
  have "l \<noteq> [] \<and> l!0 = x \<longrightarrow> (l @ [y])!0 = x"
    by (induct l, simp_all)
  with assms show ?thesis by simp
qed

lemma rev_induct2[consumes 1]:
  fixes xs :: "'a list" and ys :: "'a list" and P :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  assumes 
  "length xs = length ys" and "P [] []" and
  "\<And>x xs y ys. \<lbrakk> length xs = length ys; P xs ys \<rbrakk> \<Longrightarrow> P (xs @ [x]) (ys @ [y])"
  shows "P xs ys"
proof (simplesubst rev_rev_ident[symmetric])
  from assms(1) have lrev: "length (rev xs) = length (rev ys)" by simp
  from assms have "P (rev (rev xs))(rev (rev ys))" 
    by (induct rule: list_induct2[OF lrev], simp_all)
  thus "P xs (rev (rev ys))" by simp
qed

lemma list_induct3: (* Similar to induction for 2: see ML "thm \"list_induct2\""; *)
  "\<And>ys zs. \<lbrakk> length xs = length ys; length zs = length xs; P [] [] [];
              \<And>x xs y ys z zs. \<lbrakk> length xs = length ys; 
                                    length zs = length xs; P xs ys zs \<rbrakk>
                                 \<Longrightarrow> P (x # xs)(y # ys)(z # zs) 
  \<rbrakk> \<Longrightarrow> P xs ys zs"
proof (induct xs, simp)
  case (Cons a xs ys zs) 
  from \<open>length (a#xs) = length ys\<close> \<open>length zs = length (a#xs)\<close> 
  have "ys \<noteq> [] \<and> zs \<noteq> []" by auto
  then obtain b ly c lz where "ys = b#ly" and "zs = c#lz"
    by (auto simp: neq_Nil_conv)
  with \<open>length (a#xs) = length ys\<close> \<open>length zs = length (a#xs)\<close> 
  obtain "length xs = length ly" and "length lz = length xs" 
    by auto
  from 
    Cons(5)[OF this Cons(1)[OF this \<open>P [] [] []\<close>]] 
    Cons(5) \<open>ys = b#ly\<close> \<open>zs = c#lz\<close> 
  show ?case by simp
qed

primrec list_insert :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "list_insert (ah#as) i a = 
  (case i of 
        0      \<Rightarrow> a#ah#as
       |Suc j  \<Rightarrow> ah#(list_insert as j a))" |

  "list_insert [] i a = [a]"

lemma insert_eq[simp]: "\<forall>i\<le>length l. (list_insert l i a)!i = a"
  by (induct l, simp, intro strip, simp split: nat.split)

lemma insert_gt[simp]: "\<forall>i\<le>length l. \<forall>j<i. (list_insert  l i a)!j = l!j"
proof (induct l, simp)
  case (Cons x l) thus ?case
  proof (auto split: nat.split)
    fix n j assume "n \<le> length l" and "j < Suc n"
    with Cons(1) show "(x#(list_insert l n a))!j = (x#l)!j"
      by (cases j) simp_all
  qed
qed

lemma insert_lt[simp]: "\<forall>j\<le>length l. \<forall>i\<le>j. (list_insert l i a)!Suc j = l!j"
proof (induct l, simp)
  case (Cons x l) thus ?case
  proof (auto split: nat.split)
    fix n j assume "j \<le> Suc (length l)" and "Suc n \<le> j" 
    with Cons(1) show "(list_insert l n a)!j = l!(j - Suc 0)"
      by (cases j) simp_all
  qed
qed

lemma insert_first[simp]: "list_insert l 0 b = b#l"
  by (induct l, simp_all)

lemma insert_prepend[simp]: 
  "i = Suc j \<Longrightarrow> list_insert (a#l) i b = a # list_insert l j b"
  by auto

lemma insert_lt2[simp]: "\<forall>j. \<forall>i\<le>j. (list_insert  l i a)!Suc j = l!j"
proof (induct l, simp)
  case (Cons x l) thus ?case
  proof (auto split: nat.split)
    fix n j assume "Suc n \<le> j" 
    with Cons(1) show "(list_insert l n a)!j = l!(j - Suc 0)"
      by (cases j) simp_all
  qed
qed

lemma insert_commute[simp]: 
  "\<forall>i\<le>length l. (list_insert (list_insert l i b) 0 a) =
                 (list_insert (list_insert l 0 a ) (Suc i) b)"
  by (induct l, auto split: nat.split)

lemma insert_length': "\<And>i x. length (list_insert l i x) = length (x#l)"
  by (induct l, auto split: nat.split)

lemma insert_length[simp]: "length (list_insert l i b) = length (list_insert l j c)"
  by (simp add: insert_length')

lemma insert_select[simp]: "the ((f(l \<mapsto> t)) l) = t"
  by auto

lemma dom_insert[simp]: "l \<in> dom f \<Longrightarrow> dom (f(l \<mapsto> t)) = dom f"
  by auto

lemma insert_select2[simp]: "l1 \<noteq> l2 \<Longrightarrow> ((f(l1 \<mapsto> t)) l2) = (f l2)"
  by auto

lemma the_insert_select[simp]: 
  "\<lbrakk> l2 \<in> dom f; l1 \<noteq> l2 \<rbrakk> \<Longrightarrow>  the ((f(l1 \<mapsto> t)) l2) =  the (f l2)"
  by auto

lemma insert_dom_eq: "dom f = dom f' \<Longrightarrow> dom (f(l \<mapsto> x)) = dom (f'(l \<mapsto> x'))"
  by auto

lemma insert_dom_less_eq: 
  "\<lbrakk> x \<notin> dom f; x \<notin> dom f'; dom (f(x \<mapsto> y)) = dom (f'(x \<mapsto> y')) \<rbrakk> 
  \<Longrightarrow> dom f = dom f'"
  by auto

lemma one_more_dom[rule_format]: 
  "\<forall>l\<in>dom f . \<exists>f'. f = f'(l \<mapsto> the(f l)) \<and> l \<notin> dom f'"
proof
  fix l assume "l \<in> dom f"
  hence "\<And>la. f la = ((\<lambda>la. if la = l then None else f la)(l \<mapsto> the (f l))) la"
    by auto
  hence "f = (\<lambda>la. if la = l then None else f la)(l \<mapsto> the (f l))"
    by (rule ext)
  thus "\<exists>f'. f = f'(l \<mapsto> the(f l) ) \<and> l \<notin> dom f'" by auto
qed
 
end
