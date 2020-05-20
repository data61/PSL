subsection \<open>Theorems on lists\<close>

theory List_Theorems
  imports Main
begin

(* Returns the last n elements of list x *)
definition lastn :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list"
where "lastn n x = drop ((length x) - n) x"
(* Returns true iff [a,b] is a sequence in list x. *)
definition is_sub_seq :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
where "is_sub_seq a b x \<equiv> \<exists> n . Suc n < length x \<and> x!n = a \<and> x!(Suc n) = b"
(* Return, given a set of lists, the set with all prefixes of all the lists *)
definition prefixes :: "'a list set \<Rightarrow> 'a list set"
where "prefixes s \<equiv> {x . \<exists> n y . n > 0 \<and> y \<in> s \<and> take n y = x}"

lemma drop_one[simp]:
  shows "drop (Suc 0) x = tl x" by(induct x,auto)
lemma length_ge_one:
  shows "x \<noteq> [] \<longrightarrow> length x \<ge> 1" by(induct x,auto)
lemma take_but_one[simp]:
  shows "x \<noteq> [] \<longrightarrow> lastn ((length x) - 1) x = tl x" unfolding lastn_def
  using length_ge_one[where x=x] by auto
lemma Suc_m_minus_n[simp]:
  shows "m \<ge> n \<longrightarrow> Suc m - n = Suc (m - n)" by auto
lemma lastn_one_less:
 shows "n > 0 \<and> n \<le> length x \<and> lastn n x = (a#y) \<longrightarrow> lastn (n - 1) x = y" unfolding lastn_def
 using drop_Suc[where n="length x - n" and xs=x] drop_tl[where n="length x - n" and xs=x]
 by(auto)
lemma list_sub_implies_member:
  shows "\<forall> a x . set (a#x) \<subseteq> Z \<longrightarrow> a \<in> Z" by auto
lemma subset_smaller_list:
  shows "\<forall> a x . set (a#x) \<subseteq> Z \<longrightarrow> set x \<subseteq> Z" by auto
lemma second_elt_is_hd_tl: 
  shows "tl x = (a # x') \<longrightarrow> a = x ! 1" 
  by (cases x,auto)
lemma length_ge_2_implies_tl_not_empty:
  shows "length x \<ge> 2 \<longrightarrow> tl x \<noteq> []"
  by (cases x,auto)
lemma length_lt_2_implies_tl_empty:
  shows "length x < 2 \<longrightarrow> tl x = []"
  by (cases x,auto)  
lemma first_second_is_sub_seq:
  shows "length x \<ge> 2 \<Longrightarrow> is_sub_seq (hd x) (x!1) x"
proof-
  assume "length x \<ge> 2"
  hence 1: "(Suc 0) < length x" by auto
  hence "x!0 = hd x" by(cases x,auto)
  from this 1 show "is_sub_seq (hd x) (x!1) x" unfolding is_sub_seq_def by auto
qed
lemma hd_drop_is_nth:
  shows "n < length x \<Longrightarrow> hd (drop n x) = x!n"
proof(induct x arbitrary: n)
case Nil
  thus ?case by simp
next
case (Cons a x)
{
  have "hd (drop n (a # x)) = (a # x) ! n"
  proof(cases n)
  case 0
    thus ?thesis by simp
  next
  case (Suc m)
    from Suc Cons show ?thesis by auto
  qed
}
thus ?case by auto
qed

lemma def_of_hd:
  shows "y = a # x \<longrightarrow> hd y = a" by simp
lemma def_of_tl:
  shows "y = a # x \<longrightarrow> tl y = x" by simp  
lemma drop_yields_results_implies_nbound:
  shows "drop n x \<noteq> [] \<longrightarrow> n < length x"
by(induct x,auto)
lemma consecutive_is_sub_seq:
  shows "a # (b # x) = lastn n y \<Longrightarrow> is_sub_seq a b y"
proof-
  assume 1: "a # (b # x) = lastn n y"
  from 1 drop_Suc[where n="(length y) - n" and xs="y"]
       drop_tl[where n="(length y) - n" and xs="y"] 
       def_of_tl[where y="lastn n y" and a=a and x ="b#x"]
       drop_yields_results_implies_nbound[where n="Suc (length y - n)" and x=y]
    have 3: "Suc (length y - n) < length y" unfolding lastn_def by auto
  from 3 1 hd_drop_is_nth[where n="(length y) - n" and x=y] def_of_hd[where y="drop (length y - n) y" and x="b#x" and a=a]
    have 4: "y!(length y - n) = a"  unfolding lastn_def by auto
  from 3 1 hd_drop_is_nth[where n="Suc ((length y) - n)" and x=y] def_of_hd[where y="drop (Suc (length y - n)) y" and x="x" and a=b]
       drop_Suc[where n="(length y) - n" and xs="y"]
       drop_tl[where n="(length y) - n" and xs="y"] 
       def_of_tl[where y="lastn n y" and a=a and x ="b#x"]
    have 5: "y!Suc (length y - n) = b" unfolding lastn_def by auto
  from 3 4 5 show ?thesis
    unfolding is_sub_seq_def by auto
qed


lemma sub_seq_in_prefixes:
  assumes "\<exists>y \<in> prefixes X. is_sub_seq a a' y"
  shows "\<exists>y \<in> X. is_sub_seq a a' y"
proof-
  from assms obtain y where y: "y \<in> prefixes X \<and> is_sub_seq a a' y" by auto
  then obtain n x where x: "n > 0 \<and> x \<in> X \<and> take n x = y"
    unfolding prefixes_def by auto
  from y obtain i where sub_seq_index: "Suc i < length y \<and> y ! i = a \<and> y ! Suc i = a'"
    unfolding is_sub_seq_def by auto
  from sub_seq_index x have "is_sub_seq a a' x"
    unfolding is_sub_seq_def using nth_take by auto 
  from this x show ?thesis by metis
qed

lemma set_tl_is_subset:
shows "set (tl x) \<subseteq> set x" by(induct x,auto)
lemma x_is_hd_snd_tl:
shows "length x \<ge> 2 \<longrightarrow> x = (hd x) # x!1 # tl(tl x)"
proof(induct x)
case Nil
  show ?case by auto
case (Cons a xs)
  show ?case by(induct xs,auto)
qed

lemma tl_x_not_x:
shows "x \<noteq> [] \<longrightarrow> tl x \<noteq> x" by(induct x,auto)
lemma tl_hd_x_not_tl_x:
shows "x \<noteq> [] \<and> hd x \<noteq> [] \<longrightarrow> tl (hd x) # tl x \<noteq> x" using tl_x_not_x by(induct x,simp,auto)

end
