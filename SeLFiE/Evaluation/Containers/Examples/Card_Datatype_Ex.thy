(*  Title:      Containers/Card_Datatype_Ex.thy
    Author:     Andreas Lochbihler, ETH Zurich *)

theory Card_Datatype_Ex imports
  "../Card_Datatype"
begin

subsection \<open>Examples\<close>

subsubsection \<open>Finite types\<close>

datatype ('a, 'b) foo = Foo 'a | Bar 'a 'b | FooBar 'a 'b "'a + 'b" | Stop

lemma inj_foo [simp]: 
  "inj Foo" 
  "inj Bar" "inj (Bar x)" 
  "inj FooBar" "inj (FooBar x)" "inj (FooBar x y)"
by(simp_all add: inj_on_def fun_eq_iff)

context includes card_datatype begin

lemma UNIV_foo: 
  "(UNIV :: ('a, 'b) foo set) = 
  rangeC {Foo} \<union> 
  rangeC (rangeC {Bar}) \<union> 
  rangeC (rangeC (rangeC {FooBar})) \<union> 
  rangeC {\<lambda>_::unit. Stop}"
apply(rule UNIV_eq_I)
apply(case_tac x)
apply(simp_all)
done

lemma finite_UNIV_foo:
  "finite (UNIV :: ('a, 'b) foo set) \<longleftrightarrow> finite (UNIV :: 'a set) \<and> finite (UNIV :: 'b set)"
by(simp add: UNIV_foo)

definition card_foo :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where "card_foo a b = (if a = 0 \<or> b = 0 then 0 else a + a * b + a * b * card_sum a b + 1)"

lemma CARD_foo [card_simps]:
  "CARD(('a, 'b) foo) = card_foo CARD('a) CARD('b)"
by(simp add: card_foo_def UNIV_foo Let_def card_simps)

end


datatype ('a, 'b) bar 
  = Bar1 
  | Bar2 "'a \<Rightarrow> 'b"
  | Bar3 "('a, 'b) foo" "'a \<Rightarrow> char \<Rightarrow> 'b \<Rightarrow> 'a" "('a \<times> 'b) option" 
  | Bar4 char 'a bool

lemma inj_bar [simp]:
  "inj Bar2"
  "inj Bar3"
  "inj (Bar3 x)"
  "inj (Bar3 x y)"
  "inj Bar4"
  "inj (Bar4 z)"
  "inj (Bar4 z u)"
by(simp_all add: inj_on_def fun_eq_iff)

context includes card_datatype begin

lemma UNIV_bar: 
  "(UNIV :: ('a, 'b) bar set) =
  rangeC {\<lambda>_::unit. Bar1} \<union>
  rangeC {Bar2} \<union>
  rangeC (rangeC (rangeC {Bar3})) \<union>
  rangeC (rangeC (rangeC {Bar4}))"
apply(rule UNIV_eq_I)
apply(case_tac x)
apply(simp_all)
done

lemma finite_UNIV_bar:
  "finite (UNIV :: ('a, 'b) bar set) \<longleftrightarrow> finite (UNIV :: 'a set) \<and> finite (UNIV :: 'b set)"
by(auto simp add: UNIV_bar finite_UNIV_fun finite_prod finite_UNIV_foo)

definition card_bar :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "card_bar a b = 
  (if a = 0 \<or> b = 0 then 0
   else 1 + card_fun a b + card_foo a b * card_fun a (card_fun CARD(char) (card_fun b a)) * card_option (card_prod a b) + CARD(char) * a * CARD(bool))"

lemma CARD_bar [card_simps]:
  "CARD(('a, 'b) bar) = card_bar CARD('a) CARD('b)"
by(simp add: UNIV_bar card_bar_def finite_UNIV_bar finite_UNIV_foo finite_prod finite_UNIV_fun card_simps del: card_prod)

end

subsection \<open>Infinite types\<close>

datatype 'a tree = Leaf | Node 'a "'a tree" "'a tree"

lemma inj_expr [simp]:
  "inj Node"
  "inj (Node a)"
  "inj (Node a l)"
by(simp_all add: inj_on_def fun_eq_iff)

context includes card_datatype begin

lemma finite_UNIV_tree: "finite (UNIV :: 'a tree set) \<longleftrightarrow> False"
proof -
  have "rangeIt Leaf (Node (undefined :: 'a) Leaf) \<subseteq> UNIV" by simp
  from finite_subset[OF this] show ?thesis by auto
qed

definition card_tree :: "nat \<Rightarrow> nat"
where "card_tree _ = 0"

lemma CARD_tree [card_simps]:
  "CARD('a tree) = card_tree CARD('a)"
by(simp add: card_tree_def finite_UNIV_tree)

end

end
