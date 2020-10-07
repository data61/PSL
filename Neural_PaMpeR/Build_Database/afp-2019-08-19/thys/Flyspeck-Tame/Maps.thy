theory Maps
imports Worklist Quasi_Order
begin

locale maps =
fixes empty :: "'m"
and up :: "'a \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm"
and map_of :: "'m \<Rightarrow> 'a \<Rightarrow> 'b list"
and M :: "'m \<Rightarrow> bool"
assumes map_empty: "map_of empty = (\<lambda>a. [])"
and map_up: "map_of (up a b m) = (map_of m)(a := b)"
and M_empty: "M empty"
and M_up: "M m \<Longrightarrow> M (up a b m)"
begin

definition "set_of m = (UN x. set(map_of m x))"

end

locale set_mod_maps = maps empty up map_of M + quasi_order qle
for empty :: "'m"
and up :: "'a \<Rightarrow> 'b list \<Rightarrow> 'm \<Rightarrow> 'm"
and map_of :: "'m \<Rightarrow> 'a \<Rightarrow> 'b list"
and M :: "'m \<Rightarrow> bool"
and qle :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<preceq>" 60)
+
fixes subsumed :: "'b \<Rightarrow> 'b \<Rightarrow> bool"
and I :: "'b \<Rightarrow> bool"
and key :: "'b \<Rightarrow> 'a"
assumes equiv_iff_qle: "I x \<Longrightarrow> I y \<Longrightarrow> subsumed x y = (x \<preceq> y)"
and "key=key"
begin

definition "insert_mod x m =
  (let k = key x; ys = map_of m k
   in if (\<exists>y \<in> set ys. subsumed x y) then m else up k (x#ys) m)"

end

sublocale
  set_mod_maps <
  set_by_maps?: set_modulo qle empty insert_mod set_of I M
proof (standard, goal_cases)
  case 1 show ?case by(simp add:set_of_def map_empty)
next
  case 2 thus ?case
    by (auto simp: Let_def insert_mod_def set_of_def map_up equiv_iff_qle
      split:if_split_asm)
next
  case 3 show ?case by(simp add: M_empty)
next
  case 4 thus ?case
    by(simp add: insert_mod_def Let_def M_up)
qed

end
