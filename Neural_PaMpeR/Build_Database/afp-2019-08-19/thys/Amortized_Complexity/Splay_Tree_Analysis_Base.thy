section "Splay Tree"

subsection "Basics"

theory Splay_Tree_Analysis_Base
imports
  Lemmas_log
  Splay_Tree.Splay_Tree
begin

declare size1_size[simp]

abbreviation "\<phi> t == log 2 (size1 t)"

fun \<Phi> :: "'a tree \<Rightarrow> real" where
"\<Phi> Leaf = 0" |
"\<Phi> (Node l a r) = \<Phi> l + \<Phi> r + \<phi> (Node l a r)"


fun t_splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_splay a Leaf = 1" |
"t_splay a (Node l b r) =
  (if a=b
   then 1
   else if a < b
        then case l of
          Leaf \<Rightarrow> 1 |
          Node ll c lr \<Rightarrow>
            (if a=c then 1
             else if a < c then if ll = Leaf then 1 else t_splay a ll + 1
                  else if lr = Leaf then 1 else t_splay a lr + 1)
        else case r of
          Leaf \<Rightarrow> 1 |
          Node rl c rr \<Rightarrow>
            (if a=c then 1
             else if a < c then if rl = Leaf then 1 else t_splay a rl + 1
                  else if rr = Leaf then 1 else t_splay a rr + 1))"

lemma t_splay_simps[simp]:
  "t_splay a (Node l a r) = 1"
  "a<b \<Longrightarrow> t_splay a (Node Leaf b r) = 1"
  "a<b \<Longrightarrow> t_splay a (Node (Node ll a lr) b r) = 1"
  "a<b \<Longrightarrow> a<c \<Longrightarrow> t_splay a (Node (Node ll c lr) b r) =
   (if ll = Leaf then 1 else t_splay a ll + 1)"
  "a<b \<Longrightarrow> c<a \<Longrightarrow> t_splay a (Node (Node ll c lr) b r) =
   (if lr = Leaf then 1 else t_splay a lr + 1)"
  "b<a \<Longrightarrow> t_splay a (Node l b Leaf) = 1"
  "b<a \<Longrightarrow> t_splay a (Node l b (Node rl a rr)) = 1"
  "b<a \<Longrightarrow> a<c \<Longrightarrow> t_splay a (Node l b (Node rl c rr)) =
  (if rl=Leaf then 1 else t_splay a rl + 1)"
  "b<a \<Longrightarrow> c<a \<Longrightarrow> t_splay a (Node l b (Node rl c rr)) =
  (if rr=Leaf then 1 else t_splay a rr + 1)"
by auto

declare t_splay.simps(2)[simp del]

fun t_splay_max :: "'a::linorder tree \<Rightarrow> nat" where
"t_splay_max Leaf = 1" |
"t_splay_max (Node l b Leaf) = 1" |
"t_splay_max (Node l b (Node rl c rr)) = (if rr=Leaf then 1 else t_splay_max rr + 1)"

definition t_delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> nat" where
"t_delete a t = (if t = Leaf then 0 else t_splay a t + (case splay a t of
  Node l x r \<Rightarrow>
    if x=a then case l of Leaf \<Rightarrow> 0 | _ \<Rightarrow> t_splay_max l
    else 0))"

lemma ex_in_set_tree: "t \<noteq> Leaf \<Longrightarrow> bst t \<Longrightarrow>
  \<exists>a' \<in> set_tree t. splay a' t = splay a t \<and> t_splay a' t = t_splay a t"
proof(induction a t rule: splay.induct)
  case (6 a b c ll)
  hence "splay a ll \<noteq> Leaf" by simp
  then obtain lll u llr where [simp]: "splay a ll = Node lll u llr"
    by (metis tree.exhaust)
  have "b < c" "bst ll" using "6.prems" by auto
  from "6.IH"[OF \<open>ll \<noteq> Leaf\<close> \<open>bst ll\<close>]
  obtain e where "e \<in> set_tree ll" "splay e ll = splay a ll" "t_splay e ll = t_splay a ll"
    by blast
  moreover hence "e<b" using "6.prems"(2) by auto
  ultimately show ?case using \<open>a<c\<close> \<open>a<b\<close> \<open>b<c\<close> \<open>bst ll\<close> by force
next
  case (8 b a c lr)
  hence "splay a lr \<noteq> Leaf" by simp
  then obtain lrl u lrr where [simp]: "splay a lr = Node lrl u lrr"
    by (metis tree.exhaust)
  have "b < c" "bst lr" using "8.prems" by auto
  from "8.IH"[OF \<open>lr \<noteq> Leaf\<close> \<open>bst lr\<close>]
  obtain e where "e \<in> set_tree lr" "splay e lr = splay a lr" "t_splay e lr = t_splay a lr"
    by blast
  moreover hence "b<e & e<c" using "8.prems"(2) by simp
  ultimately show ?case using \<open>a<c\<close> \<open>b<a\<close> \<open>b<c\<close> \<open>bst lr\<close> by force
next
  case (11 c a b rl)
  hence "splay a rl \<noteq> Leaf" by simp
  then obtain rll u rlr where [simp]: "splay a rl = Node rll u rlr"
    by (metis tree.exhaust)
  have "c < b" "bst rl" using "11.prems" by auto
  from "11.IH"[OF \<open>rl \<noteq> Leaf\<close> \<open>bst rl\<close>]
  obtain e where "e \<in> set_tree rl" "splay e rl = splay a rl" "t_splay e rl = t_splay a rl"
    by blast
  moreover hence "c<e & e<b" using "11.prems" by simp
  ultimately show ?case using \<open>c<a\<close> \<open>a<b\<close> \<open>c<b\<close> \<open>bst rl\<close> by force
next
  case (14 c a b rr)
  hence "splay a rr \<noteq> Leaf" by simp
  then obtain rrl u rrr where [simp]: "splay a rr = Node rrl u rrr"
    by (metis tree.exhaust)
  have "c < b" "bst rr" using "14.prems" by auto
  from "14.IH"[OF \<open>rr \<noteq> Leaf\<close> \<open>bst rr\<close>]
  obtain e where "e \<in> set_tree rr" "splay e rr = splay a rr" "t_splay e rr = t_splay a rr"
    by blast
  moreover hence "b<e" using "14.prems"(2) by simp
  ultimately show ?case using \<open>c<a\<close> \<open>b<a\<close> \<open>c<b\<close> \<open>bst rr\<close> by force
qed (auto simp: le_less)


datatype 'a op = Empty | Splay 'a | Insert 'a | Delete 'a

fun arity :: "'a::linorder op \<Rightarrow> nat" where
"arity Empty = 0" |
"arity (Splay a) = 1" |
"arity (Insert a) = 1" |
"arity (Delete a) = 1"

fun exec :: "'a::linorder op \<Rightarrow> 'a tree list \<Rightarrow> 'a tree" where
"exec Empty [] = Leaf" |
"exec (Splay a) [t] = splay a t" |
"exec (Insert a) [t] = Splay_Tree.insert a t" |
"exec (Delete a) [t] = Splay_Tree.delete a t"

fun cost :: "'a::linorder op \<Rightarrow> 'a tree list \<Rightarrow> nat" where
"cost Empty [] = 1" |
"cost (Splay a) [t] = t_splay a t" |
"cost (Insert a) [t] = t_splay a t" |
"cost (Delete a) [t] = t_delete a t"

end
