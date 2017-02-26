theory Splay_Tree
imports "~~/src/HOL/Library/Tree"
  "../../PSL"
begin

strategy Solve_One_Hard = Ors [Blast, Fastforce, Thens [Subgoal, Auto, RepeatN(Hammer), IsSolved]]
strategy Solve_Subgoals = Thens[RepeatN(Solve_One_Hard), IsSolved]
strategy DInduct_Hard = PThenOne [DInduct, Solve_Subgoals]
  
section "Splay Tree"

text{* Splay trees were invented by Sleator and
Tarjan~\cite{SleatorT-JACM85}. *}

text{* This compensates for an incompleteness of the partial order prover: *}
simproc_setup less_False ("(x::'a::order) < y") = {* fn _ => fn ctxt => fn ct =>
  let
    fun prp t thm = Thm.full_prop_of thm aconv t;

    val eq_False_if_not = @{thm eq_False} RS iffD2

    fun prove_less_False ((less as Const(_,T)) $ r $ s) =
      let val prems = Simplifier.prems_of ctxt;
          val le = Const (@{const_name less_eq}, T);
          val t = HOLogic.mk_Trueprop(le $ s $ r);
      in case find_first (prp t) prems of
           NONE =>
             let val t = HOLogic.mk_Trueprop(less $ s $ r)
             in case find_first (prp t) prems of
                  NONE => NONE
                | SOME thm => SOME(mk_meta_eq((thm RS @{thm less_not_sym}) RS eq_False_if_not))
             end
         | SOME thm => NONE
      end;
  in prove_less_False (Thm.term_of ct) end
*}

subsection "Function @{text splay}"

function splay :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"splay a Leaf = Leaf" |
"splay a (Node l a r) = Node l a r" |
"a<b \<Longrightarrow> splay a (Node (Node la a ra) b rb) = Node la a (Node ra b rb)" |
"a<b \<Longrightarrow> splay a (Node Leaf b r) = Node Leaf b r" |
"x<a \<Longrightarrow> x<b \<Longrightarrow> splay x (Node (Node Leaf a ra) b rb) = Node Leaf a (Node ra b rb)" |
"x<a \<Longrightarrow> x<b \<Longrightarrow> la \<noteq> Leaf \<Longrightarrow>
 splay x (Node (Node la a lr) b rb) =
 (case splay x la of Node lc c rc \<Rightarrow> Node lc c (Node rc a (Node lr b rb)))" |
"x<b \<Longrightarrow> a<x \<Longrightarrow> splay x (Node (Node la a Leaf) b rb) = Node la a (Node Leaf b rb)" |
"x<b \<Longrightarrow> a<x \<Longrightarrow> ra \<noteq> Leaf \<Longrightarrow>
 splay x (Node (Node la a ra) b rb) =
 (case splay x ra of Node lc c rc \<Rightarrow> Node (Node la a lc) c (Node rc b rb))" |
"b<a \<Longrightarrow> splay a (Node lb b (Node la a ra)) = Node (Node lb b la) a ra" |
"a<x \<Longrightarrow> splay x (Node l a Leaf) = Node l a Leaf" |
"a<x \<Longrightarrow> x<b \<Longrightarrow> lb \<noteq> Leaf \<Longrightarrow>
 splay x (Node la a (Node lb b rb)) =
 (case splay x lb of Node lc c rc \<Rightarrow> Node (Node la a lc) c (Node rc b rb))" |
"a<x \<Longrightarrow> x<b \<Longrightarrow> splay x (Node la a (Node Leaf b rb)) = Node (Node la a Leaf) b rb" |
"a<x \<Longrightarrow> b<x \<Longrightarrow> splay x (Node la a (Node lb b Leaf)) = Node (Node la a lb) b Leaf" |
"a<x \<Longrightarrow> b<x \<Longrightarrow> rb \<noteq> Leaf \<Longrightarrow>
 splay x (Node la a (Node lb b rb)) =
 (case splay x rb of Node lc c rc \<Rightarrow> Node (Node (Node la a lb) b lc) c rc)"
apply(atomize_elim)
apply(auto)
(* 1 subgoal *)
apply (subst (asm) neq_Leaf_iff)
apply(auto)
apply (metis tree.exhaust le_less_linear less_linear)+
done

termination splay
by lexicographic_order

lemma splay_code: "splay x (Node la a ra) =
  (if x=a
   then Node la a ra
   else if x < a
        then case la of
          Leaf \<Rightarrow> Node la a ra |
          Node lb b rb \<Rightarrow>
            (if x=b then Node lb x (Node rb a ra)
             else if x < b
                  then if lb = Leaf then Node lb b (Node rb a ra)
                       else case splay x lb of
                         Node lc c rc \<Rightarrow> Node lc c (Node rc b (Node rb a ra))
                  else if rb = Leaf then Node lb b (Node rb a ra)
                       else case splay x rb of
                         Node lc c rc \<Rightarrow> Node (Node lb b lc) c (Node rc a ra))
        else case ra of
          Leaf \<Rightarrow> Node la a ra |
          Node lb b rb \<Rightarrow>
            (if x=b then Node (Node la a lb) x rb
             else if x < b
                  then if lb = Leaf then Node (Node la a lb) b rb
                       else case splay x lb of
                         Node lc c rc \<Rightarrow> Node (Node la a lc) c (Node rc b rb)
                  else if rb=Leaf then Node (Node la a lb) b rb
                       else case splay x rb of
                         Node lc c rc \<Rightarrow> Node (Node (Node la a lb) b lc) c rc))"
by(auto split: tree.split)

lemma splay_Leaf_iff[simp]: "(splay a t = Leaf) = (t = Leaf)"
apply(induction a t rule: splay.induct)
apply auto
 apply(auto split: tree.splits)
done

lemma size_splay[simp]: "size (splay a t) = size t"
apply(induction a t rule: splay.induct)
apply auto
 apply(force split: tree.split)+
done

lemma size_if_splay: "splay a t = Node l u r \<Longrightarrow> size t = size l + size r + 1"
by (metis One_nat_def size_splay tree.size(4))

lemma splay_not_Leaf: "t \<noteq> Leaf \<Longrightarrow> \<exists>l x r. splay a t = Node l x r"
by (metis neq_Leaf_iff splay_Leaf_iff)

lemma set_splay: "set_tree(splay a t) = set_tree t"
proof(induction a t rule: splay.induct)
  case (6 a)
  with splay_not_Leaf[OF 6(3), of a] show ?case by(fastforce)
next
  case (8 a)
  with splay_not_Leaf[OF 8(3), of a] show ?case by(fastforce)
next
  case (11 _ a)
  with splay_not_Leaf[OF 11(3), of a] show ?case by(fastforce)
next
  case (14 _ a)
  with splay_not_Leaf[OF 14(3), of a] show ?case by(fastforce)
qed auto

lemma splay_bstL: "bst t \<Longrightarrow> splay a t = Node l e r \<Longrightarrow> x \<in> set_tree l \<Longrightarrow> x < a"
apply(induction a t arbitrary: l x r rule: splay.induct)
apply (auto split: tree.splits)
apply auto
done

lemma splay_bstR: "bst t \<Longrightarrow> splay a t = Node l e r \<Longrightarrow> x \<in> set_tree r \<Longrightarrow> a < x"
apply(induction a t arbitrary: l e x r rule: splay.induct)
apply auto
apply (fastforce split: tree.splits)+
done

lemma bst_splay: "bst t \<Longrightarrow> bst(splay a t)"
proof(induction a t rule: splay.induct)
  case (6 a _ _ ll)
  with splay_not_Leaf[OF 6(3), of a] set_splay[of a ll,symmetric]
  show ?case by (fastforce)
next
  case (8 a _ _ t)
  with splay_not_Leaf[OF 8(3), of a] set_splay[of a t,symmetric]
  show ?case by fastforce
next
  case (11 _ a _ t)
  with splay_not_Leaf[OF 11(3), of a] set_splay[of a t,symmetric]
  show ?case by fastforce
next
  case (14 _ a _ t)
  with splay_not_Leaf[OF 14(3), of a] set_splay[of a t,symmetric]
  show ?case by fastforce
qed auto

lemma splay_to_root: "\<lbrakk> bst t;  splay a t = t' \<rbrakk> \<Longrightarrow>
  a \<in> set_tree t \<longleftrightarrow> (\<exists>l r. t' = Node l a r)"
proof(induction a t arbitrary: t' rule: splay.induct)
  case (6 a)
  with splay_not_Leaf[OF 6(3), of a] show ?case by auto
next
  case (8 a)
  with splay_not_Leaf[OF 8(3), of a] show ?case by auto
next
  case (11 _ a)
  with splay_not_Leaf[OF 11(3), of a] show ?case by auto
next
  case (14 _ a)
  with splay_not_Leaf[OF 14(3), of a] show ?case by auto
qed fastforce+


subsection "Is-in Test"

text{* To test if an element @{text a} is in @{text t}, first perform
@{term"splay a t"}, then check if the root is @{text a}. One could
put this into one function that returns both a new tree and the test result. *}

(* FIXME mv *)
definition is_root :: "'a \<Rightarrow> 'a tree \<Rightarrow> bool" where
"is_root a t = (case t of Leaf \<Rightarrow> False | Node _ x _ \<Rightarrow> x = a)"

lemma is_root_splay: "bst t \<Longrightarrow> is_root a (splay a t) \<longleftrightarrow> a \<in> set_tree t"
by(auto simp add: is_root_def splay_to_root split: tree.split)


subsection "Function @{text insert}"

context
begin

qualified fun insert :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"insert x t =  (if t = Leaf then Node Leaf x Leaf
  else case splay x t of
    Node l a r \<Rightarrow> if x=a then Node l a r
      else if x<a then Node l x (Node Leaf a r) else Node (Node l a Leaf) x r)"

end

lemma set_insert: "set_tree(Splay_Tree.insert a t) = insert a (set_tree t)"
apply(cases t)
 apply simp
using set_splay[of a t]
by(simp split: tree.split) fastforce

lemma bst_insert: "bst t \<Longrightarrow> bst(Splay_Tree.insert a t)"
apply(cases t)
 apply simp
using bst_splay[of t a] splay_bstL[of t a] splay_bstR[of t a]
by(auto simp: ball_Un split: tree.split)


subsection "Function @{text splay_max}"

fun splay_max :: "'a::linorder tree \<Rightarrow> 'a tree" where
"splay_max Leaf = Leaf" |
"splay_max (Node la a Leaf) = Node la a Leaf" |
"splay_max (Node la a (Node lb b rb)) =
  (if rb = Leaf then Node (Node la a lb) b Leaf
   else case splay_max rb of
     Node lc c rc \<Rightarrow> Node (Node (Node la a lb) b lc) c rc)"

lemma splay_max_Leaf_iff[simp]: "(splay_max t = Leaf) = (t = Leaf)"find_proof DInduct_Hard
  apply(induction t rule: splay_max.induct)
  apply(auto split: tree.splits)
done

lemma splay_max_code: "splay_max t = (case t of
  Leaf \<Rightarrow> t |
  Node la a ra \<Rightarrow> (case ra of
    Leaf \<Rightarrow> t |
    Node lb b rb \<Rightarrow>
      (if rb=Leaf then Node (Node la a lb) b rb
       else case splay_max rb of
              Node lc c rc \<Rightarrow> Node (Node (Node la a lb) b lc) c rc)))"
by(auto simp: neq_Leaf_iff split: tree.split)

lemma size_splay_max: "size(splay_max t) = size t"
apply(induction t rule: splay_max.induct)
  apply(simp)
 apply(simp)
apply(clarsimp split: tree.split)
done

lemma size_if_splay_max: "splay_max t = Node l u r \<Longrightarrow> size t = size l + size r + 1"
by (metis One_nat_def size_splay_max tree.size(4))

strategy DFF = Dynamic(Fastforce)
lemma set_splay_max: "set_tree(splay_max t) = set_tree t"
  apply(induction t rule: splay_max.induct)
   apply(simp)
  apply(simp)
apply(force split: tree.split)
done

lemma bst_splay_max: "bst t \<Longrightarrow> bst (splay_max t)"
proof(induction t rule: splay_max.induct)
  case (3 l b rl c rr)
  { fix rrl' d' rrr'
    have "splay_max rr = Node rrl' d' rrr'
       \<Longrightarrow> !x : set_tree(Node rrl' d' rrr'). c < x" 
      using "3.prems" set_splay_max[of rr]
      by (clarsimp split: tree.split simp: ball_Un)
  }
  with 3 show ?case by (fastforce split: tree.split simp: ball_Un)
qed auto

lemma splay_max_Leaf: "splay_max t = Node l a r \<Longrightarrow> r = Leaf"
by(induction t arbitrary: l rule: splay_max.induct)
  (auto split: tree.splits if_splits)

text{* For sanity purposes only: *}

lemma splay_max_eq_splay:
  "bst t \<Longrightarrow> \<forall>x \<in> set_tree t. x \<le> a \<Longrightarrow> splay_max t = splay a t"
(*find_proof DInduct_Hard error*)
proof(induction a t rule: splay.induct)
  case (2 a l r)
  show ?case
  proof (cases r)
    case Leaf with 2 show ?thesis by simp
  next
    case Node with 2 show ?thesis by(auto)
  qed
qed (auto simp: neq_Leaf_iff)

lemma splay_max_eq_splay_ex: assumes "bst t" shows "\<exists>a. splay_max t = splay a t"
proof(cases t)
  case Leaf thus ?thesis by simp
next
  case Node
  hence "splay_max t = splay (Max(set_tree t)) t"
    using assms by (auto simp: splay_max_eq_splay)
  thus ?thesis by auto
qed


subsection "Function @{text delete}"

context
begin

qualified definition delete :: "'a::linorder \<Rightarrow> 'a tree \<Rightarrow> 'a tree" where
"delete x t = (if t=Leaf then Leaf
  else case splay x t of Node l a r \<Rightarrow>
    if x=a
    then if l = Leaf then r else case splay_max l of Node l' m r' \<Rightarrow> Node l' m r
    else Node l a r)"

lemma set_delete: assumes "bst t"
shows "set_tree (delete a t) = set_tree t - {a}"
proof(cases t)
  case Leaf thus ?thesis by(simp add: delete_def)
next
  case (Node l x r)
  obtain l' x' r' where sp[simp]: "splay a (Node l x r) = Node l' x' r'"
    by (metis neq_Leaf_iff splay_Leaf_iff)
  show ?thesis
  proof cases
    assume [simp]: "x' = a"
    show ?thesis
    proof cases
      assume "l' = Leaf"
      thus ?thesis
        using Node assms set_splay[of a "Node l x r"] bst_splay[of "Node l x r" a]
        by(simp add: delete_def split: tree.split prod.split)(fastforce)
    next
      assume "l' \<noteq> Leaf"
      moreover then obtain l'' m r'' where "splay_max l' = Node l'' m r''"
        using splay_max_Leaf_iff tree.exhaust by blast
      moreover have "a \<notin> set_tree l'"
        by (metis (no_types) Node assms less_irrefl sp splay_bstL)
      ultimately show ?thesis
        using Node assms set_splay[of a "Node l x r"] bst_splay[of "Node l x r" a]
          splay_max_Leaf[of l' l'' m r''] set_splay_max[of l']
        by(clarsimp simp: delete_def split: tree.split) auto
    qed
  next
    assume "x' \<noteq> a"
    thus ?thesis using Node assms set_splay[of a "Node l x r"] splay_to_root[OF _ sp]
      by (simp add: delete_def)
  qed
qed

lemma bst_delete: assumes "bst t" shows "bst (delete a t)"
proof(cases t)
  case Leaf thus ?thesis by(simp add: delete_def)
next
  case (Node l x r)
  obtain l' x' r' where sp[simp]: "splay a (Node l x r) = Node l' x' r'"
    by (metis neq_Leaf_iff splay_Leaf_iff)
  show ?thesis
  proof cases
    assume [simp]: "x' = a"
    show ?thesis
    proof cases
      assume "l' = Leaf"
      thus ?thesis using Node assms bst_splay[of "Node l x r" a]
        by(simp add: delete_def split: tree.split prod.split)
    next
      assume "l' \<noteq> Leaf"
      thus ?thesis
        using Node assms set_splay[of a "Node l x r"] bst_splay[of "Node l x r" a]
          bst_splay_max[of l'] set_splay_max[of l']
        by(clarsimp simp: delete_def split: tree.split)
          (metis (no_types) insertI1 less_trans)
    qed
  next
    assume "x' \<noteq> a"
    thus ?thesis using Node assms bst_splay[of "Node l x r" a]
      by(auto simp: delete_def split: tree.split prod.split)
  qed
qed

end

end
