section \<open>Trees\<close>

theory Tree imports Main begin

text \<open>Sometimes it is nice to think of @{typ bool}s as directions in a binary tree\<close>
hide_const (open) Left Right
type_synonym dir = bool
definition Left :: bool where "Left = True"
definition Right :: bool where "Right = False"
declare Left_def [simp]
declare Right_def [simp]

datatype tree =
  Leaf
| Branching (ltree: tree) (rtree: tree) 


subsection \<open>Sizes\<close>

fun treesize :: "tree \<Rightarrow> nat" where
  "treesize Leaf = 0"
| "treesize (Branching l r) = 1 + treesize l + treesize r"

lemma treesize_Leaf:
  assumes "treesize T = 0"
  shows "T = Leaf"
  using assms by (cases T) auto

lemma treesize_Branching:
  assumes "treesize T = Suc n"
  shows "\<exists>l r. T = Branching l r" 
  using assms by (cases T) auto


subsection \<open>Paths\<close>

fun path :: "dir list \<Rightarrow> tree \<Rightarrow> bool" where
  "path [] T \<longleftrightarrow> True"
| "path (d#ds) (Branching T1 T2) \<longleftrightarrow> (if d then path ds T1 else path ds T2)"
| "path _ _ \<longleftrightarrow> False"

lemma path_inv_Leaf: "path p Leaf \<longleftrightarrow> p = []"
  by (induction p)  auto

lemma path_inv_Cons: "path (a#ds) T \<longrightarrow> (\<exists>l r. T=Branching l r)"
  by  (cases T) (auto simp add: path_inv_Leaf)


lemma path_inv_Branching_Left: "path (Left#p) (Branching l r) \<longleftrightarrow> path p l"
  using Left_def Right_def path.cases by (induction p) auto

lemma path_inv_Branching_Right: "path (Right#p) (Branching l r) \<longleftrightarrow> path p r"
using Left_def Right_def path.cases by (induction p)  auto


lemma path_inv_Branching: 
  "path p (Branching l r) \<longleftrightarrow> (p=[] \<or> (\<exists>a p'. p=a#p'\<and> (a \<longrightarrow> path p' l) \<and> (\<not>a \<longrightarrow> path p' r)))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R by (induction p) auto
next
  assume r: ?R
  then show ?L
    proof
      assume "p = []" then show ?L by auto
    next
      assume "\<exists>a p'. p=a#p'\<and> (a \<longrightarrow> path p' l) \<and> (\<not>a \<longrightarrow> path p' r)"
      then obtain a p' where "p=a#p'\<and> (a \<longrightarrow> path p' l) \<and> (\<not>a \<longrightarrow> path p' r)" by auto
      then show ?L by (cases a) auto
    qed
qed

lemma path_prefix: 
  assumes "path (ds1@ds2) T"
  shows "path ds1 T"
using assms proof (induction ds1 arbitrary: T)
  case (Cons a ds1)
  then have "\<exists>l r. T = Branching l r" using path_inv_Leaf by (cases T) auto
  then obtain l r where p_lr: "T = Branching l r" by auto
  show ?case
    proof (cases a)
      assume atrue: "a"
      then have "path ((ds1) @ ds2) l" using p_lr Cons(2) path_inv_Branching by auto
      then have "path ds1 l" using Cons(1) by auto
      then show "path (a # ds1) T" using p_lr atrue by auto
    next
      assume afalse: "\<not>a"
      then have "path ((ds1) @ ds2) r" using p_lr Cons(2) path_inv_Branching by auto
      then have "path ds1 r" using Cons(1) by auto
      then show "path (a # ds1) T" using p_lr afalse by auto
    qed
next
  case (Nil) then show ?case  by auto
qed


subsection \<open>Branches\<close>

fun branch :: "dir list \<Rightarrow> tree \<Rightarrow> bool" where
  "branch [] Leaf \<longleftrightarrow> True"    
| "branch (d # ds) (Branching l r) \<longleftrightarrow> (if d then branch ds l else branch ds r)"
| "branch _ _ \<longleftrightarrow> False"

lemma has_branch: "\<exists>b. branch b T"
proof (induction T)
  case (Leaf) 
  have "branch [] Leaf" by auto
  then show ?case by blast
next
  case (Branching T\<^sub>1 T\<^sub>2)
  then obtain b where "branch b T\<^sub>1" by auto
  then have "branch (Left#b) (Branching T\<^sub>1 T\<^sub>2)"  by auto
  then show ?case by blast
qed

lemma branch_inv_Leaf: "branch b Leaf \<longleftrightarrow> b = []"
by (cases b) auto

lemma branch_inv_Branching_Left:  
  "branch (Left#b) (Branching l r) \<longleftrightarrow> branch b l"
by auto

lemma branch_inv_Branching_Right: 
  "branch (Right#b) (Branching l r) \<longleftrightarrow> branch b r"
by auto

lemma branch_inv_Branching: 
  "branch b (Branching l r) \<longleftrightarrow> 
     (\<exists>a b'. b=a#b'\<and> (a \<longrightarrow> branch b' l) \<and> (\<not>a \<longrightarrow>  branch b' r))"
by (induction b) auto

lemma branch_inv_Leaf2:
  "T = Leaf \<longleftrightarrow> (\<forall>b. branch b T \<longrightarrow> b = [])"
proof -
  {
    assume "T=Leaf"
    then have "\<forall>b. branch b T \<longrightarrow> b = []" using branch_inv_Leaf by auto
  }
  moreover 
  {
    assume "\<forall>b. branch b T \<longrightarrow> b = []"
    then have "\<forall>b. branch b T \<longrightarrow> \<not>(\<exists>a b'. b = a # b')" by auto
    then have "\<forall>b. branch b T \<longrightarrow> \<not>(\<exists>l r. branch b (Branching l r))" 
      using branch_inv_Branching by auto
    then have "T=Leaf" using has_branch[of T] by (metis branch.elims(2))
  }
  ultimately show "T = Leaf \<longleftrightarrow> (\<forall>b. branch b T \<longrightarrow> b = [])" by auto
qed

lemma branch_is_path: 
  assumes"branch ds T"
  shows "path ds T"
using assms proof (induction T arbitrary: ds)
  case Leaf
  then have "ds = []" using branch_inv_Leaf by auto
  then show ?case  by auto
next
  case (Branching T\<^sub>1 T\<^sub>2) 
  then obtain a b where ds_p: "ds = a # b \<and> (a \<longrightarrow> branch b T\<^sub>1) \<and> (\<not> a \<longrightarrow> branch b T\<^sub>2)" using branch_inv_Branching[of ds] by blast
  then have "(a \<longrightarrow> path b T\<^sub>1) \<and> (\<not>a \<longrightarrow> path b T\<^sub>2)" using Branching by auto
  then show "?case" using ds_p by (cases a) auto
qed

lemma Branching_Leaf_Leaf_Tree:
  assumes "T = Branching T1 T2"
  shows "(\<exists>B. branch (B@[True]) T \<and> branch (B@[False]) T)"
using assms proof (induction T arbitrary: T1 T2)
  case Leaf then show ?case by auto
next
  case (Branching T1' T2')
  {
    assume "T1'=Leaf \<and> T2'=Leaf"
    then have "branch ([] @ [True]) (Branching T1' T2') \<and> branch ([] @ [False]) (Branching T1' T2')" by auto
    then have ?case by metis
  }
  moreover
  {
    fix T11 T12
    assume "T1' = Branching T11 T12"
    then obtain B where "branch (B @ [True]) T1' 
                       \<and> branch (B @ [False]) T1'" using Branching by blast
    then have "branch (([True] @ B) @ [True]) (Branching T1' T2') 
             \<and> branch (([True] @ B) @ [False]) (Branching T1' T2')" by auto
    then have ?case by blast
  }
  moreover
  {
    fix T11 T12
    assume "T2' = Branching T11 T12"
    then obtain B where "branch (B @ [True]) T2' 
                       \<and> branch (B @ [False]) T2'" using Branching by blast
    then have "branch (([False] @ B) @ [True]) (Branching T1' T2') 
             \<and> branch (([False] @ B) @ [False]) (Branching T1' T2')" by auto
    then have ?case by blast
  }
  ultimately show ?case using tree.exhaust by blast
qed


subsection \<open>Internal Paths\<close>

fun internal :: "dir list \<Rightarrow> tree \<Rightarrow> bool" where
  "internal [] (Branching l r) \<longleftrightarrow> True"
| "internal (d#ds) (Branching l r) \<longleftrightarrow> (if d then internal ds l else internal ds r)"
| "internal _ _ \<longleftrightarrow> False"

lemma internal_inv_Leaf: "\<not>internal b Leaf" using internal.simps by blast

lemma internal_inv_Branching_Left:  
  "internal (Left#b) (Branching l r) \<longleftrightarrow> internal b l" by auto

lemma internal_inv_Branching_Right: 
  "internal (Right#b) (Branching l r) \<longleftrightarrow> internal b r"
by auto

lemma internal_inv_Branching: 
  "internal p (Branching l r) \<longleftrightarrow> (p=[] \<or> (\<exists>a p'. p=a#p'\<and> (a \<longrightarrow> internal p' l) \<and> (\<not>a \<longrightarrow> internal p' r)))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R by (metis internal.simps(2) neq_Nil_conv) 
next
  assume r: ?R
  then show ?L
    proof
      assume "p = []" then show ?L by auto
    next
      assume "\<exists>a p'. p=a#p'\<and> (a \<longrightarrow> internal p' l) \<and> (\<not>a \<longrightarrow> internal p' r)"
      then obtain a p' where "p=a#p'\<and> (a \<longrightarrow> internal p' l) \<and> (\<not>a \<longrightarrow> internal p' r)" by auto
      then show ?L by (cases a) auto
    qed
qed

lemma internal_is_path: 
  assumes "internal ds T"
  shows "path ds T"
using assms proof (induction T arbitrary: ds)
  case Leaf
  then have "False" using internal_inv_Leaf by auto
  then show ?case by auto
next
  case (Branching T\<^sub>1 T\<^sub>2) 
  then obtain a b where ds_p: "ds=[] \<or> ds = a # b \<and> (a \<longrightarrow> internal b T\<^sub>1) \<and> (\<not> a \<longrightarrow> internal b T\<^sub>2)" using internal_inv_Branching by blast
  then have "ds = [] \<or> (a \<longrightarrow> path b T\<^sub>1) \<and> (\<not>a \<longrightarrow> path b T\<^sub>2)" using Branching by auto
  then show "?case" using ds_p by (cases a) auto
qed

lemma internal_prefix:
  assumes "internal (ds1@ds2@[d]) T"
  shows "internal ds1 T" (* more or less copy paste of path_prefix *)
using assms proof (induction ds1 arbitrary: T)
  case (Cons a ds1)
  then have "\<exists>l r. T = Branching l r" using internal_inv_Leaf by (cases T) auto
  then obtain l r where p_lr: "T = Branching l r" by auto
  show ?case
    proof (cases a)
      assume atrue: "a"
      then have "internal ((ds1) @ ds2 @[d]) l" using p_lr Cons(2) internal_inv_Branching by auto
      then have "internal ds1 l" using Cons(1) by auto
      then show "internal (a # ds1) T" using p_lr atrue by auto
    next
      assume afalse: "~a"
      then have "internal ((ds1) @ ds2 @[d]) r" using p_lr Cons(2) internal_inv_Branching by auto
      then have "internal ds1 r" using Cons(1) by auto
      then show "internal (a # ds1) T" using p_lr afalse by auto
    qed
next
  case (Nil)
  then have "\<exists>l r. T = Branching l r" using internal_inv_Leaf by (cases T) auto 
  then show ?case by auto
qed


lemma internal_branch:
  assumes "branch (ds1@ds2@[d]) T"
  shows "internal ds1 T" (* more or less copy paste of path_prefix *)
using assms proof (induction ds1 arbitrary: T)
  case (Cons a ds1)
  then have "\<exists>l r. T = Branching l r" using branch_inv_Leaf by (cases T) auto
  then obtain l r where p_lr: "T = Branching l r" by auto
  show ?case
    proof (cases a)
      assume atrue: "a"
      then have "branch (ds1 @ ds2 @ [d]) l" using p_lr Cons(2) branch_inv_Branching by auto
      then have "internal ds1 l" using Cons(1) by auto
      then show "internal (a # ds1) T" using p_lr atrue by auto
    next
      assume afalse: "~a"
      then have "branch ((ds1) @ ds2 @[d]) r" using p_lr Cons(2) branch_inv_Branching by auto
      then have "internal ds1 r" using Cons(1) by auto
      then show "internal (a # ds1) T" using p_lr afalse by auto
    qed
next
  case (Nil)
  then have "\<exists>l r. T = Branching l r" using branch_inv_Leaf by (cases T) auto 
  then show ?case by auto
qed


fun parent :: "dir list \<Rightarrow> dir list" where
  "parent ds = tl ds"


subsection \<open>Deleting Nodes\<close>

fun delete :: "dir list \<Rightarrow> tree \<Rightarrow> tree" where
  "delete [] T = Leaf"
| "delete (True#ds)  (Branching T\<^sub>1 T\<^sub>2) = Branching (delete ds T\<^sub>1) T\<^sub>2"
| "delete (False#ds) (Branching T\<^sub>1 T\<^sub>2) = Branching T\<^sub>1 (delete ds T\<^sub>2)"
| "delete (a#ds) Leaf = Leaf"

lemma delete_Leaf: "delete T Leaf = Leaf" by (cases T) auto

lemma path_delete: 
  assumes "path p (delete ds T)"
  shows "path p T " (* What a huge proof... But the four cases can be proven shorter *)
using assms proof (induction p arbitrary: T ds)
  case Nil 
  then show ?case by simp
next
  case (Cons a p)
  then obtain b ds' where bds'_p: "ds=b#ds'" by (cases ds) auto

  have "\<exists>dT1 dT2. delete ds T = Branching dT1 dT2" using Cons path_inv_Cons by auto
  then obtain dT1 dT2 where "delete ds T = Branching dT1 dT2" by auto

  then have "\<exists>T1 T2. T=Branching T1 T2" (* Is there a lemma hidden here that I could extract? *)
        by (cases T; cases ds) auto
  then obtain T1 T2 where T1T2_p: "T=Branching T1 T2" by auto

  {
    assume a_p: "a"
    assume b_p: "\<not>b"
    have "path (a # p) (delete ds T)" using Cons by -
    then have "path (a # p) (Branching (T1) (delete ds' T2))" using b_p bds'_p T1T2_p by auto
    then have "path p T1" using a_p by auto
    then have ?case using T1T2_p a_p by auto
  }
  moreover
  {
    assume a_p: "\<not>a"
    assume b_p: "b"
    have "path (a # p) (delete ds T)" using Cons by -
    then have "path (a # p) (Branching (delete ds' T1) T2)" using b_p bds'_p T1T2_p by auto
    then have "path p T2" using a_p by auto
    then have ?case using T1T2_p a_p by auto
  }
  moreover
  {
    assume a_p: "a"
    assume b_p: "b"
    have "path (a # p) (delete ds T)" using Cons by -
    then have "path (a # p) (Branching (delete ds' T1) T2)" using b_p bds'_p T1T2_p by auto
    then have "path p (delete ds' T1)" using a_p by auto
    then have "path p T1" using Cons by auto
    then have ?case using T1T2_p a_p by auto
  }
  moreover
  {
    assume a_p: "\<not>a"
    assume b_p: "\<not>b"
    have "path (a # p) (delete ds T)" using Cons by -
    then have "path (a # p) (Branching T1 (delete ds' T2))" using b_p bds'_p T1T2_p by auto
    then have "path p (delete ds' T2)" using a_p by auto
    then have "path p T2" using Cons by auto
    then have ?case using T1T2_p a_p by auto
  }
  ultimately show ?case by blast
qed

lemma branch_delete:
  assumes "branch p (delete ds T)"
  shows "branch p T \<or> p=ds" (* Adapted from above *)
using assms proof (induction p arbitrary: T ds)
  case Nil 
  then have "delete ds T = Leaf" by (cases "delete ds T") auto
  then have "ds = [] \<or> T = Leaf" using delete.elims by blast 
  then show ?case by auto
next
  case (Cons a p)
  then obtain b ds' where bds'_p: "ds=b#ds'" by (cases ds) auto

  have "\<exists>dT1 dT2. delete ds T = Branching dT1 dT2" using Cons path_inv_Cons branch_is_path by blast
  then obtain dT1 dT2 where "delete ds T = Branching dT1 dT2" by auto

  then have "\<exists>T1 T2. T=Branching T1 T2" (* Is there a lemma hidden here that I could extract? *)
        by (cases T; cases ds) auto
  then obtain T1 T2 where T1T2_p: "T=Branching T1 T2" by auto

  {
    assume a_p: "a"
    assume b_p: "\<not>b"
    have "branch (a # p) (delete ds T)" using Cons by -
    then have "branch (a # p) (Branching (T1) (delete ds' T2))" using b_p bds'_p T1T2_p by auto
    then have "branch p T1" using a_p by auto
    then have ?case using T1T2_p a_p by auto
  }
  moreover
  {
    assume a_p: "\<not>a"
    assume b_p: "b"
    have "branch (a # p) (delete ds T)" using Cons by -
    then have "branch (a # p) (Branching (delete ds' T1) T2)" using b_p bds'_p T1T2_p by auto
    then have "branch p T2" using a_p by auto
    then have ?case using T1T2_p a_p by auto
  }
  moreover
  {
    assume a_p: "a"
    assume b_p: "b"
    have "branch (a # p) (delete ds T)" using Cons by -
    then have "branch (a # p) (Branching (delete ds' T1) T2)" using b_p bds'_p T1T2_p by auto
    then have "branch p (delete ds' T1)" using a_p by auto
    then have "branch p T1 \<or> p = ds'" using Cons by metis
    then have ?case using T1T2_p a_p using bds'_p a_p b_p by auto
  }
  moreover
  {
    assume a_p: "\<not>a"
    assume b_p: "\<not>b"
    have "branch (a # p) (delete ds T)" using Cons by -
    then have "branch (a # p) (Branching T1 (delete ds' T2))" using b_p bds'_p T1T2_p by auto
    then have "branch p (delete ds' T2)" using a_p by auto
    then have "branch p T2 \<or> p = ds'" using Cons by metis
    then have ?case using T1T2_p a_p using bds'_p a_p b_p by auto
  }
  ultimately show ?case by blast
qed
  

lemma branch_delete_postfix: 
  assumes "path p (delete ds T)"
  shows "\<not>(\<exists>c cs. p = ds @ c#cs)" (* Adapted from previous proof *)
using assms proof (induction p arbitrary: T ds)
  case Nil then show ?case by simp
next
  case (Cons a p)
  then obtain b ds' where bds'_p: "ds=b#ds'" by (cases ds) auto

  have "\<exists>dT1 dT2. delete ds T = Branching dT1 dT2" using Cons path_inv_Cons by auto
  then obtain dT1 dT2 where "delete ds T = Branching dT1 dT2" by auto

  then have "\<exists>T1 T2. T=Branching T1 T2" (* Is there a lemma hidden here that I could extract? *)
        by (cases T; cases ds) auto
  then obtain T1 T2 where T1T2_p: "T=Branching T1 T2" by auto

  {
    assume a_p: "a"
    assume b_p: "\<not>b"
    then have ?case using T1T2_p a_p b_p bds'_p by auto
  }
  moreover
  {
    assume a_p: "\<not>a"
    assume b_p: "b"
    then have ?case using T1T2_p a_p b_p bds'_p by auto
  }
  moreover
  {
    assume a_p: "a"
    assume b_p: "b"
    have "path (a # p) (delete ds T)" using Cons by -
    then have "path (a # p) (Branching (delete ds' T1) T2)" using b_p bds'_p T1T2_p by auto
    then have "path p (delete ds' T1)" using a_p by auto
    then have "\<not> (\<exists>c cs. p = ds' @ c # cs)" using Cons by auto
    then have ?case using T1T2_p a_p b_p bds'_p by auto
  }
  moreover
  {
    assume a_p: "\<not>a"
    assume b_p: "\<not>b"
    have "path (a # p) (delete ds T)" using Cons by -
    then have "path (a # p) (Branching T1 (delete ds' T2))" using b_p bds'_p T1T2_p by auto
    then have "path p (delete ds' T2)" using a_p by auto
    then have "\<not> (\<exists>c cs. p = ds' @ c # cs)" using Cons by auto
    then have ?case using T1T2_p a_p b_p bds'_p by auto
  }
  ultimately show ?case by blast
qed

lemma treezise_delete: 
  assumes "internal p T"
  shows "treesize (delete p T) < treesize T"
using assms proof (induction p arbitrary: T)
  case (Nil)
  then have "\<exists>T1 T2. T = Branching T1 T2" by (cases T) auto
  then obtain T1 T2 where T1T2_p: "T = Branching T1 T2" by auto 
  then show ?case by auto
next
  case (Cons a p) 
  then have "\<exists>T1 T2. T = Branching T1 T2" using path_inv_Cons internal_is_path by blast
  then obtain T1 T2 where T1T2_p: "T = Branching T1 T2" by auto
  show ?case
    proof (cases a)
      assume a_p: a
      from a_p have "delete (a#p) T = (Branching (delete p T1) T2)" using T1T2_p by auto
      moreover
      from a_p have "internal p T1" using T1T2_p Cons by auto
      then have "treesize (delete p T1) < treesize T1" using Cons by auto
      ultimately
      show ?thesis using T1T2_p by auto
    next
      assume a_p: "\<not>a"
      from a_p have "delete (a#p) T = (Branching T1 (delete p T2))" using T1T2_p by auto
      moreover
      from a_p have "internal p T2" using T1T2_p Cons by auto
      then have "treesize (delete p T2) < treesize T2" using Cons by auto
      ultimately
      show ?thesis using T1T2_p by auto
    qed
qed


fun cutoff :: "(dir list \<Rightarrow> bool) \<Rightarrow> dir list \<Rightarrow> tree \<Rightarrow> tree" where
  "cutoff red ds (Branching T\<^sub>1 T\<^sub>2) = 
     (if red ds then Leaf else Branching (cutoff red (ds@[Left])  T\<^sub>1) (cutoff red (ds@[Right]) T\<^sub>2))"
| "cutoff red ds Leaf = Leaf"
text \<open>Initially you should call @{const cutoff} with @{term "ds = []"}.
 If all branches are red, then @{const cutoff} gives a subtree.
 If all branches are red, then so are the ones in @{const cutoff}.
 The internal paths of @{const cutoff} are not red.\<close>

lemma treesize_cutoff: "treesize (cutoff red ds T) \<le> treesize T"
proof (induction T arbitrary: ds)
  case Leaf then show ?case by auto
next
  case (Branching T1 T2) 
  then have "treesize (cutoff red (ds@[Left]) T1) + treesize (cutoff red (ds@[Right]) T2) \<le> treesize T1 + treesize T2" using add_mono by blast
  then show ?case by auto
qed

abbreviation anypath :: "tree \<Rightarrow> (dir list \<Rightarrow> bool) \<Rightarrow> bool" where
  "anypath T P \<equiv> \<forall>p. path p T \<longrightarrow> P p"

abbreviation anybranch :: "tree \<Rightarrow> (dir list \<Rightarrow> bool) \<Rightarrow> bool" where
  "anybranch T P \<equiv> \<forall>p. branch p T \<longrightarrow> P p"

abbreviation anyinternal :: "tree \<Rightarrow> (dir list \<Rightarrow> bool) \<Rightarrow> bool" where
  "anyinternal T P \<equiv> \<forall>p. internal p T \<longrightarrow> P p"

lemma cutoff_branch': 
  assumes "anybranch T (\<lambda>b. red(ds@b))"
  shows "anybranch (cutoff red ds T) (\<lambda>b. red(ds@b))"
using assms proof (induction T arbitrary: ds) (* This proof seems a bit excessive for such a simple theorem *)
  case (Leaf) 
  let ?T = "cutoff red ds Leaf"
  {
    fix b
    assume "branch b ?T"
    then have "branch b Leaf" by auto
    then have "red(ds@b)" using Leaf by auto
  }
  then show ?case by simp
next
  case (Branching T\<^sub>1 T\<^sub>2)
  let ?T = "cutoff red ds (Branching T\<^sub>1 T\<^sub>2)"
  from Branching have "\<forall>p. branch (Left#p) (Branching T\<^sub>1 T\<^sub>2) \<longrightarrow> red (ds @ (Left#p))" by blast
  then have "\<forall>p. branch p T\<^sub>1 \<longrightarrow> red (ds @ (Left#p))"  by auto
  then have "anybranch T\<^sub>1 (\<lambda>p. red ((ds @ [Left]) @ p))" by auto
  then have aa: "anybranch (cutoff red (ds @ [Left]) T\<^sub>1) (\<lambda>p. red ((ds @ [Left]) @ p)) 
         " using Branching by blast

  from Branching have "\<forall>p. branch (Right#p) (Branching T\<^sub>1 T\<^sub>2) \<longrightarrow> red (ds @ (Right#p))" by blast
  then have "\<forall>p. branch p T\<^sub>2 \<longrightarrow> red (ds @ (Right#p))" by auto
  then have "anybranch T\<^sub>2 (\<lambda>p. red ((ds @ [Right]) @ p))" by auto
  then have bb: "anybranch (cutoff red (ds @ [Right]) T\<^sub>2) (\<lambda>p. red ((ds @ [Right]) @ p)) 
         " using Branching by blast
  {           
    fix b
    assume b_p: "branch b ?T"
    have "red ds \<or> \<not>red ds" by auto
    then have "red(ds@b)"
      proof
        assume ds_p: "red ds"
        then have "?T = Leaf" by auto
        then have "b = []" using b_p branch_inv_Leaf by auto
        then show "red(ds@b)" using ds_p by auto
      next
        assume ds_p: "\<not>red ds"
        let ?T\<^sub>1' = "cutoff red (ds@[Left])  T\<^sub>1"
        let ?T\<^sub>2' = "cutoff red (ds@[Right]) T\<^sub>2"
        from ds_p have "?T = Branching ?T\<^sub>1' ?T\<^sub>2'" by auto
        from this b_p obtain a b' where "b = a # b' \<and> (a \<longrightarrow> branch b' ?T\<^sub>1') \<and> (\<not>a \<longrightarrow> branch b' ?T\<^sub>2' )" using branch_inv_Branching[of b ?T\<^sub>1' ?T\<^sub>2'] by auto
        then show "red(ds@b)" using aa bb by (cases a) auto
      qed
  }
  then show ?case by blast
qed

lemma cutoff_branch: 
  assumes "anybranch T (\<lambda>p. red p)"
  shows "anybranch (cutoff red [] T) (\<lambda>p. red p)" 
  using assms cutoff_branch'[of T red "[]"] by auto

lemma cutoff_internal': 
  assumes "anybranch T (\<lambda>b. red(ds@b))" 
  shows "anyinternal (cutoff red ds T) (\<lambda>b. \<not>red(ds@b))"
using assms proof (induction T arbitrary: ds) (* This proof seems a bit excessive for such a simple theorem *)
  case (Leaf) then show ?case using internal_inv_Leaf by simp
next                                                     
  case (Branching T\<^sub>1 T\<^sub>2)
  let ?T = "cutoff red ds (Branching T\<^sub>1 T\<^sub>2)"
  from Branching have "\<forall>p. branch (Left#p) (Branching T\<^sub>1 T\<^sub>2) \<longrightarrow> red (ds @ (Left#p))" by blast
  then have "\<forall>p. branch p T\<^sub>1 \<longrightarrow> red (ds @ (Left#p))" by auto
  then have "anybranch T\<^sub>1 (\<lambda>p. red ((ds @ [Left]) @ p))" by auto
  then have aa: "anyinternal (cutoff red (ds @ [Left]) T\<^sub>1) (\<lambda>p. \<not> red ((ds @ [Left]) @ p))" using Branching by blast

  from Branching have "\<forall>p. branch (Right#p) (Branching T\<^sub>1 T\<^sub>2) \<longrightarrow> red (ds @ (Right#p))" by blast
  then have "\<forall>p. branch p T\<^sub>2 \<longrightarrow> red (ds @ (Right#p))" by auto
  then have "anybranch T\<^sub>2 (\<lambda>p. red ((ds @ [Right]) @ p))" by auto
  then have bb: "anyinternal (cutoff red (ds @ [Right]) T\<^sub>2) (\<lambda>p. \<not> red ((ds @ [Right]) @ p))" using Branching by blast
  {
    fix p
    assume b_p: "internal p ?T"
    then have ds_p: "\<not>red ds" using internal_inv_Leaf by auto
    have "p=[] \<or> p\<noteq>[]" by auto
    then have "\<not>red(ds@p)"
      proof
        assume "p=[]" then show "\<not>red(ds@p)" using ds_p by auto
      next
        let ?T\<^sub>1' = "cutoff red (ds@[Left])  T\<^sub>1"
        let ?T\<^sub>2' = "cutoff red (ds@[Right]) T\<^sub>2"
        assume "p\<noteq>[]"
        moreover
        have "?T = Branching ?T\<^sub>1' ?T\<^sub>2'" using ds_p by auto
        ultimately
        obtain a p' where b_p: "p = a # p' \<and>
             (a \<longrightarrow> internal p' (cutoff red (ds @ [Left]) T\<^sub>1)) \<and>
             (\<not> a \<longrightarrow> internal p' (cutoff red (ds @ [Right]) T\<^sub>2))" 
          using b_p internal_inv_Branching[of p ?T\<^sub>1' ?T\<^sub>2'] by auto
        then have "\<not>red(ds @ [a] @ p')" using aa bb by (cases a) auto
        then show "\<not>red(ds @ p)" using b_p by simp
      qed
  }
  then show ?case by blast
qed

lemma cutoff_internal:
  assumes  "anybranch T red"
  shows "anyinternal (cutoff red [] T) (\<lambda>p. \<not>red p)" 
  using assms cutoff_internal'[of T red "[]"] by auto

lemma cutoff_branch_internal': 
  assumes "anybranch T red"
  shows "anyinternal (cutoff red [] T) (\<lambda>p. \<not>red p) \<and> anybranch (cutoff red [] T) (\<lambda>p. red p)" 
  using assms cutoff_internal[of T] cutoff_branch[of T] by blast

lemma cutoff_branch_internal: 
  assumes "anybranch T red"
  shows "\<exists>T'. anyinternal T' (\<lambda>p. \<not>red p) \<and> anybranch T' (\<lambda>p. red p)" 
  using assms cutoff_branch_internal' by blast


section \<open>Possibly Infinite Trees\<close>
text \<open>Possibly infinite trees are of type @{typ "dir list set"}.\<close>

abbreviation wf_tree :: "dir list set \<Rightarrow> bool" where
  "wf_tree T \<equiv> (\<forall>ds d. (ds @ d) \<in> T \<longrightarrow> ds \<in> T)"

text \<open>The subtree in with root r\<close>
fun subtree :: "dir list set \<Rightarrow> dir list \<Rightarrow> dir list set" where 
  "subtree T r = {ds \<in> T. \<exists>ds'. ds = r @ ds'}" 

text \<open>A subtree of a tree is either in the left branch, the right branch, or is the tree itself\<close>
lemma subtree_pos: 
  "subtree T ds \<subseteq> subtree T (ds @ [Left]) \<union> subtree T (ds @ [Right]) \<union> {ds}"
proof (rule subsetI; rule Set.UnCI)
  let ?subtree = "subtree T"
  fix x
  assume asm: "x \<in> ?subtree ds"
  assume "x \<notin> {ds}"
  then have "x \<noteq> ds" by simp
  then have "\<exists>e d. x = ds @ [d] @ e" using asm list.exhaust by auto
  then have "(\<exists>e. x = ds @ [Left] @ e) \<or> (\<exists>e. x = ds @ [Right] @ e)" using bool.exhaust by auto
  then show "x \<in> ?subtree (ds @ [Left]) \<union> ?subtree (ds @ [Right])" using asm by auto
qed


subsection \<open>Infinite Paths\<close>

abbreviation wf_infpath :: "(nat \<Rightarrow> 'a list) \<Rightarrow> bool" where
  "wf_infpath f \<equiv> (f 0 = []) \<and> (\<forall>n. \<exists>a. f (Suc n) = (f n) @ [a])"

lemma infpath_length:
  assumes "wf_infpath f"
  shows "length (f n) = n"
using assms proof (induction n)
  case 0 then show ?case by auto
next
  case (Suc n) then show ?case by (metis length_append_singleton)
qed

lemma chain_prefix: 
  assumes "wf_infpath f"
  assumes "n\<^sub>1 \<le> n\<^sub>2"
  shows "\<exists>a. (f n\<^sub>1) @ a = (f n\<^sub>2)"
using assms proof (induction n\<^sub>2)
  case (Suc n\<^sub>2)
  then have "n\<^sub>1 \<le> n\<^sub>2 \<or> n\<^sub>1 = Suc n\<^sub>2" by auto
  then show ?case
    proof
      assume "n\<^sub>1 \<le> n\<^sub>2"
      then obtain a where a: "f n\<^sub>1 @ a = f n\<^sub>2" using Suc by auto
      have b: "\<exists>b. f (Suc n\<^sub>2) = f n\<^sub>2 @ [b]" using Suc by auto 
      from a b have "\<exists>b. f n\<^sub>1 @ (a @ [b]) = f (Suc n\<^sub>2)" by auto
      then show "\<exists>c. f n\<^sub>1 @ c = f (Suc n\<^sub>2)" by blast
    next
      assume "n\<^sub>1 = Suc n\<^sub>2"
      then have "f n\<^sub>1 @ [] = f (Suc n\<^sub>2)" by auto
      then show "\<exists>a. f n\<^sub>1 @ a = f (Suc n\<^sub>2)" by auto
    qed
qed auto

text \<open>If we make a lookup in a list, then looking up in an extension gives us the same value.\<close>
lemma ith_in_extension:
  assumes chain: "wf_infpath f"
  assumes smalli: "i < length (f n\<^sub>1)"
  assumes n\<^sub>1n\<^sub>2: "n\<^sub>1 \<le> n\<^sub>2"
  shows "f n\<^sub>1 ! i = f n\<^sub>2 ! i"
proof -
  from chain n\<^sub>1n\<^sub>2 have "\<exists>a. f n\<^sub>1 @ a = f n\<^sub>2" using chain_prefix by blast
  then obtain a where a_p: "f n\<^sub>1 @ a = f n\<^sub>2" by auto
  have "(f n\<^sub>1 @ a) ! i = f n\<^sub>1 ! i" using smalli by (simp add: nth_append) 
  then show ?thesis using a_p by auto
qed


section \<open>König's Lemma\<close>

lemma inf_subs: 
  assumes inf: "\<not>finite(subtree T ds)"
  shows "\<not>finite(subtree T (ds @ [Left])) \<or> \<not>finite(subtree T (ds @ [Right]))"
proof -
  let ?subtree = "subtree T"
  {
    assume asms: "finite(?subtree(ds @ [Left]))"
                 "finite(?subtree(ds @ [Right]))"
    have "?subtree ds \<subseteq> ?subtree (ds @ [Left] ) \<union> ?subtree (ds @ [Right]) \<union> {ds} " 
      using subtree_pos by auto
    then have "finite(?subtree (ds))" using asms by (simp add: finite_subset)
  } 
  then show "\<not>finite(?subtree (ds @ [Left])) \<or> \<not>finite(?subtree (ds @ [Right]))" using inf by auto
qed

fun buildchain :: "(dir list \<Rightarrow> dir list) \<Rightarrow> nat \<Rightarrow> dir list" where
  "buildchain next 0 = []"
| "buildchain next (Suc n) = next (buildchain next n)"

lemma konig:
  assumes inf: "\<not>finite T"
  assumes wellformed: "wf_tree T"
  shows "\<exists>c. wf_infpath c \<and> (\<forall>n. (c n) \<in> T)"
proof
  let ?subtree = "subtree T"
  let ?nextnode = "\<lambda>ds. (if \<not>finite (?subtree (ds @ [Left])) then ds @ [Left] else ds @ [Right])" 

  let ?c = "buildchain ?nextnode"

  have is_chain: "wf_infpath ?c" by auto

  from wellformed have prefix: "\<forall>ds d. (ds @ d) \<in> T \<longrightarrow> ds \<in> T" by blast

  { 
    fix n
    have "(?c n) \<in> T \<and> \<not>finite (?subtree (?c n))"
      proof (induction n)
        case 0
        have "\<exists>ds. ds \<in> T" using inf by (simp add: not_finite_existsD)
        then obtain ds where "ds \<in> T" by auto
        then have "([]@ds) \<in> T" by auto
        then have "[] \<in> T" using prefix by blast 
        then show ?case using inf by auto
      next
        case (Suc n)
        from Suc have next_in:  "(?c n) \<in> T" by auto
        from Suc have next_inf: "\<not>finite (?subtree (?c n))" by auto

        from next_inf have next_next_inf:
           "\<not>finite (?subtree (?nextnode (?c n)))" 
              using inf_subs by auto
        then have "\<exists>ds. ds \<in> ?subtree (?nextnode (?c n))"
          by (simp add: not_finite_existsD)
        then obtain ds where dss: "ds \<in> ?subtree (?nextnode (?c n))" by auto
        then have "ds \<in> T" "\<exists>suf. ds = (?nextnode (?c n)) @ suf" by auto
        then obtain suf where "ds \<in> T \<and> ds = (?nextnode (?c n)) @ suf" by auto
        then have "(?nextnode (?c n)) \<in> T"
          using prefix by blast
              
        then have "(?c (Suc n)) \<in> T" by auto
        then show ?case using next_next_inf by auto
      qed
  }
  then show "wf_infpath ?c \<and> (\<forall>n. (?c n)\<in> T) " using is_chain by auto
qed

end
