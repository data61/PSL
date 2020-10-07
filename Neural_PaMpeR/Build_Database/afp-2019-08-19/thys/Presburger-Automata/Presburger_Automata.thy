(*  Title:      Presburger-Automata/Presburger_Automata.thy
    Author:     Markus Reiter and Stefan Berghofer, TU Muenchen, 2008-2009
*)

theory Presburger_Automata
imports DFS "HOL-Library.Nat_Bijection"
begin

section \<open>General automata\<close>

definition
  "reach tr p as q = (q = foldl tr p as)"

lemma reach_nil: "reach tr p [] p" by (simp add: reach_def)

lemma reach_snoc: "reach tr p bs q \<Longrightarrow> reach tr p (bs @ [b]) (tr q b)"
  by (simp add: reach_def)

lemma reach_nil_iff: "reach tr p [] q = (p = q)" by (auto simp add: reach_def)

lemma reach_snoc_iff: "reach tr p (bs @ [b]) k = (\<exists>q. reach tr p bs q \<and> k = tr q b)"
  by (auto simp add: reach_def)

lemma reach_induct [consumes 1, case_names Nil snoc, induct set: reach]:
  assumes "reach tr p w q"
  and "P [] p"
  and  "\<And>k x y. \<lbrakk>reach tr p x k; P x k\<rbrakk> \<Longrightarrow> P (x @ [y]) (tr k y)"
  shows "P w q"
using assms by (induct w arbitrary: q rule: rev_induct) (simp add: reach_def)+

lemma reach_trans: "\<lbrakk>reach tr p a r; reach tr r b q\<rbrakk> \<Longrightarrow> reach tr p (a @ b) q" 
  by (simp add: reach_def)

lemma reach_inj: "\<lbrakk>reach tr p a q; reach tr p a q'\<rbrakk> \<Longrightarrow> q = q'"
  by (simp add: reach_def)

definition
  "accepts tr P s as = P (foldl tr s as)"

locale Automaton =
  fixes trans :: "'a \<Rightarrow> 'b \<Rightarrow> 'a"
  and is_node :: "'a \<Rightarrow> bool"
  and is_alpha :: "'b \<Rightarrow> bool"
  assumes trans_is_node: "\<And>q a. \<lbrakk>is_node q; is_alpha a\<rbrakk> \<Longrightarrow> is_node (trans q a)"
begin

lemma steps_is_node:
  assumes "is_node q"
  and "list_all is_alpha w"
  shows "is_node (foldl trans q w)"
  using assms by (induct w arbitrary: q) (simp add: trans_is_node)+

lemma reach_is_node: "\<lbrakk>reach trans p w q; is_node p; list_all is_alpha w\<rbrakk> \<Longrightarrow> is_node q"
  by (simp add: steps_is_node reach_def)

end


section \<open>BDDs\<close>

definition
  is_alph :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "is_alph n = (\<lambda>w. length w = n)"

datatype 'a bdd = Leaf 'a | Branch "'a bdd" "'a bdd" for map: bdd_map

primrec bddh :: "nat \<Rightarrow> 'a bdd \<Rightarrow> bool"
where
  "bddh n (Leaf x) = True"
| "bddh n (Branch l r) = (case n of 0 \<Rightarrow> False | Suc m \<Rightarrow> bddh m l \<and> bddh m r)"

lemma bddh_ge:
  assumes "m \<ge> n"
  assumes "bddh n bdd"
  shows "bddh m bdd"
using assms
proof (induct bdd arbitrary: n m)
  case (Branch l r)
  then obtain v where V: "n = Suc v" by (cases n) simp+
  show ?case proof (cases "n = m")
    case True
    with Branch show ?thesis by simp
  next
    case False
    with Branch have "\<exists>w. m = Suc w \<and> n \<le> w" by (cases m) simp+
    then obtain w where W: "m = Suc w \<and> n \<le> w" ..
    with Branch V have "v \<le> w \<and> bddh v l \<and> bddh v r" by simp
    with Branch have "bddh w l \<and> bddh w r" by blast
    with W show ?thesis by simp
  qed
qed simp

abbreviation "bdd_all \<equiv> pred_bdd"

fun bdd_lookup :: "'a bdd \<Rightarrow> bool list \<Rightarrow> 'a"
where
  "bdd_lookup (Leaf x) bs = x"
| "bdd_lookup (Branch l r) (b#bs) = bdd_lookup (if b then r else l) bs"

lemma bdd_all_bdd_lookup: "\<lbrakk>bddh (length ws) bdd; bdd_all P bdd\<rbrakk> \<Longrightarrow> P (bdd_lookup bdd ws)"
  by (induct bdd ws rule: bdd_lookup.induct) simp+

lemma bdd_all_bdd_lookup_iff: "bddh n bdd \<Longrightarrow> bdd_all P bdd = (\<forall>ws. length ws = n \<longrightarrow> P (bdd_lookup bdd ws))"
  apply (rule iffI)
  apply (simp add: bdd_all_bdd_lookup)
  proof (induct bdd arbitrary: n)
    case Leaf thus ?case
      apply simp
      apply (erule mp)
      apply (rule_tac x="replicate n False" in exI, simp)
      done
  next
    case (Branch l r n)
    then obtain k where k: "n = Suc k" by (cases n) simp+
    from Branch have R: "\<And>ws. length ws = n \<Longrightarrow> P (bdd_lookup (Branch l r) ws)" by simp
    have "\<And>ws. length ws = k \<Longrightarrow> P (bdd_lookup l ws) \<and> P (bdd_lookup r ws)"
    proof -
      fix ws :: "bool list" assume H: "length ws = k"
      with k have "length (False#ws) = n" by simp
      hence 1: "P (bdd_lookup (Branch l r) (False#ws))" by (rule R)
      from H k have "length (True#ws) = n" by simp
      hence "P (bdd_lookup (Branch l r) (True#ws))" by (rule R)
      with 1 show "P (bdd_lookup l ws) \<and> P (bdd_lookup r ws)" by simp
    qed
    with Branch k show ?case by auto
  qed

lemma bdd_all_bdd_map:
  assumes "bdd_all P bdd"
  and "\<And>a. P a \<Longrightarrow> Q (f a)"
  shows "bdd_all Q (bdd_map f bdd)"
  using assms by (induct bdd) simp+

lemma bddh_bdd_map:
  shows "bddh n (bdd_map f bdd) = bddh n bdd"
proof
  assume "bddh n (bdd_map f bdd)" thus "bddh n bdd" proof (induct bdd arbitrary: n)
    case (Branch l r n)
    then obtain k where "n = Suc k" by (cases n) simp+
    with Branch show ?case by simp
  qed simp
next
  assume "bddh n bdd" thus "bddh n (bdd_map f bdd)" proof (induct bdd arbitrary: n)
    case (Branch l r n)
    then obtain k where "n = Suc k" by (cases n) simp+
    with Branch show ?case by simp
  qed simp
qed

lemma bdd_map_bdd_lookup:
  assumes "bddh (length ws) bdd"
  shows "bdd_lookup (bdd_map f bdd) ws = f (bdd_lookup bdd ws)"
using assms by (induct bdd ws rule: bdd_lookup.induct) (auto simp add: bddh_bdd_map)+

fun bdd_binop :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a bdd \<Rightarrow> 'b bdd \<Rightarrow> 'c bdd"
where
  "bdd_binop f (Leaf x) (Leaf y) = Leaf (f x y)"
| "bdd_binop f (Branch l r) (Leaf y) = Branch (bdd_binop f l (Leaf y)) (bdd_binop f r (Leaf y))"
| "bdd_binop f (Leaf x) (Branch l r) = Branch (bdd_binop f (Leaf x) l) (bdd_binop f (Leaf x) r)"
| "bdd_binop f (Branch l\<^sub>1 r\<^sub>1) (Branch l\<^sub>2 r\<^sub>2) = Branch (bdd_binop f l\<^sub>1 l\<^sub>2) (bdd_binop f r\<^sub>1 r\<^sub>2)"

lemma bddh_binop: "bddh n (bdd_binop f l r) = (bddh n l \<and> bddh n r)"
  by (induct f l r arbitrary: n rule: bdd_binop.induct) (auto split: nat.split_asm)

lemma bdd_lookup_binop: "\<lbrakk>bddh (length bs) l; bddh (length bs) r\<rbrakk> \<Longrightarrow>
  bdd_lookup (bdd_binop f l r) bs = f (bdd_lookup l bs) (bdd_lookup r bs)"
  apply (induct f l r arbitrary: bs rule: bdd_binop.induct)
  apply simp
  apply (case_tac bs)
  apply simp+
  apply (case_tac bs)
  apply simp+
  apply (case_tac bs)
  apply simp+
  done

lemma bdd_all_bdd_binop:
  assumes "bdd_all P bdd"
  and "bdd_all Q bdd'"
  and "\<And>a b. \<lbrakk>P a; Q b\<rbrakk> \<Longrightarrow> R (f a b)"
  shows "bdd_all R (bdd_binop f bdd bdd')"
  using assms by (induct f bdd bdd' rule: bdd_binop.induct) simp+

lemma insert_list_idemp[simp]:
  "List.insert x (List.insert x xs) = List.insert x xs"
  by simp

primrec add_leaves :: "'a bdd \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "add_leaves (Leaf x) xs = List.insert x xs"
| "add_leaves (Branch b c) xs = add_leaves c (add_leaves b xs)"

lemma add_leaves_bdd_lookup:
  "bddh n b \<Longrightarrow> (x \<in> set (add_leaves b xs)) = ((\<exists>bs. x = bdd_lookup b bs \<and> is_alph n bs) \<or> x \<in> set xs)"
  apply (induct b arbitrary: xs n)
  apply (auto split: nat.split_asm)
  apply (rule_tac x="replicate n arbitrary" in exI)
  apply (simp add: is_alph_def)
  apply (rule_tac x="True # bs" in exI)
  apply (simp add: is_alph_def)
  apply (rule_tac x="False # bs" in exI)
  apply (simp add: is_alph_def)
  apply (case_tac bs)
  apply (simp add: is_alph_def)
  apply (simp add: is_alph_def)
  apply (drule_tac x=list in spec)
  apply (case_tac a)
  apply simp
  apply simp
  apply (rule_tac x=list in exI)
  apply simp
  done

lemma add_leaves_bdd_all_eq:
  "list_all P (add_leaves tr xs) \<longleftrightarrow> bdd_all P tr \<and> list_all P xs"
  by (induct tr arbitrary: xs) (auto simp add: list_all_iff)

lemmas add_leaves_bdd_all_eq' =
  add_leaves_bdd_all_eq [where xs="[]", simplified, symmetric]

lemma add_leaves_mono:
  "set xs \<subseteq> set ys \<Longrightarrow> set (add_leaves tr xs) \<subseteq> set (add_leaves tr ys)"
  by (induct tr arbitrary: xs ys) auto

lemma add_leaves_binop_subset:
  "set (add_leaves (bdd_binop f b b') [f x y. x \<leftarrow> xs, y \<leftarrow> ys]) \<subseteq>
   (\<Union>x\<in>set (add_leaves b xs). \<Union>y\<in>set (add_leaves b' ys). {f x y})" (is "?A \<subseteq> ?B")
proof -
  have "?A \<subseteq> (\<Union>x\<in>set (add_leaves b xs). f x ` set (add_leaves b' ys))"
  proof (induct f b b' arbitrary: xs ys rule: bdd_binop.induct)
    case (1 f x y xs ys) then show ?case by auto
  next
    case (2 f l r y xs ys) then show ?case
    apply auto
    apply (drule_tac ys1="[f x y. x \<leftarrow> add_leaves l xs, y \<leftarrow> List.insert y ys]" in
      rev_subsetD [OF _ add_leaves_mono])
    apply auto
    apply (drule meta_spec, drule meta_spec, drule subsetD, assumption)
    apply simp
    done
  next
    case (3 f x l r xs ys) then show ?case
    apply auto
    apply (drule_tac ys1="[f x y. x \<leftarrow> List.insert x xs, y \<leftarrow> add_leaves l ys]" in
      rev_subsetD [OF _ add_leaves_mono])
    apply auto
    apply (drule meta_spec, drule meta_spec, drule subsetD, assumption)
    apply simp
    done
  next
    case (4 f l\<^sub>1 r\<^sub>1 l\<^sub>2 r\<^sub>2 xs ys) then show ?case
    apply auto
    apply (drule_tac ys1="[f x y. x \<leftarrow> add_leaves l\<^sub>1 xs, y \<leftarrow> add_leaves l\<^sub>2 ys]" in
      rev_subsetD [OF _ add_leaves_mono])
    apply simp
    apply (drule meta_spec, drule meta_spec, drule subsetD, assumption)
    apply simp
    done
  qed
  also have "(\<Union>x\<in>set (add_leaves b xs). f x ` set (add_leaves b' ys)) = ?B"
    by auto
  finally show ?thesis .
qed


section \<open>DFAs\<close>

type_synonym bddtable = "nat bdd list"
type_synonym astate = "bool list"
type_synonym dfa = "bddtable \<times> astate"

definition
  dfa_is_node :: "dfa \<Rightarrow> nat \<Rightarrow> bool" where
  "dfa_is_node A = (\<lambda>q. q < length (fst A))"

definition
  wf_dfa :: "dfa \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_dfa A n =
    (list_all (bddh n) (fst A) \<and>
     list_all (bdd_all (dfa_is_node A)) (fst A) \<and>
     length (snd A) = length (fst A) \<and>
     length (fst A) > 0)"

definition
  dfa_trans :: "dfa \<Rightarrow> nat \<Rightarrow> bool list \<Rightarrow> nat" where
  "dfa_trans A q bs \<equiv> bdd_lookup (fst A ! q) bs"
definition
  dfa_accepting :: "dfa \<Rightarrow> nat \<Rightarrow> bool" where
  "dfa_accepting A q = snd A ! q"

locale aut_dfa =
  fixes A n
  assumes well_formed: "wf_dfa A n"

sublocale aut_dfa < Automaton "dfa_trans A" "dfa_is_node A" "is_alph n"
proof
  fix q a
  assume Q: "dfa_is_node A q" and A: "is_alph n a"
  hence QL: "q < length (fst A)" by (simp add: dfa_is_node_def)
  with well_formed A have H: "bddh (length a) (fst A ! q)" by (simp add: wf_dfa_def list_all_iff is_alph_def)
  from QL well_formed have "bdd_all (dfa_is_node A) (fst A ! q)" by (simp add: wf_dfa_def list_all_iff)
  with H show "dfa_is_node A (dfa_trans A q a)" by (simp add: dfa_trans_def bdd_all_bdd_lookup)
qed

context aut_dfa begin
lemmas trans_is_node = trans_is_node
lemmas steps_is_node = steps_is_node
lemmas reach_is_node = reach_is_node
end

lemmas dfa_trans_is_node = aut_dfa.trans_is_node [OF aut_dfa.intro]
lemmas dfa_steps_is_node = aut_dfa.steps_is_node [OF aut_dfa.intro]
lemmas dfa_reach_is_node = aut_dfa.reach_is_node [OF aut_dfa.intro]

abbreviation "dfa_steps A \<equiv> foldl (dfa_trans A)"
abbreviation "dfa_accepts A \<equiv> accepts (dfa_trans A) (dfa_accepting A) 0"
abbreviation "dfa_reach A \<equiv> reach (dfa_trans A)"

lemma dfa_startnode_is_node: "wf_dfa A n \<Longrightarrow> dfa_is_node A 0"
  by (simp add: dfa_is_node_def wf_dfa_def)

subsection \<open>Minimization\<close>

primrec make_tr :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
where
  "make_tr f 0 i = []"
| "make_tr f (Suc n) i = f i # make_tr f n (Suc i)"

primrec fold_map_idx :: "(nat \<Rightarrow> 'c \<Rightarrow> 'a \<Rightarrow> 'c \<times> 'b) \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> 'a list \<Rightarrow> 'c \<times> 'b list"
where
  "fold_map_idx f i y [] = (y, [])"
| "fold_map_idx f i y (x # xs) =
     (let (y', x') = f i y x in
      let (y'', xs') = fold_map_idx f (Suc i) y' xs in (y'', x' # xs'))"

definition init_tr :: "dfa \<Rightarrow> bool list list" where
  "init_tr = (\<lambda>(bd,as). make_tr (\<lambda>i. make_tr (\<lambda>j. as ! i \<noteq> as ! j) i 0) (length bd - 1) 1)"

definition tr_lookup :: "bool list list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "tr_lookup = (\<lambda>T i j. (if i = j then False else if i > j then T ! (i - 1) ! j else T ! (j - 1) ! i))"

fun check_eq :: "nat bdd \<Rightarrow> nat bdd \<Rightarrow> bool list list \<Rightarrow> bool" where
  "check_eq (Leaf i) (Leaf j) T = (\<not> tr_lookup T i j)" |
  "check_eq (Branch l r) (Leaf i) T = (check_eq l (Leaf i) T \<and> check_eq r (Leaf i) T)" |
  "check_eq (Leaf i) (Branch l r) T = (check_eq (Leaf i) l T \<and> check_eq (Leaf i) r T)" |
  "check_eq (Branch l1 r1) (Branch l2 r2) T = (check_eq l1 l2 T \<and> check_eq r1 r2 T)"

definition iter :: "dfa \<Rightarrow> bool list list \<Rightarrow> bool \<times> bool list list" where
  "iter = (\<lambda>(bd,as) T. fold_map_idx (\<lambda>i. fold_map_idx (\<lambda>j c b.
     let b' = b \<or> \<not> check_eq (bd ! i) (bd ! j) T
     in (c \<or> b \<noteq> b', b')) 0) 1 False T)"

definition count_tr :: "bool list list \<Rightarrow> nat" where
  "count_tr = foldl (foldl (\<lambda>y x. if x then y else Suc y)) 0"

lemma fold_map_idx_fst_snd_eq:
  assumes f: "\<And>i c x. fst (f i c x) = (c \<or> x \<noteq> snd (f i c x))"
  shows "fst (fold_map_idx f i c xs) = (c \<or> xs \<noteq> snd (fold_map_idx f i c xs))"
  by (induct xs arbitrary: i c) (simp_all add: split_beta f)

lemma foldl_mono:
  assumes f: "\<And>x y y'. y < y' \<Longrightarrow> f y x < f y' x" and y: "y < y'"
  shows "foldl f y xs < foldl f y' xs" using y
  by (induct xs arbitrary: y y') (simp_all add: f)

lemma fold_map_idx_count:
  assumes f: "\<And>i c x y. fst (f i c x) = (c \<or> g y (snd (f i c x)) < (g y x::nat))"
  and f': "\<And>i c x y. g y (snd (f i c x)) \<le> g y x"
  and g: "\<And>x y y'. y < y' \<Longrightarrow> g y x < g y' x"
  shows "fst (fold_map_idx f i c xs) =
    (c \<or> foldl g y (snd (fold_map_idx f i c xs)) < foldl g y xs)"
  and "foldl g y (snd (fold_map_idx f i c xs)) \<le> foldl g y xs"
proof (induct xs arbitrary: i c y)
  case (Cons x xs) {
    case 1
    show ?case using f' [of y i c x, simplified le_eq_less_or_eq]
      by (auto simp add: split_beta Cons(1) [of _ _ "g y (snd (f i c x))"] f [of _ _ _ y]
        intro: less_le_trans foldl_mono g Cons)
  next
    case 2
    show ?case using f' [of y i c x, simplified le_eq_less_or_eq]
      by (auto simp add: split_beta intro: order_trans less_imp_le
        intro!: foldl_mono g Cons) }
qed simp_all

lemma iter_count:
  assumes eq: "(b, T') = iter (bd, as) T"
  and b: "b"
  shows "count_tr T' < count_tr T"
proof -
  let ?f = "fold_map_idx (\<lambda>i. fold_map_idx (\<lambda>j c b.
    let b' = b \<or> \<not> check_eq (bd ! i) (bd ! j) T
    in (c \<or> b \<noteq> b', b')) 0) (Suc 0) False T"
  from eq [symmetric] b have "fst ?f"
    by (auto simp add: iter_def)
  also have "fst ?f = (False \<or> count_tr (snd ?f) < count_tr T)"
    unfolding count_tr_def
    by (rule fold_map_idx_count foldl_mono | simp)+
  finally show ?thesis
    by (simp add: eq [THEN arg_cong, of snd, simplified] iter_def)
qed

function fixpt :: "dfa \<Rightarrow> bool list list \<Rightarrow> bool list list" where
  "fixpt M T = (let (b, T2) = iter M T in if b then fixpt M T2 else T2)"
by auto
termination by (relation "measure (\<lambda>(M, T). count_tr T)") (auto simp: iter_count)

lemma fixpt_True[simp]: "fst (iter M T) \<Longrightarrow> fixpt M T = fixpt M (snd (iter M T))"
  by (simp add: split_beta)

lemma fixpt_False[simp]: "\<not> (fst (iter M T)) \<Longrightarrow> fixpt M T = T"
  by (simp add: split_beta iter_def fold_map_idx_fst_snd_eq)

declare fixpt.simps [simp del]

lemma fixpt_induct:
  assumes H: "\<And>M T. (fst (iter M T) \<Longrightarrow> P M (snd (iter M T))) \<Longrightarrow> P M T"
  shows "P M T"
proof (induct M T rule: fixpt.induct)
  case (1 M T)
  show ?case by (rule H) (rule 1 [OF refl prod.collapse])
qed

definition dist_nodes :: "dfa \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "dist_nodes = (\<lambda>M n m p q. \<exists>w. length w = n \<and> list_all (is_alph m) w \<and>
     dfa_accepting M (dfa_steps M p w) \<noteq> dfa_accepting M (dfa_steps M q w))"

definition wf_tr :: "dfa \<Rightarrow> bool list list \<Rightarrow> bool" where
  "wf_tr = (\<lambda>M T. length T = length (fst M) - 1 \<and> (\<forall>i < length T. length (T ! i) = i + 1))"

lemma make_tr_len: "length (make_tr f n i) = n"
  by (induct n arbitrary: i) simp_all

lemma make_tr_nth: "j < n \<Longrightarrow> make_tr f n i ! j = f (i + j)"
  by (induct n arbitrary: i j) (auto simp add: nth_Cons')

lemma init_tr_wf: "wf_tr M (init_tr M)"
  by (simp add: init_tr_def wf_tr_def split_beta make_tr_len make_tr_nth)

lemma fold_map_idx_len: "length (snd (fold_map_idx f i y xs)) = length xs"
  by (induct xs arbitrary: i y) (simp_all add: split_beta)

lemma fold_map_idx_nth: "j < length xs \<Longrightarrow>
  snd (fold_map_idx f i y xs) ! j = snd (f (i + j) (fst (fold_map_idx f i y (take j xs))) (xs ! j))"
  by (induct xs arbitrary: i j y) (simp_all add: split_beta nth_Cons' take_Cons')

lemma init_tr_dist_nodes:
  assumes "dfa_is_node M q" and "p < q"
  shows "tr_lookup (init_tr M) q p = dist_nodes M 0 v p q"
proof -
  have 1: "dist_nodes M 0 v p q = (snd M ! p \<noteq> snd M ! q)" by (simp add: dist_nodes_def dfa_accepting_def)
  from assms have "tr_lookup (init_tr M) q p = (snd M ! p \<noteq> snd M ! q)"
    by (auto simp add: dfa_is_node_def init_tr_def tr_lookup_def make_tr_nth split_beta)
  with 1 show ?thesis by simp
qed

lemma dist_nodes_suc:
  "dist_nodes M (Suc n) v p q = (\<exists>bs. is_alph v bs \<and> dist_nodes M n v (dfa_trans M p bs) (dfa_trans M q bs))"
proof
  assume "dist_nodes M (Suc n) v p q"
  then obtain w where W: "length w = Suc n" and L: "list_all (is_alph v) w" and A: "dfa_accepting M (dfa_steps M p w) \<noteq> dfa_accepting M (dfa_steps M q w)" unfolding dist_nodes_def by blast
  then obtain b bs where B: "w = b # bs" by (cases w) auto
  from A have A2: "dfa_accepting M (dfa_steps M (dfa_trans M p b) bs) \<noteq> dfa_accepting M (dfa_steps M (dfa_trans M q b) bs)"
    unfolding B by simp 
  with W B L show "\<exists>bs. is_alph v bs \<and> dist_nodes M n v (dfa_trans M p bs) (dfa_trans M q bs)" by (auto simp: dist_nodes_def)
next
  assume "\<exists>bs. is_alph v bs \<and> dist_nodes M n v (dfa_trans M p bs) (dfa_trans M q bs)"
  then obtain b bs where W: "length bs = n" and V: "is_alph v b" and V': "list_all (is_alph v) bs"
    and A: "dfa_accepting M (dfa_steps M (dfa_trans M p b) bs) \<noteq> dfa_accepting M (dfa_steps M (dfa_trans M q b) bs)" 
    unfolding dist_nodes_def by blast
  hence "dfa_accepting M (dfa_steps M p (b # bs)) \<noteq> dfa_accepting M (dfa_steps M q (b # bs))" by simp 
  moreover from W have "length (b # bs) = Suc n" by simp
  moreover from V V' have "list_all (is_alph v) (b # bs)" by simp
  ultimately show "dist_nodes M (Suc n) v p q" unfolding dist_nodes_def by blast
qed

lemma bdd_lookup_append:
  assumes "bddh n B" and "length bs \<ge> n"
  shows "bdd_lookup B (bs @ w) = bdd_lookup B bs"
using assms
proof (induct B bs arbitrary: n rule: bdd_lookup.induct)
  case (2 l r b bs n)
  then obtain n' where N: "n = Suc n'" by (cases n) simp+
  with 2 show ?case by (cases b) auto
qed simp+

lemma bddh_exists: "\<exists>n. bddh n B"
proof (induct B)
  case (Branch l r)
  then obtain n m where L: "bddh n l" and R: "bddh m r" by blast
  with bddh_ge[of n "max n m" l] bddh_ge[of m "max n m" r] have "bddh (Suc (max n m)) (Branch l r)" by simp
  thus ?case by (rule exI)
qed simp

lemma check_eq_dist_nodes:
  assumes "\<forall>p q. dfa_is_node M q \<and> p < q \<longrightarrow> tr_lookup T q p = (\<exists>n < m. dist_nodes M n v p q)" and "m > 0"
  and "bdd_all (dfa_is_node M) l" and "bdd_all (dfa_is_node M) r"
  shows "(\<not> check_eq l r T) = (\<exists>bs. bddh (length bs) l \<and> bddh (length bs) r \<and> (\<exists>n < m. dist_nodes M n v (bdd_lookup l bs) (bdd_lookup r bs)))"
using assms proof (induct l r T rule: check_eq.induct)
  case (1 i j T)
  have "i < j \<or> i = j \<or> i > j" by auto
  thus ?case by (elim disjE) (insert 1, auto simp: dist_nodes_def tr_lookup_def)
next
  case (2 l r i T)
  hence IV1: "(\<not> check_eq l (Leaf i) T) = (\<exists>bs. bddh (length bs) l \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup l bs) (bdd_lookup (Leaf i) bs)))" by simp
  from 2 have IV2: "(\<not> check_eq r (Leaf i) T) = (\<exists>bs. bddh (length bs) r \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup r bs) (bdd_lookup (Leaf i) bs)))" by simp
  have "(\<not> check_eq (Branch l r) (Leaf i) T) = (\<not> check_eq l (Leaf i) T \<or> \<not> check_eq r (Leaf i) T)" by simp
  also have "\<dots> = (\<exists>bs. bddh (length bs) (Branch l r) \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m . dist_nodes M n v (bdd_lookup (Branch l r) bs) (bdd_lookup (Leaf i) bs)))" (is "(?L \<or> ?R) = ?E")
  proof
    assume "?L \<or> ?R"
    thus "?E" proof (elim disjE)
      assume "?L"
      then obtain bs where O: "bddh (length bs) l \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup l bs) (bdd_lookup (Leaf i) bs))" unfolding IV1 by blast
      from bddh_exists obtain k where B: "bddh k r" by blast
      with O have "bddh (length bs + k) r" and "bddh (length bs + k) l" and "bddh (length bs + k) (Leaf i)" by (simp add: bddh_ge[of k "length bs + k"] bddh_ge[of "length bs" "length bs + k"])+
      with O have "bddh (length (False # bs @ replicate k False)) (Branch l r) \<and> bddh (length (False # bs @ replicate k False)) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (Branch l r) (False # bs @ replicate k False)) (bdd_lookup (Leaf i) (False # bs @ replicate k False)))" by (auto simp: bdd_lookup_append)
      thus ?thesis by (rule exI)
    next
      assume "?R"
      then obtain bs where O: "bddh (length bs) r \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup r bs) (bdd_lookup (Leaf i) bs))" unfolding IV2 by blast
      from bddh_exists obtain k where B: "bddh k l" by blast
      with O have "bddh (length bs + k) l" and "bddh (length bs + k) r" and "bddh (length bs + k) (Leaf i)" by (simp add: bddh_ge[of k "length bs + k"] bddh_ge[of "length bs" "length bs + k"])+
      with O have "bddh (length (True # bs @ replicate k False)) (Branch l r) \<and> bddh (length (True # bs @ replicate k False)) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (Branch l r) (True # bs @ replicate k False)) (bdd_lookup (Leaf i) (True # bs @ replicate k False)))" by (auto simp: bdd_lookup_append)
      thus ?thesis by (rule exI)
    qed
  next
    assume "?E"
    then obtain bs where O: "bddh (length bs) (Branch l r) \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (Branch l r) bs) (bdd_lookup (Leaf i) bs))" by blast
    then obtain b br where B: "bs = b # br" by (cases bs) auto
    with O IV1 IV2 show "?L \<or> ?R" by (cases b) auto
  qed
  finally show ?case by simp 
next
  case (3 i l r T)
  hence IV1: "(\<not> check_eq (Leaf i) l T) = (\<exists>bs. bddh (length bs) l \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (Leaf i) bs) (bdd_lookup l bs)))" by simp
  from 3 have IV2: "(\<not> check_eq (Leaf i) r T) = (\<exists>bs. bddh (length bs) r \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (Leaf i) bs) (bdd_lookup r bs)))" by simp
  have "(\<not> check_eq (Leaf i) (Branch l r) T) = (\<not> check_eq (Leaf i) l T \<or> \<not> check_eq (Leaf i) r T)" by simp
  also have "\<dots> = (\<exists>bs. bddh (length bs) (Branch l r) \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m . dist_nodes M n v (bdd_lookup (Leaf i) bs) (bdd_lookup (Branch l r) bs)))" (is "(?L \<or> ?R) = ?E")
  proof
    assume "?L \<or> ?R"
    thus "?E" proof (elim disjE)
      assume "?L"
      then obtain bs where O: "bddh (length bs) l \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (Leaf i) bs) (bdd_lookup l bs))" unfolding IV1 by blast
      from bddh_exists obtain k where B: "bddh k r" by blast
      with O have "bddh (length bs + k) r" and "bddh (length bs + k) l" and "bddh (length bs + k) (Leaf i)" by (simp add: bddh_ge[of k "length bs + k"] bddh_ge[of "length bs" "length bs + k"])+
      with O have "bddh (length (False # bs @ replicate k False)) (Branch l r) \<and> bddh (length (False # bs @ replicate k False)) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (Leaf i) (False # bs @ replicate k False)) (bdd_lookup (Branch l r) (False # bs @ replicate k False)))" by (auto simp: bdd_lookup_append)
      thus ?thesis by (rule exI)
    next
      assume "?R"
      then obtain bs where O: "bddh (length bs) r \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (Leaf i) bs) (bdd_lookup r bs))" unfolding IV2 by blast
      from bddh_exists obtain k where B: "bddh k l" by blast
      with O have "bddh (length bs + k) l" and "bddh (length bs + k) r" and "bddh (length bs + k) (Leaf i)" by (simp add: bddh_ge[of k "length bs + k"] bddh_ge[of "length bs" "length bs + k"])+
      with O have "bddh (length (True # bs @ replicate k False)) (Branch l r) \<and> bddh (length (True # bs @ replicate k False)) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (Leaf i) (True # bs @ replicate k False)) (bdd_lookup (Branch l r) (True # bs @ replicate k False)))" by (auto simp: bdd_lookup_append)
      thus ?thesis by (rule exI)
    qed
  next
    assume "?E"
    then obtain bs where O: "bddh (length bs) (Branch l r) \<and> bddh (length bs) (Leaf i) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (Leaf i) bs) (bdd_lookup (Branch l r) bs))" by blast
    then obtain b br where B: "bs = b # br" by (cases bs) auto
    with O IV1 IV2 show "?L \<or> ?R" by (cases b) auto
  qed
  finally show ?case by simp 
next
  case (4 l1 r1 l2 r2 T)
  hence IV1: "(\<not> check_eq l1 l2 T) = (\<exists>bs. bddh (length bs) l1 \<and> bddh (length bs) l2 \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup l1 bs) (bdd_lookup l2 bs)))" by simp
  from 4 have IV2: "(\<not> check_eq r1 r2 T) = (\<exists>bs. bddh (length bs) r1 \<and> bddh (length bs) r2 \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup r1 bs) (bdd_lookup r2 bs)))" by simp
  have "(\<not> check_eq (Branch l1 r1) (Branch l2 r2) T) = (\<not> check_eq l1 l2 T \<or> \<not> check_eq r1 r2 T)" by simp
  also have "\<dots> = (\<exists>bs. bddh (length bs) (Branch l1 r1) \<and> bddh (length bs) (Branch l2 r2) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (Branch l1 r1) bs) (bdd_lookup (Branch l2 r2) bs)))"
    (is "(?L \<or> ?R) = (\<exists>bs. ?E bs)") proof
    assume "?L \<or> ?R"
    thus "\<exists>bs. ?E bs" proof (elim disjE)
      assume "?L"
      then obtain bs where O: "bddh (length bs) l1 \<and> bddh (length bs) l2 \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup l1 bs) (bdd_lookup l2 bs))" unfolding IV1 by blast
      from bddh_exists obtain k1 k2 where K1: "bddh k1 r1" and K2: "bddh k2 r2" by blast
      with O have "bddh (length bs + max k1 k2) l1" and "bddh (length bs + max k1 k2) l2" and "bddh (length bs + max k1 k2) r1" and "bddh (length bs + max k1 k2) r2"
        by (simp add: bddh_ge[of "length bs" "length bs + max k1 k2"] bddh_ge[of k1 "length bs + max k1 k2"] bddh_ge[of k2 "length bs + max k1 k2"])+
      with O have "bddh (length (False # bs @ replicate (max k1 k2) False)) (Branch l1 r1) \<and> bddh (length (False # bs @ replicate (max k1 k2) False)) (Branch l2 r2) \<and>
        (\<exists>n<m. dist_nodes M n v (bdd_lookup (Branch l1 r1) (False # bs @ replicate (max k1 k2) False)) (bdd_lookup (Branch l2 r2) (False # bs @ replicate (max k1 k2) False)))"
        by (auto simp: bdd_lookup_append)
      thus ?thesis by (rule exI)
    next
      assume "?R"
      then obtain bs where O: "bddh (length bs) r1 \<and> bddh (length bs) r2 \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup r1 bs) (bdd_lookup r2 bs))" unfolding IV2 by blast
      from bddh_exists obtain k1 k2 where K1: "bddh k1 l1" and K2: "bddh k2 l2" by blast
      with O have "bddh (length bs + max k1 k2) l1" and "bddh (length bs + max k1 k2) l2" and "bddh (length bs + max k1 k2) r1" and "bddh (length bs + max k1 k2) r2"
        by (simp add: bddh_ge[of "length bs" "length bs + max k1 k2"] bddh_ge[of k1 "length bs + max k1 k2"] bddh_ge[of k2 "length bs + max k1 k2"])+
      with O have "bddh (length (True # bs @ replicate (max k1 k2) False)) (Branch l1 r1) \<and> bddh (length (True # bs @ replicate (max k1 k2) False)) (Branch l2 r2) \<and>
        (\<exists>n<m. dist_nodes M n v (bdd_lookup (Branch l1 r1) (True # bs @ replicate (max k1 k2) False)) (bdd_lookup (Branch l2 r2) (True # bs @ replicate (max k1 k2) False)))"
        by (auto simp: bdd_lookup_append)
      thus ?thesis by (rule exI)
    qed
  next
    assume "\<exists>bs. ?E bs"
    then obtain bs where O: "?E bs" by blast
    then obtain b br where B: "bs = b # br" by (cases bs) auto
    with O IV1 IV2 show "?L \<or> ?R" by (cases b) auto
  qed
  finally show ?case by simp
qed

lemma iter_wf: "wf_tr M T \<Longrightarrow> wf_tr M (snd (iter M T))"
  by (simp add: wf_tr_def iter_def fold_map_idx_len fold_map_idx_nth split_beta)

lemma fixpt_wf: "wf_tr M T \<Longrightarrow> wf_tr M (fixpt M T)"
proof (induct M T rule: fixpt_induct)
  case (1 M T)
  show ?case proof (cases "fst (iter M T)")
    case True with 1 show ?thesis by (simp add: iter_wf)
  next
    case False with 1 show ?thesis by simp
  qed
qed

lemma list_split:
  assumes "n \<le> length bss"
  shows "\<exists>b bs. bss = b @ bs \<and> length b = n"
using assms proof (induct bss arbitrary: n)
  case (Cons a as)
  show ?case proof (cases n)
    case (Suc n')
    with Cons have "\<exists>b bs. as = b @ bs \<and> length b = n'" by simp
    then obtain b bs where B: "as = b @ bs \<and> length b = n'" by blast
    with Suc Cons have "a # as = (a # b) @ bs \<and> length (a # b) = n" by simp
    thus ?thesis by blast
  qed simp
qed simp

lemma iter_dist_nodes:
  assumes "wf_tr M T"
  and "wf_dfa M v"
  and "\<forall>p q. dfa_is_node M q \<and> p < q \<longrightarrow> tr_lookup T q p = (\<exists>n < m. dist_nodes M n v p q)" and "m > 0"
  and "dfa_is_node M q" and "p < q"
  shows "tr_lookup (snd (iter M T)) q p = (\<exists>n < Suc m. dist_nodes M n v p q)"
proof -
  from assms obtain m' where M': "m = Suc m'" by (cases m) simp+
  have C: "(\<not> check_eq (fst M ! q) (fst M ! p) T) = (\<exists>n<m. dist_nodes M (Suc n) v p q)" proof
    assume "\<not> check_eq (fst M ! q) (fst M ! p) T"
    with assms have "\<exists>bs. bddh (length bs) (fst M ! q) \<and> bddh (length bs) (fst M ! p) \<and> (\<exists>n < m. dist_nodes M n v (bdd_lookup (fst M ! q) bs) (bdd_lookup (fst M ! p) bs))"
      by (simp add: check_eq_dist_nodes wf_dfa_def list_all_iff dfa_is_node_def)
    then obtain bs n bss where X: "bddh (length bs) (fst M ! q) \<and> bddh (length bs) (fst M ! p) \<and> n < m \<and>
      length bss = n \<and> list_all (is_alph v) bss \<and> dfa_accepting M (dfa_steps M (bdd_lookup (fst M ! q) bs) bss) \<noteq> dfa_accepting M (dfa_steps M (bdd_lookup (fst M ! p) bs) bss)"
      unfolding dist_nodes_def by blast
    from list_split[of v "bs @ replicate v False"] have "\<exists>b' bs'. bs @ replicate v False = b' @ bs' \<and> length b' = v" by simp
    then obtain b' bs' where V: "bs @ replicate v False = b' @ bs' \<and> length b' = v" by blast
    with X bdd_lookup_append[of "length bs" "fst M ! q" "bs" "replicate v False"] bdd_lookup_append[of "length bs" "fst M ! p" "bs" "replicate v False"]
    have 1: "dfa_accepting M (dfa_steps M (bdd_lookup (fst M ! q) (bs @ replicate v False)) bss) \<noteq> dfa_accepting M (dfa_steps M (bdd_lookup (fst M ! p) (bs @ replicate v False)) bss)" by simp
    from assms have "bddh v (fst M ! q) \<and> bddh v (fst M ! p)" by (simp add: wf_dfa_def dfa_is_node_def list_all_iff)
    with 1 V have "dfa_accepting M (dfa_steps M (dfa_trans M q b') bss) \<noteq> dfa_accepting M (dfa_steps M (dfa_trans M p b') bss)" by (auto simp: bdd_lookup_append dfa_trans_def)
    with X V have "is_alph v b' \<and> dist_nodes M n v (dfa_trans M p b') (dfa_trans M q b')" by (auto simp: dist_nodes_def is_alph_def)
    hence "dist_nodes M (Suc n) v p q" by (auto simp: dist_nodes_suc)
    with X show "\<exists>n<m. dist_nodes M (Suc n) v p q" by auto
  next
    assume "\<exists>n<m. dist_nodes M (Suc n) v p q"
    hence "\<exists>bs. \<exists>n<m. is_alph v bs \<and> dist_nodes M n v (dfa_trans M p bs) (dfa_trans M q bs)" by (auto simp: dist_nodes_suc)
    then obtain bs where X: "\<exists>n<m. is_alph v bs \<and> dist_nodes M n v (dfa_trans M p bs) (dfa_trans M q bs)" by blast
    hence BS: "length bs = v" by (auto simp: is_alph_def)
    with assms have "bddh (length bs) (fst M ! p) \<and> bddh (length bs) (fst M ! q)" by (simp add: wf_dfa_def dfa_is_node_def list_all_iff)
    with X have "bddh (length bs) (fst M ! p) \<and> bddh (length bs) (fst M ! q) \<and> (\<exists>n<m. dist_nodes M n v (bdd_lookup (fst M ! q) bs) (bdd_lookup (fst M ! p) bs))" by (auto simp: dfa_trans_def dist_nodes_def)
    moreover from assms have "bdd_all (dfa_is_node M) (fst M ! p) \<and> bdd_all (dfa_is_node M) (fst M ! q)" by (simp add: wf_dfa_def dfa_is_node_def list_all_iff)
    moreover note assms(3,4)
    ultimately show "\<not> check_eq (fst M ! q) (fst M ! p) T" by (auto simp: check_eq_dist_nodes)
  qed

  from assms have "tr_lookup (snd (iter M T)) q p =
    (if tr_lookup T q p then True else \<not> check_eq (fst M ! q) (fst M ! p) T)"
    by (auto simp add: iter_def wf_tr_def split_beta fold_map_idx_nth tr_lookup_def dfa_is_node_def)
  also have "\<dots> = (tr_lookup T q p \<or> \<not> check_eq (fst M ! q) (fst M ! p) T)" by simp
  also from assms C have "\<dots> = ((\<exists>n<m. dist_nodes M n v p q) \<or> (\<exists>n<m. dist_nodes M (Suc n) v p q))" by simp
  also have "\<dots> = (\<exists>n < m. dist_nodes M n v p q \<or> dist_nodes M (Suc n) v p q)" by auto
  also have "\<dots> = (\<exists>n < Suc m. dist_nodes M n v p q)" proof
    assume "\<exists>n<m. dist_nodes M n v p q \<or> dist_nodes M (Suc n) v p q"
    then obtain n where D: "dist_nodes M n v p q \<or> dist_nodes M (Suc n) v p q" and N: "n < m" by blast
    moreover from N have "n < Suc m" by simp
    ultimately show "\<exists>n < Suc m. dist_nodes M n v p q" by (elim disjE) blast+
  next
    assume "\<exists>n < Suc m. dist_nodes M n v p q"
    then obtain n where N: "n < Suc m" and D: "dist_nodes M n v p q" by blast
    from N have "n < m \<or> n = m" by auto
    from this D M' show "\<exists>n<m. dist_nodes M n v p q \<or> dist_nodes M (Suc n) v p q" by auto
  qed
  finally show ?thesis by simp
qed

lemma fixpt_dist_nodes':
  assumes "wf_tr M T" and "wf_dfa M v"
  and "\<forall>p q. dfa_is_node M q \<and> p < q \<longrightarrow> tr_lookup T q p = (\<exists>n < m. dist_nodes M n v p q)" and "m > 0"
  and "dfa_is_node M q" and "p < q"
  shows "tr_lookup (fixpt M T) q p = (\<exists>n. dist_nodes M n v p q)"
using assms proof (induct M T arbitrary: m rule: fixpt_induct)
  case (1 M T m)
  let ?T = "snd (iter M T)"
  show ?case proof (cases "fst (iter M T)")
    case True
    { fix p' q' assume H: "dfa_is_node M q' \<and> p' < q'"
      with 1 have "tr_lookup ?T q' p' = (\<exists>n < Suc m. dist_nodes M n v p' q')" by (simp only: iter_dist_nodes)
    } hence 2: "\<forall>p q. dfa_is_node M q \<and> p < q \<longrightarrow> tr_lookup ?T q p = (\<exists>n < Suc m. dist_nodes M n v p q)" by simp moreover
    from 1 have "wf_tr M ?T" by (simp add: iter_wf) moreover
    note 1(3,6,7) 1(1)[of "Suc m"] True
    ultimately have "tr_lookup (fixpt M ?T) q p = (\<exists>n. dist_nodes M n v p q)" by simp
    with True show ?thesis by (simp add: Let_def split_beta)
  next
    case False
    then have F: "snd (iter M T) = T" by (simp add: iter_def fold_map_idx_fst_snd_eq split_beta)
    have C: "\<And>m'. \<forall>p q. dfa_is_node M q \<and> p < q \<longrightarrow> tr_lookup T q p = (\<exists>n < m' + m. dist_nodes M n v p q)"
    proof -
      fix m' show "\<forall>p q. dfa_is_node M q \<and> p < q \<longrightarrow> tr_lookup T q p = (\<exists>n < m' + m. dist_nodes M n v p q)"
      proof (induct m')
        case 0 with 1 show ?case by simp
      next
        case (Suc m')
        { fix p' q' assume H: "dfa_is_node M q'" and H2: "p' < q'"
          note 1(2,3) Suc
          moreover from Suc 1 have "0 < m' + m" by simp
          moreover note H H2
          ultimately have "tr_lookup (snd (iter M T)) q' p' = (\<exists>n < Suc (m' + m). dist_nodes M n v p' q')" by (rule iter_dist_nodes)
          with F have "tr_lookup T q' p' = (\<exists>n < Suc m' + m. dist_nodes M n v p' q')" by simp
        } thus ?case by simp
      qed
    qed
    {
      fix p' q' assume H: "dfa_is_node M q' \<and> p' < q'"
      have "tr_lookup T q' p' = (\<exists>n. dist_nodes M n v p' q')" proof
        assume "tr_lookup T q' p'"
        with H C[of 0] show "\<exists>n. dist_nodes M n v p' q'" by auto
      next
        assume H': "\<exists>n. dist_nodes M n v p' q'"
        then obtain n where "dist_nodes M n v p' q'" by blast
        moreover have "n < Suc n + m" by simp
        ultimately have "\<exists>n' < Suc n + m. dist_nodes M n' v p' q'" by blast
        with H C[of "Suc n"] show "tr_lookup T q' p'" by simp
      qed
    } hence "\<forall>p q. dfa_is_node M q \<and> p < q \<longrightarrow> tr_lookup T q p = (\<exists>n. dist_nodes M n v p q)" by simp
    with False \<open>dfa_is_node M q\<close> \<open>p < q\<close> show ?thesis by simp
  qed
qed

lemma fixpt_dist_nodes:
  assumes "wf_dfa M v"
  and "dfa_is_node M p" and "dfa_is_node M q"
  shows "tr_lookup (fixpt M (init_tr M)) p q = (\<exists>n. dist_nodes M n v p q)"
proof -
  { fix p q assume H1: "p < q" and H2: "dfa_is_node M q"
    from init_tr_wf have "wf_tr M (init_tr M)" by simp
    moreover note assms(1)
    moreover {
      fix p' q' assume "dfa_is_node M q'" and "p' < q'"
      hence "tr_lookup (init_tr M) q' p' = dist_nodes M 0 v p' q'" by (rule init_tr_dist_nodes)
      also have "\<dots> = (\<exists>n < 1. dist_nodes M n v p' q')" by auto
      finally have "tr_lookup (init_tr M) q' p' = (\<exists>n<1. dist_nodes M n v p' q')" by simp
    } hence "\<forall>p q. dfa_is_node M q \<and> p < q \<longrightarrow> tr_lookup (init_tr M) q p = (\<exists>n<1. dist_nodes M n v p q)" by simp
    moreover note H1 H2
    ultimately have "tr_lookup (fixpt M (init_tr M)) q p = (\<exists>n. dist_nodes M n v p q)" by (simp only: fixpt_dist_nodes'[of _ _ _ 1])
  }
  with assms(2,3) show ?thesis by (auto simp: tr_lookup_def dist_nodes_def)
qed

primrec mk_eqcl' :: "nat option list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool list list \<Rightarrow> nat option list"
where
  "mk_eqcl' [] i j l T = []"
| "mk_eqcl' (x#xs) i j l T = (if tr_lookup T j i \<or> x \<noteq> None then x else Some l) # mk_eqcl' xs i (Suc j) l T"

lemma mk_eqcl'_len: "length (mk_eqcl' xs i j l T) = length xs" by (induct xs arbitrary: j) simp+

function mk_eqcl  :: "nat option list \<Rightarrow> nat list \<Rightarrow> nat \<Rightarrow> bool list list \<Rightarrow> nat list \<times> nat list" where
  "mk_eqcl [] zs i T = ([], zs)" |
  "mk_eqcl (None # xs) zs i T = (let (xs',zs') = mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T in (length zs # xs', zs'))" |
  "mk_eqcl (Some l # xs) zs i T = (let (xs',zs') = mk_eqcl xs zs (Suc i) T in (l # xs', zs'))"
  by pat_completeness auto
termination by (lexicographic_order simp: mk_eqcl'_len)

lemma mk_eqcl'_bound:
  assumes "\<And>x k. \<lbrakk>x \<in> set xs; x = Some k\<rbrakk> \<Longrightarrow> k < l"
  and "x \<in> set (mk_eqcl' xs i j l T)" and "x = Some k"
  shows "k \<le> l"
using assms proof (induct xs arbitrary: j)
  case (Cons y xs j)
  hence "x = y \<or> x = Some l \<or> x \<in> set (mk_eqcl' xs i (Suc j) l T)" by (cases "tr_lookup T j i \<or> y \<noteq> None") auto
  thus ?case proof (elim disjE)
    assume "x = y"
    hence "x \<in> set (y # xs)" by simp
    with Cons(2)[of x k] Cons(4) show ?thesis by simp
  qed (insert Cons, auto)
qed simp

lemma mk_eqcl'_nth':
  assumes "\<And>x k. \<lbrakk>x \<in> set xs; x = Some k\<rbrakk> \<Longrightarrow> k < l"
  and "\<And>i'. \<lbrakk>i' < length xs; \<not> tr_lookup T (i' + j) i\<rbrakk> \<Longrightarrow> xs ! i' = None"
  and "i < j" and "j' < length xs"
  shows "(mk_eqcl' xs i j l T ! j' = Some l) = (\<not> tr_lookup T (j' + j) i)"
using assms proof (induct xs arbitrary: j j')
  case (Cons x xs j)
  have I1:"\<And>i'. \<lbrakk>i' < length xs; \<not> tr_lookup T (i' + Suc j) i\<rbrakk> \<Longrightarrow> xs ! i' = None" proof -
    fix i' assume H: "i' < length xs" "\<not> tr_lookup T (i' + Suc j) i"
    with Cons(3)[of "Suc i'"] show "xs ! i' = None" by simp
  qed
  have "j' = 0 \<or> j' > 0" by auto
  thus ?case proof (elim disjE)
    assume "j' > 0"
    then obtain j'' where J: "j' = Suc j''" by (cases j') simp+
    from Cons(1)[of "Suc j" j''] I1 Cons(2,4,5) J show ?thesis by simp
  next
    assume H: "j' = 0"
    with Cons(3)[of 0] have "\<not> tr_lookup T j i \<Longrightarrow> x = None" by simp
    with Cons H show ?thesis by auto
  qed
qed simp

lemma mk_eqcl'_nth:
  assumes "\<And>i' j' k. \<lbrakk>i' < length xs; j' < length xs; xs ! i' = Some k\<rbrakk> \<Longrightarrow> (xs ! j' = Some k) = (\<not> tr_lookup T (i' + jj) (j' + jj))"
  and "\<And>a b c. \<lbrakk>a \<le> length T; b \<le> length T; c \<le> length T; \<not> tr_lookup T a b; \<not> tr_lookup T b c\<rbrakk> \<Longrightarrow> \<not> tr_lookup T a c"
  and "length xs + jj = length T + 1"
  and "\<And>x k. \<lbrakk>x \<in> set xs; x = Some k\<rbrakk> \<Longrightarrow> k < l"
  and "\<And>i'. \<lbrakk>i' < length xs; \<not> tr_lookup T (i' + jj) ii\<rbrakk> \<Longrightarrow> xs ! i' = None"
  and "ii < jj"
  and "i < length xs" and "mk_eqcl' xs ii jj l T ! i = Some m"
  and "j < length xs"
  shows "(mk_eqcl' xs ii jj l T ! j = Some m) = (\<not> tr_lookup T (i + jj) (j + jj))"
using assms proof (induct xs arbitrary: jj i j)
  case Nil
  from Nil(7) have False by simp
  thus ?case by simp
next
  case (Cons y xs jj i j)
  show ?case proof (cases i)
    case 0
    show ?thesis proof (cases j)
      case 0
      with \<open>i=0\<close> Cons(9) show ?thesis by (simp add: tr_lookup_def)
    next
      case (Suc j')
      from 0 Cons(5,9) have 1: "y = Some m \<and> m < l \<or> (y = None \<and> \<not> tr_lookup T jj ii \<and> m = l)" by (cases y, cases "tr_lookup T jj ii", auto)
      thus ?thesis proof (elim disjE)
        assume H: "y = Some m \<and> m < l"
        from Suc have "(mk_eqcl' (y # xs) ii jj l T ! j = Some m) = (mk_eqcl' xs ii (Suc jj) l T ! j' = Some m)" by simp
        also from H have "\<dots> = (xs ! j' = Some m)" proof (induct xs arbitrary: jj j') 
          case (Cons a xs jj j') thus ?case by (cases j') simp+
        qed simp
        also from Suc have "\<dots> = ((y # xs) ! j = Some m)" by simp
        also from Cons(2)[of i j m] Cons(8,10) Suc 0 H have "\<dots> = (\<not> tr_lookup T (i + jj) (j + jj))" by simp
        finally show ?thesis by simp
      next
        assume H: "y = None \<and> \<not> tr_lookup T jj ii \<and> m = l"
        with Suc have "(mk_eqcl' (y # xs) ii jj l T ! j = Some m) = (mk_eqcl' xs ii (Suc jj) l T ! j' = Some l)" by simp
        also have "\<dots> = (\<not> tr_lookup T (j' + Suc jj) ii)" proof (rule mk_eqcl'_nth')
          from Cons(5) show "\<And>x k. \<lbrakk>x \<in> set xs; x = Some k\<rbrakk> \<Longrightarrow> k < l" by simp
          show "\<And>i'. \<lbrakk>i' < length xs; \<not> tr_lookup T (i' + Suc jj) ii\<rbrakk> \<Longrightarrow> xs ! i' = None" proof -
            fix i' assume "i' < length xs" "\<not> tr_lookup T (i' + Suc jj) ii"
            with Cons(6)[of "Suc i'"] show "xs ! i' = None" by simp
          qed
          from Cons(7) show "ii < Suc jj" by simp
          from Cons(10) Suc show "j' < length xs" by simp
        qed
        also from Suc H 0 have "\<dots> = (\<not> tr_lookup T (j + jj) ii \<and> \<not> tr_lookup T (i + jj) ii)" by (simp add: add.commute) 
        also have "\<dots> = (\<not> tr_lookup T (i + jj) (j + jj) \<and> \<not> tr_lookup T (i + jj) ii)" proof
          assume H': "\<not> tr_lookup T (j + jj) ii \<and> \<not> tr_lookup T (i + jj) ii"
          hence "\<not> tr_lookup T ii (j + jj)" by (auto simp: tr_lookup_def)
          with H' Cons(3)[of "i + jj" ii "j + jj"] Cons(4,7,8,10) show "\<not> tr_lookup T (i + jj) (j + jj) \<and> \<not> tr_lookup T (i + jj) ii" by simp
        next
          assume H': "\<not> tr_lookup T (i + jj) (j + jj) \<and> \<not> tr_lookup T (i + jj) ii"
          hence "\<not> tr_lookup T (j + jj) (i + jj)" by (auto simp: tr_lookup_def)
          with H' Cons(3)[of "j + jj" "i + jj" ii] Cons(4,7,8,10) show "\<not> tr_lookup T (j + jj) ii \<and> \<not> tr_lookup T (i + jj) ii" by simp
        qed
        also from 0 H have "\<dots> = (\<not> tr_lookup T (i + jj) (j + jj))" by simp
        finally show ?thesis by simp
      qed
    qed
  next
    case (Suc i')
    show ?thesis proof (cases j)
      case 0
      have "m \<le> l" proof (rule mk_eqcl'_bound)
        from Cons(5) show "\<And>x k. \<lbrakk>x \<in> set (y # xs); x = Some k\<rbrakk> \<Longrightarrow> k < l" by simp
        from Cons(8) have "i < length (mk_eqcl' (y # xs) ii jj l T)" by (simp add: mk_eqcl'_len)
        with Cons(9) have "\<exists>i < length (mk_eqcl' (y # xs) ii jj l T). mk_eqcl' (y # xs) ii jj l T ! i = Some m" by blast
        thus "Some m \<in> set (mk_eqcl' (y # xs) ii jj l T)" by (simp only: in_set_conv_nth)
        show "Some m = Some m" by simp
      qed
      hence "m < l \<or> m = l" by auto
      thus ?thesis proof (elim disjE)
        assume H: "m < l"
        with Cons(9) have I: "(y # xs) ! i = Some m" proof (induct ("y # xs") arbitrary: jj i)
          case (Cons a l jj i) thus ?case by (cases i) (auto, cases "tr_lookup T jj ii \<or> a \<noteq> None", simp+)
        qed simp
        from 0 H have "(mk_eqcl' (y # xs) ii jj l T ! j = Some m) = ((y#xs) ! j = Some m)" by (cases "tr_lookup T jj ii \<or> y \<noteq> None") simp+
        also from Cons(8,10) I have "\<dots> = (\<not> tr_lookup T (i + jj) (j + jj))" by (rule Cons(2))
        finally show ?thesis by simp
      next
        assume H: "m = l"
        from Cons(5,6,7,8) have "(mk_eqcl' (y # xs) ii jj l T ! i = Some l) = (\<not> tr_lookup T (i + jj) ii)" by (rule mk_eqcl'_nth')
        with H Cons(9) have I: "\<not> tr_lookup T (i + jj) ii" by simp

        with 0 H Cons(5) have "(mk_eqcl' (y # xs) ii jj l T ! j = Some m) = (\<not> tr_lookup T (j + jj) ii \<and> \<not> tr_lookup T (i + jj) ii \<and> y = None)" by auto
        also from Cons(6)[of 0] 0 have "\<dots> = (\<not> tr_lookup T (j + jj) ii \<and> \<not> tr_lookup T (i + jj) ii)" by auto
        also have "\<dots> = (\<not> tr_lookup T (i + jj) (j + jj) \<and> \<not> tr_lookup T (i + jj) ii)" proof
          assume H': "\<not> tr_lookup T (j + jj) ii \<and> \<not> tr_lookup T (i + jj) ii"
          hence "\<not> tr_lookup T ii (j + jj)" by (auto simp: tr_lookup_def)
          with H' Cons(3)[of "i + jj" ii "j + jj"] Cons(4,7,8,10) show "\<not> tr_lookup T (i + jj) (j + jj) \<and> \<not> tr_lookup T (i + jj) ii" by simp
        next
          assume H': "\<not> tr_lookup T (i + jj) (j + jj) \<and> \<not> tr_lookup T (i + jj) ii" 
          hence "\<not> tr_lookup T (j + jj) (i + jj)" by (auto simp: tr_lookup_def)
          with H' Cons(3)[of "j + jj" "i + jj" ii] Cons(4,7,8,10) show "\<not> tr_lookup T (j + jj) ii \<and> \<not> tr_lookup T (i + jj) ii" by simp
        qed
        also from I have "\<dots> = (\<not> tr_lookup T (i + jj) (j + jj))" by simp
        finally show ?thesis by simp
      qed
    next
      case (Suc j')
      hence "(mk_eqcl' (y # xs) ii jj l T ! j = Some m) = (mk_eqcl' xs ii (Suc jj) l T ! j' = Some m)" by simp
      also have "\<dots> = (\<not> tr_lookup T (i' + Suc jj) (j' + Suc jj))" proof (rule Cons(1))
        show "\<And>i' j' k. \<lbrakk>i' < length xs; j' < length xs; xs ! i' = Some k\<rbrakk> \<Longrightarrow> (xs ! j' = Some k) = (\<not> tr_lookup T (i' + Suc jj) (j' + Suc jj))" proof -
          fix i' j' k assume "i' < length xs" "j' < length xs" "xs ! i' = Some k"
          with Cons(2)[of "Suc i'" "Suc j'" k] show "(xs ! j' = Some k) = (\<not> tr_lookup T (i' + Suc jj) (j' + Suc jj))" by simp
        qed
        from Cons(3) show "\<And>a b c. \<lbrakk>a \<le> length T; b \<le> length T; c \<le> length T; \<not> tr_lookup T a b; \<not> tr_lookup T b c \<rbrakk> \<Longrightarrow> \<not> tr_lookup T a c" by blast
        from Cons(4) show "length xs + Suc jj = length T + 1" by simp
        from Cons(5) show "\<And>x k. \<lbrakk>x \<in> set xs; x = Some k\<rbrakk> \<Longrightarrow> k < l" by simp
        show "\<And>i'. \<lbrakk>i' < length xs; \<not> tr_lookup T (i' + Suc jj) ii\<rbrakk> \<Longrightarrow> xs ! i' = None" proof -
          fix i' assume "i' < length xs" "\<not> tr_lookup T (i' + Suc jj) ii"
          with Cons(6)[of "Suc i'"] show "xs ! i' = None" by simp
        qed
        from Cons(7) show "ii < Suc jj" by simp
        from Cons(8) \<open>i=Suc i'\<close> show "i' < length xs" by simp
        from Cons(9) \<open>i=Suc i'\<close> show "mk_eqcl' xs ii (Suc jj) l T ! i' = Some m" by simp
        from Cons(10) Suc show "j' < length xs" by simp
      qed
      also from Suc \<open>i=Suc i'\<close> have "\<dots> = (\<not> tr_lookup T (i + jj) (j + jj))" by simp
      finally show ?thesis by simp
    qed
  qed
qed

lemma mk_eqcl'_Some:
  assumes "i < length xs" and "xs ! i \<noteq> None"
  shows "mk_eqcl' xs ii j l T ! i = xs ! i"
using assms proof (induct xs arbitrary: j i) 
  case (Cons y xs j i)
  thus ?case by (cases i) auto
qed simp

lemma mk_eqcl'_Some2:
  assumes "i < length xs"
  and "k < l"
  shows "(mk_eqcl' xs ii j l T ! i = Some k) = (xs ! i = Some k)"
using assms proof (induct xs arbitrary: j i)
  case (Cons y xs j i)
  thus ?case by (cases i) auto
qed simp
  
lemma mk_eqcl_fst_Some:
  assumes "i < length xs" and "k < length zs"
  shows "(fst (mk_eqcl xs zs ii T) ! i = k) = (xs ! i = Some k)"
using assms proof (induct xs zs ii T arbitrary: i rule: mk_eqcl.induct)
  case (2 xs zs ii T i)
  thus ?case by (cases i) (simp add: split_beta mk_eqcl'_len mk_eqcl'_Some2)+
next
  case (3 l xs zs ii T i)
  thus ?case by (cases i) (simp add: split_beta)+
qed simp

lemma mk_eqcl_len_snd:
  "length zs \<le> length (snd (mk_eqcl xs zs i T))"
  by (induct xs zs i T rule: mk_eqcl.induct) (simp add: split_beta)+

lemma mk_eqcl_len_fst:
  "length (fst (mk_eqcl xs zs i T)) = length xs"
  by (induct xs zs i T rule: mk_eqcl.induct) (simp add: split_beta mk_eqcl'_len)+

lemma mk_eqcl_set_snd:
  assumes "i \<notin> set zs"
  and "j > i"
  shows "i \<notin> set (snd (mk_eqcl xs zs j T))"
using assms by (induct xs zs j T rule: mk_eqcl.induct) (auto simp: split_beta)

lemma mk_eqcl_snd_mon:
  assumes "\<And>j1 j2. \<lbrakk>j1 < j2; j2 < length zs\<rbrakk> \<Longrightarrow> zs ! j1 < zs ! j2"
  and "\<And>x. x \<in> set zs \<Longrightarrow> x < i"
  and "j1 < j2" and "j2 < length (snd (mk_eqcl xs zs i T))"
  shows "snd (mk_eqcl xs zs i T) ! j1 < snd (mk_eqcl xs zs i T) ! j2"
using assms proof (induct xs zs i T rule: mk_eqcl.induct)
  case (2 xs zs i T)
  have "\<And>j1 j2. \<lbrakk>j1 < j2; j2 < length (zs @ [i])\<rbrakk> \<Longrightarrow> (zs @ [i]) ! j1 < (zs @ [i]) ! j2" proof -
    fix j1 j2 assume H: "j1 < j2" "j2 < length (zs @ [i])"
    hence "j2 < length zs \<or> j2 = length zs" by auto
    from this H 2 show "(zs @ [i]) ! j1 < (zs @ [i]) ! j2" by (elim disjE) (simp add: nth_append)+ 
  qed moreover
  have "\<And>x. x \<in> set (zs @ [i]) \<Longrightarrow> x < Suc i" proof -
    fix x assume "x \<in> set (zs @ [i])"
    hence "x \<in> set zs \<or> x = i" by auto
    with 2(3)[of x] show "x < Suc i" by auto
  qed moreover
  note 2(4) moreover
  from 2(5) have "j2 < length (snd (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T))" by (simp add: split_beta)
  ultimately have "snd (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T) ! j1 < snd (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T) ! j2" by (rule 2(1))
  thus ?case by (simp add: split_beta)
next
  case (3 l xs zs i T)
  note 3(2) moreover
  have "\<And>x. x \<in> set zs \<Longrightarrow> x < Suc i" proof -
    fix x assume "x \<in> set zs"
    with 3(3)[of x] show "x < Suc i" by simp
  qed moreover
  note 3(4) moreover
  from 3(5) have "j2 < length (snd (mk_eqcl xs zs (Suc i) T))" by (simp add: split_beta)
  ultimately have "snd (mk_eqcl xs zs (Suc i) T) ! j1 < snd (mk_eqcl xs zs (Suc i) T) ! j2" by (rule 3(1))
  thus ?case by (simp add: split_beta)
qed simp

lemma mk_eqcl_snd_nth:
  assumes "i < length zs"
  shows "snd (mk_eqcl xs zs j T) ! i = zs ! i"
using assms by (induct xs zs j T rule: mk_eqcl.induct) (simp add: split_beta nth_append)+

lemma mk_eqcl_bound:
  assumes "\<And>x k. \<lbrakk>x \<in> set xs; x = Some k\<rbrakk> \<Longrightarrow> k < length zs"
  and "x \<in> set (fst (mk_eqcl xs zs ii T))"
  shows "x < length (snd (mk_eqcl xs zs ii T))"
using assms proof (induct xs zs ii T rule: mk_eqcl.induct)
  case (2 xs zs i T)
  hence "x = length zs \<or> x \<in> set (fst (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T))" by (auto simp: split_beta)
  thus ?case proof (elim disjE)
    assume "x = length zs"
    hence "x < length (zs @ [i])" by simp
    also have "\<dots> \<le> length (snd (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T))" by (simp only: mk_eqcl_len_snd)
    finally show ?thesis by (simp add: split_beta)
  next
    assume H: "x \<in> set (fst (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T))" 
    have "\<And>x k. \<lbrakk>x \<in> set (mk_eqcl' xs i (Suc i) (length zs) T); x = Some k\<rbrakk> \<Longrightarrow> k < length (zs @ [i])" proof -
      fix x k assume H': "x \<in> set (mk_eqcl' xs i (Suc i) (length zs) T)" " x = Some k"
      { fix x' k' assume "x' \<in> set xs" "x' = Some k'"
        with 2 have "k' < length zs" by simp
      } from this H' have "k \<le> length zs" by (rule mk_eqcl'_bound)
      thus "k < length (zs @ [i])" by simp
    qed
    with H 2 show ?thesis by (simp add: split_beta)
  qed
next
  case (3 l xs zs i T)
  hence "x = l \<or> x \<in> set (fst (mk_eqcl xs zs (Suc i) T))" by (auto simp: split_beta)
  thus ?case proof (elim disjE)
    assume "x = l"
    with 3 have "x < length zs" by simp
    also from 3 have "\<dots> \<le> length (snd (mk_eqcl (Some l # xs) zs i T))" by (simp only: mk_eqcl_len_snd)
    finally show ?thesis by simp
  next
    assume "x \<in> set (fst (mk_eqcl xs zs (Suc i) T))"
    with 3 have "x < length (snd (mk_eqcl xs zs (Suc i) T))" by simp
    thus ?thesis by (simp add: split_beta)
  qed
qed simp

lemma mk_eqcl_fst_snd:
  assumes "\<And>i. i < length zs \<Longrightarrow> zs ! i < length xs + ii \<and> (zs ! i \<ge> ii \<longrightarrow> xs ! (zs ! i - ii) = Some i)"
  and "\<And>j1 j2. \<lbrakk>j1 < j2; j2 < length zs\<rbrakk> \<Longrightarrow> zs ! j1 < zs ! j2"
  and "\<And>z. z \<in> set zs \<Longrightarrow> z < ii"
  and "i < length (snd (mk_eqcl xs zs ii T))"
  and "length xs + ii \<le> length T + 1"
  shows "snd (mk_eqcl xs zs ii T) ! i < length (fst (mk_eqcl xs zs ii T)) + ii \<and> (snd (mk_eqcl xs zs ii T) ! i \<ge> ii \<longrightarrow>  fst (mk_eqcl xs zs ii T) ! (snd (mk_eqcl xs zs ii T) ! i - ii) = i)"
using assms proof (induct xs zs ii T arbitrary: i rule: mk_eqcl.induct)
  case (1 zs ii T i)
  from 1(1)[of i] 1(4,5) show ?case by simp
next
  case (2 xs zs i T j)
  have "\<And>i'. i' < length (zs @ [i]) \<Longrightarrow> (zs @ [i]) ! i' < length (mk_eqcl' xs i (Suc i) (length zs) T) + Suc i \<and>
    (Suc i \<le> (zs @ [i]) ! i' \<longrightarrow> mk_eqcl' xs i (Suc i) (length zs) T ! ((zs @ [i]) ! i' - Suc i) = Some i')" proof -
    fix i' assume "i' < length (zs @ [i])"
    hence "i' < length zs \<or> i' = length zs" by auto
    thus "(zs @ [i]) ! i' < length (mk_eqcl' xs i (Suc i) (length zs) T) + Suc i \<and> (Suc i \<le> (zs @ [i]) ! i' \<longrightarrow> mk_eqcl' xs i (Suc i) (length zs) T ! ((zs @ [i]) ! i' - Suc i) = Some i')"
    proof (elim disjE)
      assume H: "i' < length zs"
      with 2(2) have I: "zs ! i' < length (None # xs) + i \<and> (i \<le> zs ! i' \<longrightarrow> (None # xs) ! (zs ! i' - i) = Some i')" by simp
      with H have G1: "(zs @ [i]) ! i' < length (mk_eqcl' xs i (Suc i) (length zs) T) + Suc i" by (auto simp: mk_eqcl'_len nth_append)
      { assume H': "Suc i \<le> (zs @ [i]) ! i'"
        then obtain k where K: "(zs @ [i]) ! i' - i = Suc k" by (cases "(zs @ [i]) ! i' - i") simp+
        hence K': "k = (zs @ [i]) ! i' - Suc i" by simp
        from K H' H I have "xs ! k = Some i'" by (simp add: nth_append)
        with K I H have "mk_eqcl' xs i (Suc i) (length zs) T ! k = Some i'" by (auto simp add: mk_eqcl'_Some nth_append)
        with K' have "mk_eqcl' xs i (Suc i) (length zs) T ! ((zs @ [i]) ! i' - Suc i) = Some i'" by simp
      } with G1 show ?thesis by simp
    qed simp
  qed
  moreover have "\<And>j1 j2. \<lbrakk>j1 < j2; j2 < length (zs @ [i])\<rbrakk> \<Longrightarrow> (zs @ [i]) ! j1 < (zs @ [i]) ! j2" proof -
    fix j1 j2 assume H: "j1 < j2" "j2 < length (zs @ [i])"
    hence "j2 < length zs \<or> j2 = length zs" by auto
    from this H 2(3)[of j1 j2] 2(4)[of "zs ! j1"] show "(zs @ [i]) ! j1 < (zs @ [i]) ! j2" by (elim disjE) (simp add: nth_append)+
  qed
  moreover have "\<And>z. z \<in> set (zs @ [i]) \<Longrightarrow> z < Suc i" proof -
    fix z assume "z \<in> set (zs @ [i])"
    hence "z \<in> set zs \<or> z = i" by auto
    with 2(4)[of z] show "z < Suc i" by auto
  qed
  moreover from 2 have "j < length (snd (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T))" by (simp add: split_beta)
  moreover from 2 have "length (mk_eqcl' xs i (Suc i) (length zs) T) + Suc i \<le> length T + 1" by (simp add: mk_eqcl'_len)
  ultimately have IV: "snd (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T) ! j < length (fst (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T)) + Suc i \<and>
   (Suc i \<le> snd (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T) ! j \<longrightarrow>
    fst (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T) ! (snd (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T) ! j - Suc i) = j)" by (rule 2(1))
  hence G1: "snd (mk_eqcl (None # xs) zs i T) ! j < length (fst (mk_eqcl (None # xs) zs i T)) + i" by (auto simp: split_beta)
  { assume "i \<le> snd (mk_eqcl (None # xs) zs i T) ! j"
    hence "i = snd (mk_eqcl (None # xs) zs i T) ! j \<or> Suc i \<le> snd (mk_eqcl (None # xs) zs i T) ! j" by auto
    hence "fst (mk_eqcl (None # xs) zs i T) ! (snd (mk_eqcl (None # xs) zs i T) ! j - i) = j" proof (elim disjE)
      assume H: "i = snd (mk_eqcl (None # xs) zs i T) ! j"
      define k where "k = length zs"
      hence K: "snd (mk_eqcl (None # xs) zs i T) ! k = i" by (simp add: mk_eqcl_snd_nth split_beta)
      { assume "j \<noteq> k"
        hence "j < k \<or> j > k" by auto
        hence "snd (mk_eqcl (None # xs) zs i T) ! j \<noteq> i" proof (elim disjE)
          assume H': "j < k"
          from k_def have "k < length (zs @ [i])" by simp
          also have "\<dots> \<le> length (snd (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T))" by (simp only: mk_eqcl_len_snd)
          also have "\<dots> = length (snd (mk_eqcl (None # xs) zs i T))" by (simp add: split_beta)
          finally have K': "k < length (snd (mk_eqcl (None # xs) zs i T))" by simp
          from 2(3,4) H' this have "snd (mk_eqcl (None # xs) zs i T) ! j < snd (mk_eqcl (None # xs) zs i T) ! k" by (rule mk_eqcl_snd_mon)
          with K show ?thesis by simp
        next
          assume H': "j > k"
          from 2(3,4) H' 2(5) have "snd (mk_eqcl (None # xs) zs i T) ! k < snd (mk_eqcl (None # xs) zs i T) ! j" by (rule mk_eqcl_snd_mon)
          with K show ?thesis by simp
        qed
      }
      with H k_def have "j = length zs" by auto
      with H show ?thesis by (simp add: split_beta)
    next
      assume H: "Suc i \<le> snd (mk_eqcl (None # xs) zs i T) ! j"
      then obtain k where K: "snd (mk_eqcl (None # xs) zs i T) ! j - i = Suc k" by (cases "snd (mk_eqcl (None # xs) zs i T) ! j - i") simp+
      hence K': "k = snd (mk_eqcl (None # xs) zs i T) ! j - Suc i" by simp
      from H IV have "fst (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T) ! (snd (mk_eqcl (mk_eqcl' xs i (Suc i) (length zs) T) (zs @ [i]) (Suc i) T) ! j - Suc i) = j"
        by (auto simp: split_beta)
      with K' have "fst (mk_eqcl (None # xs) zs i T) ! Suc k = j" by (simp add: split_beta)
      with K show ?thesis by simp
    qed
  } with G1 show ?case by simp
next
  case (3 l xs zs i T j)
  have 1: "snd (mk_eqcl (Some l # xs) zs i T) = snd (mk_eqcl xs zs (Suc i) T)" by (simp add: split_beta)
  have 2: "length (fst (mk_eqcl (Some l # xs) zs i T)) = length (Some l # xs)" by (simp add: split_beta mk_eqcl_len_fst)
  have "\<And>j. j < length zs \<Longrightarrow> zs ! j < length xs + Suc i \<and> (Suc i \<le> zs ! j \<longrightarrow> xs ! (zs ! j - Suc i) = Some j)" proof -
    fix j assume H: "j < length zs"
    with 3(2)[of j] have I: "zs ! j < length (Some l # xs) + i \<and> (i \<le> zs ! j \<longrightarrow> (Some l # xs) ! (zs ! j - i) = Some j)" by simp
    hence G1: "zs ! j < length xs + Suc i" and G2: "i \<le> zs ! j \<longrightarrow> (Some l # xs) ! (zs ! j - i) = Some j" by simp+
    { assume H2: "Suc i \<le> zs ! j"
      then obtain k where K: "zs ! j - i = Suc k" by (cases "zs ! j - i") simp+
      with H2 G2 have "xs ! k = Some j" by simp
      moreover from K have "k = zs ! j - Suc i" by simp
      ultimately have "xs ! (zs ! j - Suc i) = Some j" by simp
    }
    with G1 show "zs ! j < length xs + Suc i \<and> (Suc i \<le> zs ! j \<longrightarrow> xs ! (zs ! j - Suc i) = Some j)" by simp
  qed
  moreover note 3(3)
  moreover have "\<And>z. z \<in> set zs \<Longrightarrow> z < Suc i" proof -
    fix z assume "z \<in> set zs"
    with 3(4)[of z] show "z < Suc i" by simp
  qed
  moreover from 3(5) 1 have "j < length (snd (mk_eqcl xs zs (Suc i) T))" by simp
  moreover from 3 have "length xs + Suc i \<le> length T + 1" by simp
  ultimately have IV: "snd (mk_eqcl xs zs (Suc i) T) ! j < length (fst (mk_eqcl xs zs (Suc i) T)) + Suc i \<and>
    (Suc i \<le> snd (mk_eqcl xs zs (Suc i) T) ! j \<longrightarrow> fst (mk_eqcl xs zs (Suc i) T) ! (snd (mk_eqcl xs zs (Suc i) T) ! j - Suc i) = j)" by (rule 3(1))
  with 1 have G1: "snd (mk_eqcl (Some l # xs) zs i T) ! j < length (fst (mk_eqcl (Some l # xs) zs i T)) + i" by (simp add: split_beta mk_eqcl_len_fst)
  { assume "i \<le> snd (mk_eqcl (Some l # xs) zs i T) ! j"
    hence "i = snd (mk_eqcl (Some l # xs) zs i T) ! j \<or> i < snd (mk_eqcl (Some l # xs) zs i T) ! j" by auto
    hence "fst (mk_eqcl (Some l # xs) zs i T) ! (snd (mk_eqcl (Some l # xs) zs i T) ! j - i) = j" proof (elim disjE)
      assume H: "i = snd (mk_eqcl (Some l # xs) zs i T) ! j"
      with 3 1 have "\<exists>j < length (snd (mk_eqcl xs zs (Suc i) T)). snd (mk_eqcl xs zs (Suc i) T) ! j = i" by auto
      hence T1: "i \<in> set (snd (mk_eqcl xs zs (Suc i) T))" by (simp only: in_set_conv_nth)
      from 3(4) have "i \<notin> set zs" by auto
      hence "i \<notin> set (snd (mk_eqcl xs zs (Suc i) T))" by (simp add: mk_eqcl_set_snd)
      with T1 show ?thesis by simp
    next
      assume H: "i < snd (mk_eqcl (Some l # xs) zs i T) ! j"
      from H obtain k where K: "snd (mk_eqcl (Some l # xs) zs i T) ! j - i = Suc k" by (cases "snd (mk_eqcl (Some l # xs) zs i T) ! j - i") simp+
      hence K': "snd (mk_eqcl (Some l # xs) zs i T) ! j - Suc i = k" by simp
      from 1 H IV have "fst (mk_eqcl xs zs (Suc i) T) ! (snd (mk_eqcl xs zs (Suc i) T) ! j - Suc i) = j" by simp
      with K K' show ?thesis by (simp add: split_beta)
    qed
  } with G1 show ?case by simp
qed

lemma mk_eqcl_fst_nth:
  assumes "\<And>i j k. \<lbrakk>i < length xs; j < length xs; xs ! i = Some k\<rbrakk> \<Longrightarrow> (xs ! j = Some k) = (\<not> tr_lookup T (i + ii) (j + ii))"
  and "\<And>a b c. \<lbrakk>a \<le> length T; b \<le> length T; c \<le> length T; \<not> tr_lookup T a b; \<not> tr_lookup T b c\<rbrakk> \<Longrightarrow> \<not> tr_lookup T a c"
  and "\<And>x k. \<lbrakk>x \<in> set xs; x = Some k\<rbrakk> \<Longrightarrow> k < length zs"
  and "length xs + ii = length T + 1"
  and "i < length xs" and "j < length xs"
  shows "(fst (mk_eqcl xs zs ii T) ! i = fst (mk_eqcl xs zs ii T) ! j) = (\<not> tr_lookup T (i + ii) (j + ii))"
using assms proof (induct xs zs ii T arbitrary: i j rule: mk_eqcl.induct)
  case (1 zs ii T) thus ?case by simp
next
  case (2 xs zs ii T)
  { fix i j assume H: "i < j" "j < length (None # xs)"
    then obtain j' where J: "j = Suc j'" by (cases j) simp+
    have "(fst (mk_eqcl (None # xs) zs ii T) ! i = fst (mk_eqcl (None # xs) zs ii T) ! j) = (\<not> tr_lookup T (i + ii) (j + ii))" proof (cases i)
      case 0
      with J have "(fst (mk_eqcl (None # xs) zs ii T) ! i = fst (mk_eqcl (None # xs) zs ii T) ! j) = (fst (mk_eqcl (mk_eqcl' xs ii (Suc ii) (length zs) T) (zs @ [ii]) (Suc ii) T) ! j' = length zs)"
        by (auto simp add: split_beta)
      also from H J have "\<dots> = (mk_eqcl' xs ii (Suc ii) (length zs) T ! j' = Some (length zs))" by (simp add: mk_eqcl_fst_Some mk_eqcl'_len)
      also have "\<dots> = (\<not> tr_lookup T (j' + Suc ii) ii)" proof -
        have "\<And>x k. \<lbrakk>x \<in> set xs; x = Some k\<rbrakk> \<Longrightarrow> k < length zs" proof -
          fix x k assume "x \<in> set xs" "x = Some k"
          with 2(4)[of x k] show "k < length zs" by simp
        qed moreover
        have "\<And>i'. \<lbrakk>i' < length xs; \<not> tr_lookup T (i' + Suc ii) ii\<rbrakk> \<Longrightarrow> xs ! i' = None" proof -
          fix i' assume H: "i' < length xs" "\<not> tr_lookup T (i' + Suc ii) ii"
          { assume H': "xs ! i' \<noteq> None"
            then obtain k where "xs ! i' = Some k" by (cases "xs ! i'") simp+
            with 2(2)[of "Suc i'" 0 k] H have False by simp
          } thus "xs ! i' = None" by (cases "xs ! i'") simp+
        qed moreover
        from H J have "ii < Suc ii" "j' < length xs" by simp+
        ultimately show ?thesis by (rule mk_eqcl'_nth')
      qed
      also from J 0 have "\<dots> = (\<not> tr_lookup T (i + ii) (j + ii))" by (auto simp: tr_lookup_def)
      finally show ?thesis by simp
    next
      case (Suc i')
      have "\<And>i j k. \<lbrakk>i < length (mk_eqcl' xs ii (Suc ii) (length zs) T); j < length (mk_eqcl' xs ii (Suc ii) (length zs) T); mk_eqcl' xs ii (Suc ii) (length zs) T ! i = Some k\<rbrakk>
         \<Longrightarrow> (mk_eqcl' xs ii (Suc ii) (length zs) T ! j = Some k) = (\<not> tr_lookup T (i + Suc ii) (j + Suc ii))" proof -
        fix i j k assume H: "i < length (mk_eqcl' xs ii (Suc ii) (length zs) T)" "j < length (mk_eqcl' xs ii (Suc ii) (length zs) T)" "mk_eqcl' xs ii (Suc ii) (length zs) T ! i = Some k"
        { fix i' j' k assume "i' < length xs" "j' < length xs" "xs ! i' = Some k"
          with 2(2)[of "Suc i'" "Suc j'" k] have "(xs ! j' = Some k) = (\<not> tr_lookup T (i' + Suc ii) (j' + Suc ii))" by simp
        } moreover
        note 2(3) moreover
        from 2(5) have "length xs + Suc ii = length T + 1" by simp moreover
        { fix x k assume "x \<in> set xs" "x = Some k"
          with 2(4)[of x k] have "k < length zs" by simp
        } moreover
        have "\<And>i'. \<lbrakk>i' < length xs; \<not> tr_lookup T (i' + Suc ii) ii\<rbrakk> \<Longrightarrow> xs ! i' = None" proof -
          fix i' assume H': "i' < length xs" "\<not> tr_lookup T (i' + Suc ii) ii"
          { assume "xs ! i' \<noteq> None"
            then obtain k where K: "xs ! i' = Some k" by (cases "xs ! i'") simp+
            with H' 2(2)[of "Suc i'" 0 k] have False by simp 
          } thus "xs ! i' = None" by (cases "xs ! i' = None") simp+
        qed moreover
        have "ii < Suc ii" by simp moreover
        from H have "i < length xs" by (simp add: mk_eqcl'_len) moreover
        note H(3) moreover
        from H have "j < length xs" by (simp add: mk_eqcl'_len)
        ultimately show "(mk_eqcl' xs ii (Suc ii) (length zs) T ! j = Some k) = (\<not> tr_lookup T (i + Suc ii) (j + Suc ii))" by (rule mk_eqcl'_nth)
      qed moreover
      note 2(3) moreover
      have "\<And>x k. \<lbrakk>x \<in> set (mk_eqcl' xs ii (Suc ii) (length zs) T); x = Some k\<rbrakk> \<Longrightarrow> k < length (zs @ [ii])" proof -
        fix x k assume H: "x \<in> set (mk_eqcl' xs ii (Suc ii) (length zs) T)" "x = Some k"
        { fix x k assume "x \<in> set xs" "x = Some k"
          with 2(4)[of x k] have "k < length zs" by simp
        } from this H have "k \<le> length zs" by (rule mk_eqcl'_bound)
        thus "k < length (zs @ [ii])" by simp
      qed moreover
      from 2(5) have "length (mk_eqcl' xs ii (Suc ii) (length zs) T) + Suc ii = length T + 1" by (simp add: mk_eqcl'_len) moreover
      from H Suc J have "i' < length (mk_eqcl' xs ii (Suc ii) (length zs) T)" "j' < length (mk_eqcl' xs ii (Suc ii) (length zs) T)" by (simp add: mk_eqcl'_len)+
      ultimately have IV: "(fst (mk_eqcl (mk_eqcl' xs ii (Suc ii) (length zs) T) (zs @ [ii]) (Suc ii) T) ! i' = fst (mk_eqcl (mk_eqcl' xs ii (Suc ii) (length zs) T) (zs @ [ii]) (Suc ii) T) ! j') =
        (\<not> tr_lookup T (i' + Suc ii) (j' + Suc ii))" by (rule 2(1))
      with Suc J show ?thesis by (simp add: split_beta)
    qed
  } note L = this
  have "i < j \<or> i = j \<or> i > j" by auto
  thus ?case proof (elim disjE)
    assume "i > j"
    with 2(6) L have "(fst (mk_eqcl (None # xs) zs ii T) ! j = fst (mk_eqcl (None # xs) zs ii T) ! i) = (\<not> tr_lookup T (i + ii) (j + ii))" by (auto simp: tr_lookup_def)
    thus ?thesis by auto
  qed (insert 2(7) L, simp add: tr_lookup_def)+
next
  case (3 l xs zs ii T i j)
  { fix i j assume H: "i < j" "j < length (Some l # xs)"
    then obtain j' where J: "j = Suc j'" by (cases j) simp+
    have "(fst (mk_eqcl (Some l # xs) zs ii T) ! i = fst (mk_eqcl (Some l # xs) zs ii T) ! j) = (\<not> tr_lookup T (i + ii) (j + ii))" proof (cases i)
      case 0
      with J have "(fst (mk_eqcl (Some l # xs) zs ii T) ! i = fst (mk_eqcl (Some l # xs) zs ii T) ! j) = (fst (mk_eqcl xs zs (Suc ii) T) ! j' = l)" by (auto simp add: split_beta)
      also from 3(4)[of "Some l" l] H J have "\<dots> = (xs ! j' = Some l)" by (simp add: mk_eqcl_fst_Some)
      also from J have "\<dots> = ((Some l # xs) ! j = Some l)" by simp
      also from H 0 3(2)[of i j l] have "\<dots> = (\<not> tr_lookup T (i + ii) (j + ii))" by simp
      finally show ?thesis by simp
    next
      case (Suc i')
      have "\<And>i j k. \<lbrakk>i < length xs; j < length xs; xs ! i = Some k\<rbrakk> \<Longrightarrow> (xs ! j = Some k) = (\<not> tr_lookup T (i + Suc ii) (j + Suc ii))" proof -
        fix i j k assume "i < length xs" "j < length xs" "xs ! i = Some k"
        with 3(2)[of "Suc i" "Suc j" k] show "(xs ! j = Some k) = (\<not> tr_lookup T (i + Suc ii) (j + Suc ii))" by simp
      qed moreover
      note 3(3) moreover
      have "\<And>x k. \<lbrakk>x \<in> set xs; x = Some k\<rbrakk> \<Longrightarrow> k < length zs" proof -
        fix x k assume "x \<in> set xs" "x = Some k"
        with 3(4)[of x k] show "k < length zs" by simp
      qed moreover
      from 3(5) H Suc J have "length xs + Suc ii = length T + 1" "i' < length xs" "j' < length xs" by simp+
      ultimately have "(fst (mk_eqcl xs zs (Suc ii) T) ! i' = fst (mk_eqcl xs zs (Suc ii) T) ! j') = (\<not> tr_lookup T (i' + Suc ii) (j' + Suc ii))" by (rule 3(1))
      with J Suc show ?thesis by (simp add: split_beta)
    qed
  } note L = this
  have "i < j \<or> i = j \<or> i > j" by auto
  thus ?case proof (elim disjE)
    assume "i > j"
    with 3(6) L have "(fst (mk_eqcl (Some l # xs) zs ii T) ! j = fst (mk_eqcl (Some l # xs) zs ii T) ! i) = (\<not> tr_lookup T (j + ii) (i + ii))" by simp
    thus ?thesis by (auto simp: tr_lookup_def)
  qed (insert 3(7) L, simp add: tr_lookup_def)+
qed

definition min_dfa :: "dfa \<Rightarrow> dfa" where
  "min_dfa = (\<lambda>(bd, as). let (os, ns) = mk_eqcl (replicate (length bd) None) [] 0 (fixpt (bd, as) (init_tr (bd, as))) in
      (map (\<lambda>p. bdd_map (\<lambda>q. os ! q) (bd ! p)) ns, map (\<lambda>p. as ! p) ns))"

definition eq_nodes :: "dfa \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "eq_nodes = (\<lambda>M v p q. \<not> (\<exists>n. dist_nodes M n v p q))"

lemma mk_eqcl_fixpt_fst_bound:
  assumes "dfa_is_node M i"
  shows "fst (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! i < length (snd (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))))"
  (is "fst ?M ! i < length (snd ?M)")
proof -
  { fix x k assume H: "x \<in> set (replicate (length (fst M)) (None::nat option))" "x = Some k"
    hence "k < length []" by (cases "length (fst M) = 0") simp+
  } moreover
  from assms have "fst ?M ! i \<in> set (fst ?M)" by (simp add: dfa_is_node_def mk_eqcl_len_fst)
  ultimately show ?thesis by (rule mk_eqcl_bound)
qed

lemma mk_eqcl_fixpt_fst_nth:
  assumes "wf_dfa M v"
  and "dfa_is_node M p" and "dfa_is_node M q"
  shows "(fst (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! p = fst (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! q)
          = eq_nodes M v p q"
  (is "(fst ?M ! p = fst ?M ! q) = eq_nodes M v p q")
proof -
  have WF: "wf_tr M (fixpt M (init_tr M))" by (simp only: fixpt_wf init_tr_wf)
  
  have "(fst ?M ! p = fst ?M ! q) = (\<not> tr_lookup (fixpt M (init_tr M)) p q)" proof -
    { fix i j k assume H: "i < length (replicate (length (fst M)) None)" "j < length (replicate (length (fst M)) None)" "replicate (length (fst M)) None ! i = Some k"
      hence "(replicate (length (fst M)) None ! j = Some k) = (\<not> tr_lookup (fixpt M (init_tr M)) (i + 0) (j + 0))" by simp
    }
    moreover
    have "\<And>a b c. \<lbrakk>a \<le> length (fixpt M (init_tr M)); b \<le> length (fixpt M (init_tr M)); c \<le> length (fixpt M (init_tr M)); \<not> tr_lookup (fixpt M (init_tr M)) a b; \<not> tr_lookup (fixpt M (init_tr M)) b c\<rbrakk>
      \<Longrightarrow> \<not> tr_lookup (fixpt M (init_tr M)) a c" proof -
      fix a b c assume H': "a \<le> length (fixpt M (init_tr M))" "b \<le> length (fixpt M (init_tr M))" "c \<le> length (fixpt M (init_tr M))" "\<not> tr_lookup (fixpt M (init_tr M)) a b"
        "\<not> tr_lookup (fixpt M (init_tr M)) b c"
      { fix q assume H'': "q \<le> length (fixpt M (init_tr M))"
        from assms have "length (fst M) > 0" by (simp add: wf_dfa_def) 
        then obtain m where M: "length (fst M) = Suc m" by (cases "length (fst M)") simp+
        hence M': "m = length (fst M) - 1" by simp
        with H'' WF have "q \<le> m" by (simp add: wf_tr_def)
        with M have "q < length (fst M)" by simp
      }
      with H' have D: "dfa_is_node M a" "dfa_is_node M b" "dfa_is_node M c" by (auto simp: dfa_is_node_def)
      with H'(4,5) assms(1) have "\<not> (\<exists>n. dist_nodes M n v a b)" "\<not> (\<exists>n. dist_nodes M n v b c)" by (simp add: fixpt_dist_nodes[symmetric])+
      hence "\<not> (\<exists>n. dist_nodes M n v a c)" by (auto simp: dist_nodes_def)
      with H' assms D show "\<not> tr_lookup (fixpt M (init_tr M)) a c" by (simp add: fixpt_dist_nodes[symmetric])
    qed
    moreover have "\<And>x k. \<lbrakk>x \<in> set (replicate (length (fst M)) None); x = Some k\<rbrakk> \<Longrightarrow> k < length []" proof -
      fix x k assume "x \<in> set (replicate (length (fst M)) (None::nat option))" "x = Some k"
      thus "k < length []" by (cases "length (fst M) = 0") simp+
    qed
    moreover from WF assms have "length (replicate (length (fst M)) None) + 0 = length (fixpt M (init_tr M)) + 1" by (simp add: wf_tr_def wf_dfa_def)
    moreover from assms have "p < length (replicate (length (fst M)) None)" "q < length (replicate (length (fst M)) None)" by (simp add: dfa_is_node_def)+
    ultimately have "(fst ?M ! p = fst ?M ! q) = (\<not> tr_lookup (fixpt M (init_tr M)) (p+0) (q+0))" by (rule mk_eqcl_fst_nth)
    thus ?thesis by simp
  qed
  also from assms have "\<dots> = eq_nodes M v p q" by (simp only: fixpt_dist_nodes eq_nodes_def)
  finally show ?thesis by simp
qed

lemma mk_eqcl_fixpt_fst_snd_nth:
  assumes "i < length (snd (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))))"
  and "wf_dfa M v"
  shows "snd (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! i < length (fst (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M)))) \<and>
    fst (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! (snd (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! i) = i"
  (is "snd ?M ! i < length (fst ?M) \<and> fst ?M ! (snd ?M ! i) = i")
proof -
  have "\<And>i. i < length [] \<Longrightarrow> [] ! i < length (replicate (length (fst M)) None) + 0 \<and> (0 \<le> [] ! i \<longrightarrow> replicate (length (fst M)) None ! ([] ! i - 0) = Some i)" by simp
  moreover have "\<And>j1 j2. \<lbrakk>j1 < j2; j2 < length []\<rbrakk> \<Longrightarrow> [] ! j1 < [] ! j2" by simp
  moreover have "\<And>z. z \<in> set [] \<Longrightarrow> z < 0" by simp
  moreover note assms(1)
  moreover have "length (replicate (length (fst M)) None) + 0 \<le> length (fixpt M (init_tr M)) + 1" proof -
    have WF: "wf_tr M (fixpt M (init_tr M))" by (simp only: init_tr_wf fixpt_wf)
    from assms have "length (fst M) > 0" by (simp add: wf_dfa_def)
    then obtain m where M:"length (fst M) = Suc m" by (cases "length (fst M)") simp+
    hence M': "m = length (fst M) - 1" by simp
    with WF have "length (fixpt M (init_tr M)) = m" by (simp add: wf_tr_def)
    with M show ?thesis by simp
  qed
  ultimately have "snd ?M ! i < length (fst ?M) + 0 \<and> (0 \<le> snd ?M ! i \<longrightarrow> fst ?M ! (snd ?M ! i - 0) = i)" by (rule mk_eqcl_fst_snd)
  thus ?thesis by simp
qed

lemma eq_nodes_dfa_trans:
  assumes "eq_nodes M v p q"
  and "is_alph v bs"
  shows "eq_nodes M v (dfa_trans M p bs) (dfa_trans M q bs)"
proof (rule ccontr)
  assume H: "\<not> eq_nodes M v (dfa_trans M p bs) (dfa_trans M q bs)"
  then obtain n w where "length w = n" "list_all (is_alph v) w" "dfa_accepting M (dfa_steps M (dfa_trans M p bs) w) \<noteq> dfa_accepting M (dfa_steps M (dfa_trans M q bs) w)"
    unfolding eq_nodes_def dist_nodes_def by blast
  with assms have "length (bs # w) = Suc n" "list_all (is_alph v) (bs # w)" "dfa_accepting M (dfa_steps M p (bs # w)) \<noteq> dfa_accepting M (dfa_steps M q (bs # w))" by simp+
  hence "\<not> eq_nodes M v p q" unfolding eq_nodes_def dist_nodes_def by blast
  with assms show False by simp
qed

lemma mk_eqcl_fixpt_trans:
  assumes "wf_dfa M v"
  and "dfa_is_node M p"
  and "is_alph v bs"
  shows "dfa_trans (min_dfa M) (fst (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! p) bs = 
    fst (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! (dfa_trans M p bs)"
  (is "dfa_trans (min_dfa M) (fst ?M ! p) bs = fst ?M ! (dfa_trans M p bs)")
proof -
  let ?q = "snd ?M ! (fst ?M ! p)"
  from assms have I1: "?q < length (fst ?M)" "fst ?M ! ?q = fst ?M ! p" by (simp add: mk_eqcl_fixpt_fst_bound mk_eqcl_fixpt_fst_snd_nth)+
  with assms have I2: "bddh (length bs) (fst M ! ?q)" by (simp add: mk_eqcl_len_fst wf_dfa_def list_all_iff is_alph_def)
  from I1 have I3: "dfa_is_node M ?q" by (simp add: mk_eqcl_len_fst dfa_is_node_def)
  with assms I1 have "eq_nodes M v p ?q" by (simp add: mk_eqcl_fixpt_fst_nth[symmetric])
  with assms have "eq_nodes M v (dfa_trans M p bs) (dfa_trans M ?q bs)" by (simp add: eq_nodes_dfa_trans)
  with assms I3 have "fst ?M ! (dfa_trans M p bs) = fst ?M ! (dfa_trans M ?q bs)" by (simp add: dfa_trans_is_node mk_eqcl_fixpt_fst_nth)

  with assms I2 show ?thesis by (simp add: dfa_trans_def min_dfa_def split_beta mk_eqcl_fixpt_fst_bound bdd_map_bdd_lookup)
qed  

lemma mk_eqcl_fixpt_steps:
  assumes "wf_dfa M v"
  and "dfa_is_node M p"
  and "list_all (is_alph v) w"
  shows "dfa_steps (min_dfa M) (fst (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! p) w =
    fst (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! (dfa_steps M p w)"
  (is "dfa_steps (min_dfa M) (fst ?M ! p) w = fst ?M ! (dfa_steps M p w)")
using assms by (induct w arbitrary: p) (simp add: mk_eqcl_fixpt_trans dfa_trans_is_node)+

lemma mk_eqcl_fixpt_startnode:
  assumes "length (fst M) > 0"
  shows "length (snd (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M)))) > 0 \<and> 
    fst (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! 0 = 0 \<and> snd (mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))) ! 0 = 0"
  (is "length (snd ?M) > 0 \<and> fst ?M ! 0 = 0 \<and> snd ?M ! 0 = 0")
proof -
  from assms obtain k where K: "length (fst M) = Suc k" by (cases "length (fst M)") simp+
  from K have "length (snd ?M) = length (snd (mk_eqcl (mk_eqcl' (replicate k None) 0 (Suc 0) 0 (fixpt M (init_tr M))) [0] (Suc 0) (fixpt M (init_tr M))))" by (simp add: split_beta)
  also have "\<dots> \<ge> length [0::nat]" by (simp only: mk_eqcl_len_snd)
  finally have "length (snd ?M) > 0" by auto
  with K show ?thesis by (simp add: split_beta mk_eqcl_snd_nth)
qed

lemma min_dfa_wf:
  "wf_dfa M v \<Longrightarrow> wf_dfa (min_dfa M) v"
proof -
  assume H: "wf_dfa M v"
  obtain bd as where "min_dfa M = (bd, as)" by (cases "min_dfa M") auto
  hence M: "bd = fst (min_dfa M)" "as = snd (min_dfa M)" by simp+
  let ?M = "mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))"

  { fix x assume "x \<in> set bd"
    then obtain i where I: "i < length bd" "x = bd ! i" by (auto simp: in_set_conv_nth)

    with M H have "snd ?M ! i < length (fst ?M)" by (simp add: min_dfa_def split_beta mk_eqcl_fixpt_fst_snd_nth)
    hence N: "dfa_is_node M (snd ?M ! i)" by (simp add: mk_eqcl_len_fst dfa_is_node_def)
    with H have BH: "bddh v (fst M ! (snd ?M ! i))" by (simp add: wf_dfa_def list_all_iff dfa_is_node_def)

    from I M have BI: "bd ! i = bdd_map (\<lambda>q. fst ?M ! q) (fst M ! (snd ?M ! i))" by (simp add: split_beta min_dfa_def)
    with BH have G1: "bddh v (bd ! i)" by (simp add: bddh_bdd_map)

    from H N have "bdd_all (dfa_is_node M) (fst M ! (snd ?M ! i))" by (simp add: wf_dfa_def list_all_iff dfa_is_node_def)
    moreover
    { fix q assume "dfa_is_node M q"
      hence "fst ?M ! q < length (snd ?M)" by (simp add: mk_eqcl_fixpt_fst_bound)
      hence "dfa_is_node (min_dfa M) (fst ?M ! q)" by (simp add: dfa_is_node_def min_dfa_def split_beta)
    }
    ultimately have "bdd_all (dfa_is_node (min_dfa M)) (bdd_map (\<lambda>q. fst ?M ! q) (fst M ! (snd ?M ! i)))" by (simp add: bdd_all_bdd_map)
    with G1 BI I have "bddh v x \<and> bdd_all (dfa_is_node (min_dfa M)) x" by simp
  }
  hence G: "list_all (bddh v) bd \<and> list_all (bdd_all (dfa_is_node (min_dfa M))) bd" by (simp add: list_all_iff)

  from H have "length (fst M) > 0" by (simp add: wf_dfa_def)
  hence "length (snd ?M) > 0" by (auto simp only: mk_eqcl_fixpt_startnode)
  
  with G M show "wf_dfa (min_dfa M) v" by (simp add: wf_dfa_def min_dfa_def split_beta)
qed
  

lemma min_dfa_accept:
  assumes "wf_dfa M v"
  and "list_all (is_alph v) w"
  shows "dfa_accepts (min_dfa M) w = dfa_accepts M w"
proof -
  let ?M = "mk_eqcl (replicate (length (fst M)) None) [] 0 (fixpt M (init_tr M))"

  from assms have "length (fst M) > 0" by (simp add: wf_dfa_def)
  hence SN: "length (snd ?M) > 0 \<and> fst ?M ! 0 = 0 \<and> snd ?M ! 0 = 0" by (auto simp only: mk_eqcl_fixpt_startnode)
  have D: "dfa_steps (min_dfa M) 0 w = fst ?M ! dfa_steps M 0 w" proof -
    from assms have "dfa_is_node M 0" by (simp add: wf_dfa_def dfa_is_node_def)
    moreover from SN have "dfa_steps (min_dfa M) 0 w = dfa_steps (min_dfa M) (fst ?M ! 0) w" by simp
    moreover note assms 
    ultimately show ?thesis by (simp add: mk_eqcl_fixpt_steps)
  qed

  from assms have WF: "wf_dfa (min_dfa M) v" by (simp add: min_dfa_wf)
  hence "dfa_is_node (min_dfa M) 0" by (simp add: dfa_startnode_is_node)
  with WF assms have "dfa_is_node (min_dfa M) (dfa_steps (min_dfa M) 0 w)" by (simp add: dfa_steps_is_node)
  with D have DN: "dfa_is_node (min_dfa M) (fst ?M ! dfa_steps M 0 w)" by simp

  let ?q = "snd ?M ! (fst ?M ! dfa_steps M 0 w)"

  from assms have N: "dfa_is_node M (dfa_steps M 0 w)" by (simp add: dfa_steps_is_node dfa_startnode_is_node)
  with assms have I: "?q < length (fst ?M)" "fst ?M ! ?q = fst ?M ! dfa_steps M 0 w" by (simp add: mk_eqcl_fixpt_fst_bound mk_eqcl_fixpt_fst_snd_nth)+
  hence "dfa_is_node M ?q" by (simp add: mk_eqcl_len_fst dfa_is_node_def)
  with assms N I have EQ: "eq_nodes M v (dfa_steps M 0 w) ?q" by (simp add: mk_eqcl_fixpt_fst_nth[symmetric])
  have A: "dfa_accepting M (dfa_steps M 0 w) = dfa_accepting M ?q" proof (rule ccontr)
    assume H: "dfa_accepting M (dfa_steps M 0 w) \<noteq> dfa_accepting M ?q"
    hence "dist_nodes M 0 v (dfa_steps M 0 w) ?q" by (auto simp: dist_nodes_def)
    with EQ show False by (simp add: eq_nodes_def)
  qed

  from D have "dfa_accepts (min_dfa M) w = snd (min_dfa M) ! (fst ?M ! dfa_steps M 0 w)" by (simp add: accepts_def dfa_accepting_def)
  also from WF DN have "\<dots> = dfa_accepting M ?q" by (simp add: dfa_is_node_def wf_dfa_def min_dfa_def split_beta dfa_accepting_def)
  also from A have "\<dots> = dfa_accepts M w" by (simp add: accepts_def)

  finally show ?thesis by simp
qed


section \<open>NFAs\<close>

type_synonym nbddtable = "bool list bdd list"
type_synonym nfa = "nbddtable \<times> astate"

definition
  nfa_is_node :: "nfa \<Rightarrow> bool list \<Rightarrow> bool" where
  "nfa_is_node A = (\<lambda>qs. length qs = length (fst A))"

definition
  wf_nfa :: "nfa \<Rightarrow> nat \<Rightarrow> bool" where
  "wf_nfa A n =
    (list_all (bddh n) (fst A) \<and>
     list_all (bdd_all (nfa_is_node A)) (fst A) \<and>
     length (snd A) = length (fst A) \<and>
     length (fst A) > 0)"

definition
  set_of_bv :: "bool list \<Rightarrow> nat set" where
  "set_of_bv bs = {i. i < length bs \<and> bs ! i}"

fun
  bv_or :: "bool list \<Rightarrow> bool list \<Rightarrow> bool list"
where
  "bv_or [] [] = []" |
  "bv_or (x # xs) (y # ys) = (x \<or> y) # (bv_or xs ys)"

lemma bv_or_nth:
  assumes "length l = length r"
  assumes "i < length l"
  shows "bv_or l r ! i = (l ! i \<or> r ! i)"
using assms proof (induct l r arbitrary: i rule: bv_or.induct)
  case (2 xx xss yy yss ii)
  have "ii = 0 \<or> ii > 0" by auto
  thus ?case proof (elim disjE)
    assume "ii > 0"
    then obtain j where J: "ii = Suc j" by (induct ii) simp+
    with 2 show ?thesis by simp
  qed simp
qed simp+

lemma bv_or_length:
  assumes "length l = length r"
  shows "length (bv_or l r) = length l"
using assms by (induct l r rule: bv_or.induct) simp+

lemma bv_or_set_of_bv:
  assumes "nfa_is_node A p" and "nfa_is_node A q"
  shows "set_of_bv (bv_or p q) = set_of_bv p \<union> set_of_bv q"
using assms by (auto simp: nfa_is_node_def set_of_bv_def bv_or_length bv_or_nth)

lemma bv_or_is_node: "\<lbrakk>nfa_is_node A p; nfa_is_node A q\<rbrakk> \<Longrightarrow> nfa_is_node A (bv_or p q)"
  by (simp add: bv_or_length nfa_is_node_def)

fun subsetbdd
where
  "subsetbdd [] [] bdd = bdd"
| "subsetbdd (bdd' # bdds) (b # bs) bdd =
     (if b then subsetbdd bdds bs (bdd_binop bv_or bdd bdd') else subsetbdd bdds bs bdd)"

definition
  nfa_emptybdd :: "nat \<Rightarrow> bool list bdd" where
  "nfa_emptybdd n = Leaf (replicate n False)"

lemma bdd_all_is_node_subsetbdd:
  assumes "list_all (bdd_all (nfa_is_node A)) (fst A)"
  and "nfa_is_node A q"
  shows "bdd_all (nfa_is_node A) (subsetbdd (fst A) q (nfa_emptybdd (length q)))"
proof -
  { fix bdds :: "bool list bdd list" and q :: "bool list" and bd :: "bool list bdd" and n
    assume "list_all (bdd_all (\<lambda>l. length l = n)) bdds" and "bdd_all (\<lambda>l. length l = n) bd" and "length bdds = length q"
    hence "bdd_all (\<lambda>l. length l = n) (subsetbdd bdds q bd)" by (induct bdds q bd rule: subsetbdd.induct) (simp add: bdd_all_bdd_binop[of "\<lambda>l. length l =n" _ "\<lambda>l. length l = n"] bv_or_length)+
  }
  with assms show ?thesis by (simp add: nfa_is_node_def nfa_emptybdd_def)
qed

lemma bddh_subsetbdd:
  assumes "list_all (bddh l) (fst A)"
  and "bddh l bdd'"
  and "nfa_is_node A q"
  shows "bddh l (subsetbdd (fst A) q bdd')"
using assms unfolding nfa_is_node_def by (induct ("fst A") q bdd' rule: subsetbdd.induct) (simp add: bddh_binop)+

lemma bdd_lookup_subsetbdd':
  assumes "length bdds = length q"
  and "\<forall>x \<in> set bdds. bddh (length ws) x"
  and "bddh (length ws) obdd"
  and "\<And>bs w. \<lbrakk>bs \<in> set bdds; length w = length ws\<rbrakk> \<Longrightarrow> length (bdd_lookup bs w) = c"
  and "\<And>w. length w = length ws \<Longrightarrow> length (bdd_lookup obdd w) = c"
  and "a < c"
  shows "bdd_lookup (subsetbdd bdds q obdd) ws ! a = ((\<exists>i < length q. q ! i \<and> bdd_lookup (bdds ! i) ws ! a) \<or> bdd_lookup obdd ws ! a)"
using assms proof (induct bdds q obdd rule: subsetbdd.induct)
  case (2 bdd' bdds x xs bdd)
  show ?case proof (cases x)
    case True
    with 2 have H: "bdd_lookup (subsetbdd bdds xs (bdd_binop bv_or bdd bdd')) ws ! a =
     ((\<exists>i<length xs. xs ! i \<and> bdd_lookup (bdds ! i) ws ! a) \<or> bdd_lookup (bdd_binop bv_or bdd bdd') ws ! a)" by (simp add: bddh_binop bdd_lookup_binop bv_or_length)
    from 2 have "((\<exists>i < length xs. xs ! i \<and> bdd_lookup (bdds ! i) ws ! a) \<or> bdd_lookup (bdd_binop bv_or bdd bdd') ws ! a) = 
      ((\<exists>i < length xs. xs ! i \<and> bdd_lookup (bdds ! i) ws ! a) \<or> (bdd_lookup bdd' ws) ! a \<or> (bdd_lookup bdd ws) ! a)" by (auto simp: bdd_lookup_binop bv_or_nth)
    also have "\<dots> = ((\<exists>i < Suc (length xs). (True # xs) ! i \<and> bdd_lookup ((bdd' # bdds) ! i) ws ! a) \<or> bdd_lookup bdd ws ! a)"
      (is "((\<exists>i. ?P i) \<or> ?Q \<or> ?R) = ((\<exists>i. ?S i) \<or> ?R)") proof
      assume "(\<exists>i. ?P i) \<or> ?Q \<or> ?R" thus "(\<exists>i. ?S i) \<or> ?R" by (elim disjE) auto
    next
      assume "(\<exists>i. ?S i) \<or> ?R" thus "(\<exists>i. ?P i) \<or> ?Q \<or> ?R" proof (elim disjE)
        assume "\<exists>i. ?S i"
        then obtain i where I: "?S i" ..
        { assume "i = 0" with I have "?Q" by simp }
        { assume "i \<noteq> 0" then obtain j where "i = Suc j" by (cases i) simp+ with I have "\<exists>j. ?P j" by auto }
        with \<open>i=0 \<Longrightarrow> ?Q\<close> show ?thesis by (cases "i=0") simp+
      qed simp
    qed
    finally have "((\<exists>i<length xs. xs ! i \<and> bdd_lookup (bdds ! i) ws ! a) \<or> bdd_lookup (bdd_binop bv_or bdd bdd') ws ! a) =
       ((\<exists>i<Suc (length xs). (True # xs) ! i \<and> bdd_lookup ((bdd' # bdds) ! i) ws ! a) \<or> bdd_lookup bdd ws ! a)" by simp
    with True H show ?thesis by simp
  next
    case False
    with 2 have H: "bdd_lookup (subsetbdd bdds xs bdd) ws ! a = ((\<exists>i < length xs. xs ! i \<and> bdd_lookup (bdds ! i) ws ! a) \<or> bdd_lookup bdd ws ! a)" by simp
    have "((\<exists>i<length xs. xs ! i \<and> bdd_lookup (bdds ! i) ws ! a) \<or> bdd_lookup bdd ws ! a) =
       ((\<exists>i<Suc (length xs). (False # xs) ! i \<and> bdd_lookup ((bdd' # bdds) ! i) ws ! a) \<or> bdd_lookup bdd ws ! a)"
      (is "((\<exists>i. ?S i) \<or> ?R) = ((\<exists>i. ?P i) \<or> ?R)") proof
      assume "(\<exists>i. ?S i) \<or> ?R" thus "(\<exists>i. ?P i) \<or> ?R" by (elim disjE) auto
    next
      assume "(\<exists>i. ?P i) \<or> ?R" thus "(\<exists>i. ?S i) \<or> ?R" proof (elim disjE)
        assume "\<exists>i. ?P i"
        then obtain i where "?P i" ..
        then obtain j where "i = Suc j" by (cases i) simp+
        with \<open>?P i\<close> show ?thesis by auto
      qed simp
    qed
    with False H show ?thesis by simp
  qed
qed simp+
    
lemma bdd_lookup_subsetbdd:
  assumes "wf_nfa N (length ws)"
  and "nfa_is_node N q"
  and "a < length (fst N)"
  shows "bdd_lookup (subsetbdd (fst N) q (nfa_emptybdd (length q))) ws ! a = (\<exists>i< length q. q ! i \<and> bdd_lookup (fst N ! i) ws ! a)"
proof -
  {
    fix w :: "bool list"
    assume H: "length w = length ws"
    from assms have "\<forall>bd \<in> set (fst N). bdd_all (nfa_is_node N) bd" by (simp add: wf_nfa_def list_all_iff) moreover
    from assms have "\<forall>bd \<in> set (fst N). bddh (length ws) bd" by (simp add: wf_nfa_def list_all_iff) moreover
    note H
    ultimately have "\<forall>bd \<in> set (fst N). nfa_is_node N (bdd_lookup bd w)" by (simp add: bdd_all_bdd_lookup)
  }
  with assms have "bdd_lookup (subsetbdd (fst N) q (nfa_emptybdd (length q))) ws ! a = ((\<exists>i < length q. q ! i \<and> bdd_lookup (fst N ! i) ws ! a) \<or> bdd_lookup (nfa_emptybdd (length q)) ws ! a)"
    by (simp add: bdd_lookup_subsetbdd' nfa_is_node_def wf_nfa_def list_all_iff nfa_emptybdd_def)
  with assms show ?thesis by (auto simp: nfa_emptybdd_def nfa_is_node_def)
qed

definition
  nfa_trans :: "nfa \<Rightarrow> bool list \<Rightarrow> bool list \<Rightarrow> bool list" where
  "nfa_trans A qs bs = bdd_lookup (subsetbdd (fst A) qs (nfa_emptybdd (length qs))) bs"

fun nfa_accepting' :: "bool list \<Rightarrow> bool list \<Rightarrow> bool" where
  "nfa_accepting' [] bs = False"
| "nfa_accepting' as [] = False"
| "nfa_accepting' (a # as) (b # bs) = (a \<and> b \<or> nfa_accepting' as bs)"
definition nfa_accepting :: "nfa \<Rightarrow> bool list \<Rightarrow> bool" where
  "nfa_accepting A = nfa_accepting' (snd A)"

lemma nfa_accepting'_set_of_bv: "nfa_accepting' l r = (set_of_bv l \<inter> set_of_bv r \<noteq> {})"
proof -
  have nfa_accepting_help: "\<And>as q. nfa_accepting' as q = (\<exists>i. i < length as \<and> i < length q \<and> as ! i \<and> q ! i)"
  proof - 
    fix as q 
    show "nfa_accepting' as q = (\<exists>i < length as. i < length q \<and> as ! i \<and> q ! i)"
    proof (induct as q rule: nfa_accepting'.induct)
      case (3 a as q qs)
      thus ?case proof (cases "a\<and>q")
        case False
        with 3 have "nfa_accepting' as qs = (\<exists>i < length as. i < length qs \<and> as ! i \<and> qs ! i)" (is "?T = _") by simp
        also have "\<dots> = (\<exists>j < length as. j < length qs \<and> (a#as) ! Suc j \<and> (q#qs) ! Suc j)" by simp
        also have "\<dots> = (\<exists>j < length (a#as). j < length (q#qs) \<and> (a#as) ! j \<and> (q#qs) ! j)" (is "(\<exists>j. ?P j) = (\<exists>j. ?Q j)")
        proof
          assume "\<exists>j. ?P j"
          then obtain j where "?P j" ..
          hence "?Q (Suc j)" by simp
          thus "\<exists>j. ?Q j" by (rule exI)
        next
          assume "\<exists>j. ?Q j"
          then obtain j where J: "?Q j" ..
          with False obtain i where "j = Suc i" by (cases j) simp+
          with J have "?P i" by simp
          thus "\<exists>i. ?P i" by (rule exI)
        qed
        also from False have "\<dots> = ((a\<and>q \<and> ?Q 0) \<or> (\<not> (a\<and>q) \<and> (\<exists>j. ?Q j)))" by auto
        also have "\<dots> = ((a \<and> q \<and> (\<exists>j. ?Q j)) \<or> (\<not>(a\<and>q) \<and> (\<exists>j. ?Q j)))" by auto
        also have "\<dots> = (\<exists>j. ?Q j)" by auto
        finally have "?T = (\<exists>j. ?Q j)" .
        with False show ?thesis by auto
      qed (auto simp: 3)
    qed simp+
  qed
  hence "nfa_accepting' l r = (\<exists>i. i < length l \<and> i < length r \<and> l ! i \<and> r ! i)" by simp
  also have "\<dots> = (\<exists>i. i \<in> set_of_bv l \<and> i \<in> set_of_bv r)" by (auto simp: set_of_bv_def)
  also have "\<dots> = (set_of_bv l \<inter> set_of_bv r \<noteq> {})" by auto
  finally show ?thesis .
qed

lemma nfa_accepting_set_of_bv: "nfa_accepting A q = (set_of_bv (snd A) \<inter> set_of_bv q \<noteq> {})"
  by (simp add: nfa_accepting'_set_of_bv nfa_accepting_def)

definition
  nfa_startnode :: "nfa \<Rightarrow> bool list" where
  "nfa_startnode A = (replicate (length (fst A)) False)[0:=True]"

locale aut_nfa =
  fixes A n
  assumes well_formed: "wf_nfa A n"

sublocale aut_nfa < Automaton "nfa_trans A" "nfa_is_node A" "is_alph n"
proof
  fix q a
  assume Q: "nfa_is_node A q" and A: "is_alph n a"
  with well_formed have "bdd_all (nfa_is_node A) (subsetbdd (fst A) q (nfa_emptybdd (length q)))"
    by (simp add: wf_nfa_def bdd_all_is_node_subsetbdd)
  moreover from well_formed Q have "bddh n (subsetbdd (fst A) q (nfa_emptybdd (length q)))"
    by (simp add: wf_nfa_def nfa_emptybdd_def bddh_subsetbdd)
  with A have "bddh (length a) (subsetbdd (fst A) q (nfa_emptybdd (length q)))" by (simp add: is_alph_def)
  ultimately have "nfa_is_node A (bdd_lookup (subsetbdd (fst A) q (nfa_emptybdd (length q))) a)"
    by (simp add: bdd_all_bdd_lookup)
  then show "nfa_is_node A (nfa_trans A q a)" by (simp add: nfa_trans_def)
qed

context aut_nfa begin
lemmas trans_is_node = trans_is_node
lemmas steps_is_node = steps_is_node
lemmas reach_is_node = reach_is_node
end

lemmas nfa_trans_is_node = aut_nfa.trans_is_node [OF aut_nfa.intro]
lemmas nfa_steps_is_node = aut_nfa.steps_is_node [OF aut_nfa.intro]
lemmas nfa_reach_is_node = aut_nfa.reach_is_node [OF aut_nfa.intro]

abbreviation "nfa_steps A \<equiv> foldl (nfa_trans A)"
abbreviation "nfa_accepts A \<equiv> accepts (nfa_trans A) (nfa_accepting A) (nfa_startnode A)"
abbreviation "nfa_reach A \<equiv> reach (nfa_trans A)"

lemma nfa_startnode_is_node: "wf_nfa A n \<Longrightarrow> nfa_is_node A (nfa_startnode A)"
  by (simp add: nfa_is_node_def wf_nfa_def nfa_startnode_def)


section \<open>Automata Constructions\<close>

subsection \<open>Negation\<close>

definition
  negate_dfa :: "dfa \<Rightarrow> dfa" where
  "negate_dfa = (\<lambda>(t,a). (t, map Not a))"

lemma negate_wf_dfa: "wf_dfa (negate_dfa A) l = wf_dfa A l"
  by (simp add: negate_dfa_def wf_dfa_def dfa_is_node_def split_beta)

lemma negate_negate_dfa: "negate_dfa (negate_dfa A) = A"
proof (induct A)
  case (Pair t a) thus ?case by (induct a) (simp add: negate_dfa_def)+
qed

lemma dfa_accepts_negate: 
  assumes "wf_dfa A n"
  and "list_all (is_alph n) bss"
  shows "dfa_accepts (negate_dfa A) bss = (\<not> dfa_accepts A bss)"
proof -
  have "dfa_steps (negate_dfa A) 0 bss = dfa_steps A 0 bss"
    by (simp add: negate_dfa_def dfa_trans_def [abs_def] split_beta)
  moreover from assms have "dfa_is_node A (dfa_steps A 0 bss)"
    by (simp add: dfa_steps_is_node dfa_startnode_is_node)
  ultimately show ?thesis using assms
    by (simp add: accepts_def dfa_accepting_def wf_dfa_def dfa_is_node_def negate_dfa_def split_beta)
qed


subsection \<open>Product Automaton\<close>

definition
  prod_succs :: "dfa \<Rightarrow> dfa \<Rightarrow> nat \<times> nat \<Rightarrow> (nat \<times> nat) list" where
  "prod_succs A B = (\<lambda>(i, j). add_leaves (bdd_binop Pair (fst A ! i) (fst B ! j)) [])"

definition
  "prod_is_node A B = (\<lambda>(i, j). dfa_is_node A i \<and> dfa_is_node B j)"

definition
  prod_invariant :: "dfa \<Rightarrow> dfa \<Rightarrow> nat option list list \<times> (nat \<times> nat) list \<Rightarrow> bool" where
  "prod_invariant A B = (\<lambda>(tab, ps).
     length tab = length (fst A) \<and> (\<forall>tab'\<in>set tab. length tab' = length (fst B)))"

definition
  "prod_ins = (\<lambda>(i, j). \<lambda>(tab, ps).
     (tab[i := (tab ! i)[j := Some (length ps)]],
      ps @ [(i, j)]))"

definition
  prod_memb :: "nat \<times> nat \<Rightarrow> nat option list list \<times> (nat \<times> nat) list \<Rightarrow> bool" where
  "prod_memb = (\<lambda>(i, j). \<lambda>(tab, ps). tab ! i ! j \<noteq> None)"

definition
  prod_empt :: "dfa \<Rightarrow> dfa \<Rightarrow> nat option list list \<times> (nat \<times> nat) list" where
  "prod_empt A B = (replicate (length (fst A)) (replicate (length (fst B)) None), [])"

definition
  prod_dfs :: "dfa \<Rightarrow> dfa \<Rightarrow> nat \<times> nat \<Rightarrow> nat option list list \<times> (nat \<times> nat) list" where
  "prod_dfs A B x = gen_dfs (prod_succs A B) prod_ins prod_memb (prod_empt A B) [x]"

definition
  binop_dfa :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> dfa \<Rightarrow> dfa \<Rightarrow> dfa" where
  "binop_dfa f A B =
    (let (tab, ps) = prod_dfs A B (0, 0)
     in
       (map (\<lambda>(i, j). bdd_binop (\<lambda>k l. the (tab ! k ! l)) (fst A ! i) (fst B ! j)) ps,
        map (\<lambda>(i, j). f (snd A ! i) (snd B ! j)) ps))"

locale prod_DFS =
  fixes A B n
  assumes well_formed1: "wf_dfa A n"
  and well_formed2: "wf_dfa B n"

sublocale prod_DFS < DFS "prod_succs A B" "prod_is_node A B" "prod_invariant A B" prod_ins prod_memb "prod_empt A B"
  apply unfold_locales
  apply (simp add: prod_memb_def prod_ins_def prod_invariant_def
    prod_is_node_def split_paired_all dfa_is_node_def)
  apply (case_tac "a = aa")
  apply (case_tac "b = ba")
  apply auto[3]
  apply (simp add: prod_memb_def prod_empt_def prod_is_node_def split_paired_all dfa_is_node_def)
  apply (insert well_formed1 well_formed2)[]
  apply (simp add: prod_is_node_def prod_succs_def split_paired_all dfa_is_node_def wf_dfa_def)
  apply (drule conjunct1 [OF conjunct2])+
  apply (simp add: list_all_iff)
  apply (rule ballI)
  apply (simp add: split_paired_all)
  apply (drule subsetD [OF add_leaves_binop_subset [where xs="[]" and ys="[]", simplified]])
  apply clarify
  apply (drule_tac x="fst A ! a" in bspec)
  apply simp
  apply (drule_tac x="fst B ! b" in bspec)
  apply simp
  apply (simp add: add_leaves_bdd_all_eq' list_all_iff)
  apply (simp add: prod_invariant_def prod_empt_def set_replicate_conv_if)
  apply (simp add: prod_is_node_def prod_invariant_def
    prod_memb_def prod_ins_def split_paired_all dfa_is_node_def)
  apply (rule ballI)
  apply (drule subsetD [OF set_update_subset_insert])
  apply auto
  apply (simp add: prod_is_node_def dfa_is_node_def)
  done

context prod_DFS
begin

lemma prod_dfs_eq_rtrancl: "prod_is_node A B x \<Longrightarrow> prod_is_node A B y \<Longrightarrow>
  prod_memb y (prod_dfs A B x) = ((x, y) \<in> (succsr (prod_succs A B))\<^sup>*)"
  by (unfold prod_dfs_def) (rule dfs_eq_rtrancl)

lemma prod_dfs_bij:
  assumes x: "prod_is_node A B x"
  shows "(fst (prod_dfs A B x) ! i ! j = Some k \<and> dfa_is_node A i \<and> dfa_is_node B j) =
    (k < length (snd (prod_dfs A B x)) \<and> (snd (prod_dfs A B x) ! k = (i, j)))"
proof -
  from x have "list_all (prod_is_node A B) [x]" by simp
  with empt_invariant
  have "(fst (dfs (prod_empt A B) [x]) ! i ! j = Some k \<and> dfa_is_node A i \<and> dfa_is_node B j) =
    (k < length (snd (dfs (prod_empt A B) [x])) \<and> (snd (dfs (prod_empt A B) [x]) ! k = (i, j)))"
  proof (induct rule: dfs_invariant)
    case base
    show ?case
      by (auto simp add: prod_empt_def dfa_is_node_def)
  next
    case (step S y)
    obtain y1 y2 where y: "y = (y1, y2)" by (cases y)
    show ?case
    proof (cases "y1 = i")
      case True
      show ?thesis
      proof (cases "y2 = j")
        case True
        with step y \<open>y1 = i\<close> show ?thesis
          by (auto simp add: prod_ins_def prod_memb_def split_beta nth_append
            prod_invariant_def prod_is_node_def dfa_is_node_def)
      next
        case False
        with step y \<open>y1 = i\<close> show ?thesis
          by (auto simp add: prod_ins_def prod_memb_def split_beta nth_append
            prod_invariant_def prod_is_node_def dfa_is_node_def)
      qed
    next
      case False
      with step y show ?thesis
        by (auto simp add: prod_ins_def prod_memb_def split_beta nth_append)
    qed
  qed
  then show ?thesis by (simp add: prod_dfs_def)
qed

lemma prod_dfs_mono:
  assumes z: "prod_invariant A B z"
  and xs: "list_all (prod_is_node A B) xs"
  and H: "fst z ! i ! j = Some k"
  shows "fst (gen_dfs (prod_succs A B) prod_ins prod_memb z xs) ! i ! j = Some k"
  using z xs
  apply (rule dfs_invariant)
  apply (rule H)
  apply (simp add: prod_ins_def prod_memb_def split_paired_all prod_is_node_def prod_invariant_def)
  apply (case_tac "aa = i")
  apply (case_tac "ba = j")
  apply (simp add: dfa_is_node_def)+
  done
    
lemma prod_dfs_start:
  "\<lbrakk>dfa_is_node A i; dfa_is_node B j\<rbrakk> \<Longrightarrow> fst (prod_dfs A B (i, j)) ! i ! j = Some 0"
  apply (simp add: prod_dfs_def empt prod_is_node_def gen_dfs_simps)
  apply (rule prod_dfs_mono)
  apply (rule ins_invariant)
  apply (simp add: prod_is_node_def dfa_is_node_def)
  apply (rule empt_invariant)
  apply (rule empt)
  apply (simp add: prod_is_node_def)
  apply (rule succs_is_node)
  apply (simp add: prod_is_node_def)
  apply (simp add: prod_ins_def prod_empt_def dfa_is_node_def)
  done

lemma prod_dfs_inj:
  assumes x: "prod_is_node A B x" and i1: "dfa_is_node A i1" and i2: "dfa_is_node B i2"
  and j1: "dfa_is_node A j1" and j2: "dfa_is_node B j2"
  and i: "fst (prod_dfs A B x) ! i1 ! i2 = Some k"
  and j: "fst (prod_dfs A B x) ! j1 ! j2 = Some k"
  shows "(i1, i2) = (j1, j2)"
proof -
  from x i1 i2 i
  have "k < length (snd (prod_dfs A B x)) \<and> snd (prod_dfs A B x) ! k = (i1, i2)"
    by (simp add: prod_dfs_bij [symmetric])
  moreover from x j1 j2 j
  have "k < length (snd (prod_dfs A B x)) \<and> snd (prod_dfs A B x) ! k = (j1, j2)"
    by (simp add: prod_dfs_bij [symmetric])
  ultimately show ?thesis by simp
qed

lemma prod_dfs_statetrans:
  assumes bs: "length bs = n"
  and i: "dfa_is_node A i" and j: "dfa_is_node B j"
  and s1: "dfa_is_node A s1" and s2: "dfa_is_node B s2"
  and k: "fst (prod_dfs A B (s1, s2)) ! i ! j = Some k"
  obtains k'
  where "fst (prod_dfs A B (s1, s2)) !
    dfa_trans A i bs ! dfa_trans B j bs = Some k'"
  and "dfa_is_node A (dfa_trans A i bs)"
  and "dfa_is_node B (dfa_trans B j bs)"
  and "k' < length (snd (prod_dfs A B (s1, s2)))"
proof -
  from i well_formed1 bs have h_tr1: "bddh (length bs) (fst A ! i)" by (simp add: wf_dfa_def dfa_is_node_def list_all_iff)
  from j well_formed2 bs have h_tr2: "bddh (length bs) (fst B ! j)" by (simp add: wf_dfa_def dfa_is_node_def list_all_iff)
  from i j k have "prod_memb (i, j) (prod_dfs A B (s1, s2))"
    by (simp add: prod_memb_def split_beta)
  then have "((s1, s2), (i, j)) \<in> (succsr (prod_succs A B))\<^sup>*"
    using i j s1 s2
    by (simp add: prod_dfs_eq_rtrancl prod_is_node_def)
  moreover from h_tr1 h_tr2 have "(bdd_lookup (fst A ! i) bs, bdd_lookup (fst B ! j) bs) =
    bdd_lookup (bdd_binop Pair (fst A ! i) (fst B ! j)) bs"
    by (simp add: bdd_lookup_binop)
  with i j h_tr1 h_tr2
  have "((i, j), (bdd_lookup (fst A ! i) bs, bdd_lookup (fst B ! j) bs)) \<in>
    succsr (prod_succs A B)"
    by (auto simp add: succsr_def prod_succs_def
      add_leaves_bdd_lookup [of "length bs"] bddh_binop is_alph_def)
  ultimately have "((s1, s2), (bdd_lookup (fst A ! i) bs, bdd_lookup (fst B ! j) bs)) \<in>
    (succsr (prod_succs A B))\<^sup>*" ..
  moreover from well_formed1 well_formed2 bs i j
  have "prod_is_node A B (bdd_lookup (fst A ! i) bs, bdd_lookup (fst B ! j) bs)"
    by (auto simp: prod_is_node_def bdd_all_bdd_lookup is_alph_def dfa_trans_is_node dfa_trans_def[symmetric])
  moreover from i well_formed1 bs
  have s_tr1: "dfa_is_node A (dfa_trans A i bs)"
    by (simp add: is_alph_def dfa_trans_is_node)
  moreover from j well_formed2 bs
  have s_tr2: "dfa_is_node B (dfa_trans B j bs)"
    by (simp add: is_alph_def dfa_trans_is_node)
  ultimately have "\<exists>k'. fst (prod_dfs A B (s1, s2)) ! 
    dfa_trans A i bs ! dfa_trans B j bs = Some k'"
    using s1 s2
    by (simp add: prod_dfs_eq_rtrancl [symmetric] prod_memb_def split_beta prod_is_node_def dfa_trans_def)
  then obtain k' where k': "fst (prod_dfs A B (s1, s2)) ! 
    dfa_trans A i bs ! dfa_trans B j bs = Some k'" ..
  from k' s_tr1 s_tr2 s1 s2
  have "k' < length (snd (prod_dfs A B (s1, s2))) \<and>
    snd (prod_dfs A B (s1, s2)) ! k' = (dfa_trans A i bs, dfa_trans B j bs)"
    by (simp add: prod_dfs_bij [symmetric] prod_is_node_def)
  then have "k' < length (snd (prod_dfs A B (s1, s2)))" by simp
  with k' s_tr1 s_tr2 show ?thesis ..
qed

lemma binop_wf_dfa: "wf_dfa (binop_dfa f A B) n"
proof -
  let ?dfa = "binop_dfa f A B"
  from well_formed1 well_formed2 have is_node_s1_s2: "prod_is_node A B (0, 0)" by (simp add: prod_is_node_def wf_dfa_def dfa_is_node_def)
  let ?tr = "map (\<lambda>(i,j). bdd_binop (\<lambda>k l. the (fst (prod_dfs A B (0, 0)) ! k ! l)) (fst A ! i) (fst B ! j)) (snd (prod_dfs A B (0,0)))"
  {
    fix i j
    assume ij: "(i, j) \<in> set (snd (prod_dfs A B (0, 0)))"
    then obtain k where k: "k < length (snd (prod_dfs A B (0, 0)))"
      "snd (prod_dfs A B (0, 0)) ! k = (i, j)"
      by (auto simp add: in_set_conv_nth)
    from conjI [OF k] obtain ij_k: "fst (prod_dfs A B (0,0)) ! i ! j = Some k"
      and i: "dfa_is_node A i" and j: "dfa_is_node B j"
      by (simp add: prod_dfs_bij [OF is_node_s1_s2, symmetric])
    from well_formed1 i have bddh_tr1: "bddh n (fst A ! i)"
      and less_tr1: "bdd_all (dfa_is_node A) (fst A ! i)" by (simp add: wf_dfa_def list_all_iff dfa_is_node_def)+
    from well_formed2 j have bddh_tr2: "bddh n (fst B ! j)"
      and less_tr2: "bdd_all (dfa_is_node B) (fst B ! j)" by (simp add: wf_dfa_def list_all_iff dfa_is_node_def)+
    from bddh_tr1 bddh_tr2 have 1: "bddh n (bdd_binop (\<lambda>k l. the (fst (prod_dfs A B (0, 0)) ! k ! l)) (fst A ! i) (fst B ! j))"
      by (simp add: bddh_binop)
    have "\<forall>bs. length bs = n \<longrightarrow> the (fst (prod_dfs A B (0, 0)) ! dfa_trans A i bs ! dfa_trans B j bs)
      < length (snd (prod_dfs A B (0, 0)))"
    proof (intro strip)
      fix bs
      assume bs: "length (bs::bool list) = n"
      moreover note i j
      moreover from well_formed1 well_formed2 have "dfa_is_node A 0" and "dfa_is_node B 0"
        by (simp add: dfa_is_node_def wf_dfa_def)+
      moreover note ij_k
      ultimately obtain m where "fst (prod_dfs A B (0, 0)) ! dfa_trans A i bs ! dfa_trans B j bs = Some m"
        and "m < length (snd (prod_dfs A B (0, 0)))" by (rule prod_dfs_statetrans)
      then show "the (fst (prod_dfs A B (0,0)) ! dfa_trans A i bs ! dfa_trans B j bs) < length (snd (prod_dfs A B (0,0)))" by simp
    qed
    with bddh_tr1 bddh_tr2 have 2: "bdd_all (\<lambda>q. q < length (snd (prod_dfs A B (0, 0)))) (bdd_binop (\<lambda>k l. the (fst (prod_dfs A B (0,0)) ! k ! l)) (fst A ! i) (fst B ! j))"
      by (simp add: bddh_binop bdd_lookup_binop bdd_all_bdd_lookup_iff[of n _ "\<lambda>x. x < length (snd (prod_dfs A B (0,0)))"] dfa_trans_def)
    note this 1
  }
  hence 1: "list_all (bddh n) ?tr" and 2: "list_all (bdd_all (\<lambda>q. q < length ?tr)) ?tr" by (auto simp: split_paired_all list_all_iff)
  from well_formed1 well_formed2 have 3: "fst (prod_dfs A B (0, 0)) ! 0 ! 0 = Some 0" by (simp add: wf_dfa_def dfa_is_node_def prod_dfs_start)
  from is_node_s1_s2 have "(fst (prod_dfs A B (0,0)) ! 0 ! 0 = Some 0 \<and> dfa_is_node A 0 \<and> dfa_is_node B 0) =
    (0 < length (snd (prod_dfs A B (0,0))) \<and> snd (prod_dfs A B (0,0)) ! 0 = (0,0))" by (rule prod_dfs_bij)
  with 3 well_formed1 well_formed2 have "0 < length (snd (prod_dfs A B (0,0)))" by (simp add: wf_dfa_def dfa_is_node_def)
  with 1 2 3 show "wf_dfa (binop_dfa f A B) n" by (simp add: binop_dfa_def wf_dfa_def split_beta dfa_is_node_def)
qed

theorem binop_dfa_reachable:
  assumes bss: "list_all (is_alph n) bss"
  shows "(\<exists>m. dfa_reach (binop_dfa f A B) 0 bss m \<and>
    fst (prod_dfs A B (0, 0)) ! s\<^sub>1 ! s\<^sub>2 = Some m \<and>
    dfa_is_node A s\<^sub>1 \<and> dfa_is_node B s\<^sub>2) =
   (dfa_reach A 0 bss s\<^sub>1 \<and> dfa_reach B 0 bss s\<^sub>2)"
proof -
  let ?tr = "map (\<lambda>(i, j).
    bdd_binop (\<lambda>k l. the (fst (prod_dfs A B (0,0)) ! k ! l)) (fst A ! i) (fst B ! j))
      (snd (prod_dfs A B (0,0)))"
  have T: "?tr = fst (binop_dfa f A B)" by (simp add: binop_dfa_def split_beta)
  from well_formed1 well_formed2 have is_node_s1_s2: "prod_is_node A B (0, 0)" by (simp add: prod_is_node_def wf_dfa_def dfa_is_node_def)
  from well_formed1 well_formed2 have s1: "dfa_is_node A 0" and s2: "dfa_is_node B 0" by (simp add: dfa_is_node_def wf_dfa_def)+
  from s1 s2 have start: "fst (prod_dfs A B (0,0)) ! 0 ! 0 = Some 0"
    by (rule prod_dfs_start)
  show "(\<exists>m. dfa_reach (binop_dfa f A B) 0 bss m \<and>
     fst (prod_dfs A B (0, 0)) ! s\<^sub>1 ! s\<^sub>2 = Some m \<and>
     dfa_is_node A s\<^sub>1 \<and> dfa_is_node B s\<^sub>2) =
    (dfa_reach A 0 bss s\<^sub>1 \<and> dfa_reach B 0 bss s\<^sub>2)"
    (is "(\<exists>m. ?lhs1 m \<and> ?lhs2 m \<and> ?lhs3 \<and> ?lhs4) = ?rhs"
     is "?lhs = _")
  proof
    assume "\<exists>m. ?lhs1 m \<and> ?lhs2 m \<and> ?lhs3 \<and> ?lhs4"
    then obtain m where lhs: "?lhs1 m" "?lhs2 m" "?lhs3" "?lhs4" by auto
    from lhs bss show ?rhs
    proof (induct arbitrary: s\<^sub>1 s\<^sub>2)
      case Nil
      from is_node_s1_s2
        s1 s2 \<open>dfa_is_node A s\<^sub>1\<close> \<open>dfa_is_node B s\<^sub>2\<close>
      have "(0, 0) = (s\<^sub>1, s\<^sub>2)"
        using start \<open>fst (prod_dfs A B (0,0)) ! s\<^sub>1 ! s\<^sub>2 = Some 0\<close>
        by (rule prod_dfs_inj)
      moreover have "dfa_reach A 0 [] 0" by (rule reach_nil)
      moreover have "dfa_reach B 0 [] 0" by (rule reach_nil)
      ultimately show ?case by simp
    next
      case (snoc j bss bs s\<^sub>1 s\<^sub>2)
      then have "length bs = n" by (simp add: is_alph_def)
      moreover from binop_wf_dfa have "dfa_is_node (binop_dfa f A B) 0" by (simp add: dfa_is_node_def wf_dfa_def)
      with snoc binop_wf_dfa [of f] have "dfa_is_node (binop_dfa f A B) j" by (simp add: dfa_reach_is_node)
      then have j: "j < length (snd (prod_dfs A B (0,0)))" by (simp add: binop_dfa_def dfa_is_node_def split_beta)
      with prod_dfs_bij [OF is_node_s1_s2,
        of "fst (snd (prod_dfs A B (0,0)) ! j)" "snd (snd (prod_dfs A B (0,0)) ! j)"]
      have j_tr1: "dfa_is_node A (fst (snd (prod_dfs A B (0,0)) ! j))"
        and j_tr2: "dfa_is_node B (snd (snd (prod_dfs A B (0,0)) ! j))"
        and Some_j: "fst (prod_dfs A B (0,0)) ! fst (snd (prod_dfs A B (0,0)) ! j) ! snd (snd (prod_dfs A B (0,0)) ! j) = Some j"
        by auto
      note j_tr1 j_tr2 s1 s2 Some_j
      ultimately obtain k
        where k: "fst (prod_dfs A B (0,0)) ! 
          dfa_trans A (fst (snd (prod_dfs A B (0, 0)) ! j)) bs !
          dfa_trans B (snd (snd (prod_dfs A B (0, 0)) ! j)) bs = Some k"
        and s_tr1': "dfa_is_node A (dfa_trans A (fst (snd (prod_dfs A B (0,0)) ! j)) bs)"
        and s_tr2': "dfa_is_node B (dfa_trans B (snd (snd (prod_dfs A B (0,0)) ! j)) bs)"
        by (rule prod_dfs_statetrans)

      from well_formed1 well_formed2 j_tr1 j_tr2 snoc
      have lh: "bddh (length bs) (fst A ! fst (snd (prod_dfs A B (0,0)) ! j))"
        and rh: "bddh (length bs) (fst B ! snd (snd (prod_dfs A B (0,0)) ! j))"
        by (auto simp: wf_dfa_def dfa_is_node_def list_all_iff is_alph_def)
      from snoc(3)[unfolded dfa_trans_def binop_dfa_def Let_def split_beta fst_conv nth_map[OF j] bdd_lookup_binop[OF lh,OF rh], folded dfa_trans_def] k
      have "fst (prod_dfs A B (0,0)) ! s\<^sub>1 ! s\<^sub>2 = Some k" by simp
      with is_node_s1_s2 \<open>dfa_is_node A s\<^sub>1\<close> \<open>dfa_is_node B s\<^sub>2\<close> s_tr1' s_tr2'
      have "(s\<^sub>1, s\<^sub>2) = (dfa_trans A (fst (snd (prod_dfs A B (0,0)) ! j)) bs, dfa_trans B (snd (snd (prod_dfs A B (0,0)) ! j)) bs)"
        using k
        by (rule prod_dfs_inj)
      moreover from snoc Some_j j_tr1 j_tr2
      have "dfa_reach A 0 bss (fst (snd (prod_dfs A B (0,0)) ! j))" by simp
      hence "dfa_reach A 0 (bss @ [bs]) (dfa_trans A (fst (snd (prod_dfs A B (0,0)) ! j)) bs)"
        by (rule reach_snoc)
      moreover from snoc Some_j j_tr1 j_tr2
      have "dfa_reach B 0 bss (snd (snd (prod_dfs A B (0,0)) ! j))" by simp
      hence "dfa_reach B 0 (bss @ [bs]) (dfa_trans B (snd (snd (prod_dfs A B (0,0)) ! j)) bs)"
        by (rule reach_snoc)
      ultimately show "dfa_reach A 0 (bss @ [bs]) s\<^sub>1 \<and> dfa_reach B 0 (bss @ [bs]) s\<^sub>2"
        by simp
    qed
  next
    assume ?rhs
    hence reach: "dfa_reach A 0 bss s\<^sub>1" "dfa_reach B 0 bss s\<^sub>2" by simp_all
    then show ?lhs using bss
    proof (induct arbitrary: s\<^sub>2)
      case Nil
      with start s1 s2 show ?case
        by (auto intro: reach_nil simp: reach_nil_iff)
    next
      case (snoc j bss bs s\<^sub>2)
      from snoc(3)
      obtain s\<^sub>2' where reach_s2': "dfa_reach B 0 bss s\<^sub>2'" and s2': "s\<^sub>2 = dfa_trans B s\<^sub>2' bs"
        by (auto simp: reach_snoc_iff)
      from snoc(2) [OF reach_s2'] snoc(4)
      obtain m where reach_m: "dfa_reach (binop_dfa f A B) 0 bss m"
        and m: "fst (prod_dfs A B (0,0)) ! j ! s\<^sub>2' = Some m"
        and j: "dfa_is_node A j" and s2'': "dfa_is_node B s\<^sub>2'"
        by auto
      from snoc have "list_all (is_alph n) bss" by simp
      with binop_wf_dfa reach_m dfa_startnode_is_node[OF binop_wf_dfa]
      have m_less: "dfa_is_node (binop_dfa f A B) m"
        by (rule dfa_reach_is_node)
      from is_node_s1_s2 m j s2''
      have m': "(m < length (snd (prod_dfs A B (0,0))) \<and>
        snd (prod_dfs A B (0,0)) ! m = (j, s\<^sub>2'))"
        by (simp add: prod_dfs_bij [symmetric])
      with j s2'' have "dfa_is_node A (fst (snd (prod_dfs A B (0,0)) ! m))"
        "dfa_is_node B (snd (snd (prod_dfs A B (0,0)) ! m))"
        by simp_all
      with well_formed1 well_formed2 snoc
      have bddh: "bddh (length bs) (fst A ! fst (snd (prod_dfs A B (0,0)) ! m))"
        "bddh (length bs) (fst B ! snd (snd (prod_dfs A B (0,0)) ! m))"
        by (simp add: wf_dfa_def is_alph_def dfa_is_node_def list_all_iff)+
      from snoc have "length bs = n" by (simp add: is_alph_def)
      then obtain k where k: "fst (prod_dfs A B (0,0)) !
          dfa_trans A j bs ! dfa_trans B s\<^sub>2' bs = Some k"
        and s_tr1: "dfa_is_node A (dfa_trans A j bs)"
        and s_tr2: "dfa_is_node B (dfa_trans B s\<^sub>2' bs)"
        using j s2'' s1 s2 m
        by (rule prod_dfs_statetrans)
      show ?case
        apply (rule exI)
        apply (simp add: s2')
        apply (intro conjI)
        apply (rule reach_snoc)
        apply (rule reach_m)
        apply (cut_tac m_less)
        apply (simp add: dfa_trans_def binop_dfa_def split_beta dfa_is_node_def)
        apply (simp add: bddh bdd_lookup_binop split_beta)
        apply (simp add: dfa_trans_def[symmetric] m' k)
        apply (rule s_tr1)
        apply (rule s_tr2)
        done
    qed
  qed
qed

lemma binop_dfa_steps:
  assumes X: "list_all (is_alph n) bs"
  shows "snd (binop_dfa f A B) ! dfa_steps (binop_dfa f A B) 0 bs = f (snd A ! dfa_steps A 0 bs) (snd B ! dfa_steps B 0 bs)"
  (is "?as3 ! dfa_steps ?A 0 bs = ?rhs")
proof -
  note 2 = dfa_startnode_is_node[OF well_formed1]
  note 5 = dfa_startnode_is_node[OF well_formed2]
  note B = dfa_startnode_is_node[OF binop_wf_dfa]
  define tab where "tab = fst (prod_dfs A B (0,0))"
  define ps where "ps = snd (prod_dfs A B (0,0))"
  from tab_def ps_def have prod: "prod_dfs A B (0,0) = (tab, ps)" by simp
  define s1 where "s1 = dfa_steps A 0 bs"
  define s2 where "s2 = dfa_steps B 0 bs"
  with s1_def have "dfa_reach A 0 bs s1" and "dfa_reach B 0 bs s2" by (simp add: reach_def)+
  with X have "\<exists>m. dfa_reach ?A 0 bs m \<and> fst (prod_dfs A B (0, 0)) ! s1 ! s2 = Some m \<and> dfa_is_node A s1 \<and> dfa_is_node B s2"
    by (simp add: binop_dfa_reachable)
  with tab_def have "\<exists>m. dfa_reach ?A 0 bs m \<and> tab ! s1 ! s2 = Some m \<and> dfa_is_node A s1 \<and> dfa_is_node B s2" by simp
  then obtain m where R: "dfa_reach ?A 0 bs m" and M: "tab ! s1 ! s2 = Some m" and s1: "dfa_is_node A s1" and s2: "dfa_is_node B s2" by blast
  hence M': "m = dfa_steps ?A 0 bs" by (simp add: reach_def)
  from B X R binop_wf_dfa [of f] have mL: "dfa_is_node ?A m" by (simp add: dfa_reach_is_node)
  from 2 5 M s1 s2 have bij: "m < length (snd (prod_dfs A B (0, 0))) \<and> snd (prod_dfs A B (0, 0)) ! m = (s1, s2)" unfolding tab_def
    by (simp add: prod_dfs_bij[symmetric] prod_is_node_def)
  with mL have "snd (binop_dfa f A B) ! m = f (snd A ! s1) (snd B ! s2)"
    by (simp add: binop_dfa_def split_beta dfa_is_node_def)
  with M' s1_def s2_def 
  show "snd ?A ! dfa_steps ?A 0 bs = f (snd A ! dfa_steps A 0 bs) (snd B ! dfa_steps B 0 bs)"
    by simp
qed

end

lemma binop_wf_dfa:
  assumes A: "wf_dfa A n" and B: "wf_dfa B n"
  shows "wf_dfa (binop_dfa f A B) n"
proof -
  from A B
  interpret prod_DFS A B n by unfold_locales
  show ?thesis by (rule binop_wf_dfa)
qed

theorem binop_dfa_accepts:
  assumes A: "wf_dfa A n"
  and B: "wf_dfa B n"
  and X: "list_all (is_alph n) bss"
  shows "dfa_accepts (binop_dfa f A B) bss = f (dfa_accepts A bss) (dfa_accepts B bss)"
proof -
  from A B
  interpret prod_DFS A B n by unfold_locales
  from X show ?thesis
    by (simp add: accepts_def dfa_accepting_def binop_dfa_steps)
qed

definition
  and_dfa :: "dfa \<Rightarrow> dfa \<Rightarrow> dfa" where
  "and_dfa = binop_dfa (\<and>)"

lemma and_wf_dfa:
  assumes "wf_dfa M n"
  and "wf_dfa N n"
  shows "wf_dfa (and_dfa M N) n"
  using assms by (simp add: and_dfa_def binop_wf_dfa)

lemma and_dfa_accepts:
  assumes "wf_dfa M n"
  and "wf_dfa N n"
  and "list_all (is_alph n) bs"
  shows "dfa_accepts (and_dfa M N) bs = (dfa_accepts M bs \<and> dfa_accepts N bs)"
  using assms by (simp add: binop_dfa_accepts and_dfa_def)

definition
  or_dfa :: "dfa \<Rightarrow> dfa \<Rightarrow> dfa" where
  "or_dfa = binop_dfa (\<or>)"

lemma or_wf_dfa:
  assumes "wf_dfa M n" and "wf_dfa N n"
  shows "wf_dfa (or_dfa M N) n"
  using assms by (simp add: or_dfa_def binop_wf_dfa)

lemma or_dfa_accepts:
  assumes "wf_dfa M n" and "wf_dfa N n"
  and "list_all (is_alph n) bs"
  shows "dfa_accepts (or_dfa M N) bs = (dfa_accepts M bs \<or> dfa_accepts N bs)"
  using assms by (simp add: binop_dfa_accepts or_dfa_def)
    
definition
  imp_dfa :: "dfa \<Rightarrow> dfa \<Rightarrow> dfa" where
  "imp_dfa = binop_dfa (\<longrightarrow>)"

lemma imp_wf_dfa:
  assumes "wf_dfa M n" and "wf_dfa N n"
  shows "wf_dfa (imp_dfa M N) n"
  using assms by (simp add: binop_wf_dfa imp_dfa_def)

lemma imp_dfa_accepts:
  assumes "wf_dfa M n" and "wf_dfa N n"
  and "list_all (is_alph n) bs"
  shows "dfa_accepts (imp_dfa M N) bs = (dfa_accepts M bs \<longrightarrow> dfa_accepts N bs)"
  using assms by (auto simp add: binop_dfa_accepts imp_dfa_def)


subsection \<open>Transforming DFAs to NFAs\<close>

definition
  nfa_of_dfa :: "dfa \<Rightarrow> nfa" where
  "nfa_of_dfa = (\<lambda>(bdd,as). (map (bdd_map (\<lambda>q. (replicate (length bdd) False)[q:=True])) bdd, as))"

lemma dfa2wf_nfa:
  assumes "wf_dfa M n"
  shows "wf_nfa (nfa_of_dfa M) n"
proof -
  have "\<And>a. dfa_is_node M a \<Longrightarrow> nfa_is_node (nfa_of_dfa M) ((replicate (length (fst M)) False)[a:=True])"
    by (simp add: dfa_is_node_def nfa_is_node_def nfa_of_dfa_def split_beta)
  hence "\<And>bdd. bdd_all (dfa_is_node M) bdd \<Longrightarrow> bdd_all (nfa_is_node (nfa_of_dfa M)) (bdd_map (\<lambda>q. (replicate (length (fst M)) False)[q:=True]) bdd)"
    by (simp add: bdd_all_bdd_map)
  with assms have "list_all (bdd_all (nfa_is_node (nfa_of_dfa M))) (fst (nfa_of_dfa M))" by (simp add: list_all_iff split_beta nfa_of_dfa_def wf_dfa_def)
  with assms show ?thesis by (simp add: wf_nfa_def wf_dfa_def nfa_of_dfa_def split_beta list_all_iff bddh_bdd_map)
qed

lemma replicate_upd_inj: "\<lbrakk>q < n; (replicate n False)[q:=True] = (replicate n False)[p:=True]\<rbrakk> \<Longrightarrow> (q = p)" (is "\<lbrakk>_ ;?lhs = ?rhs\<rbrakk> \<Longrightarrow>  _")
proof -
  assume q: "q < n" and r: "?lhs = ?rhs"
  { assume "p \<noteq> q"
    with q have "?lhs ! q = True" by simp
    moreover from \<open>p \<noteq> q\<close> q have "?rhs ! q = False" by simp
    ultimately have "?lhs \<noteq> ?rhs" by auto
  }
  with r show "q = p" by auto
qed

lemma nfa_of_dfa_reach':
  assumes V: "wf_dfa M l"
  and X: "list_all (is_alph l) bss"
  and N: "n1 = (replicate (length (fst M)) False)[q:=True]"
  and Q: "dfa_is_node M q"
  and R: "nfa_reach (nfa_of_dfa M) n1 bss n2"
  shows "\<exists>p. dfa_reach M q bss p \<and> n2 = (replicate (length (fst M)) False)[p:=True]"
proof -
  from R V X N Q show ?thesis proof induct
    case Nil
    hence "dfa_reach M q [] q" by (simp add: reach_nil)
    with Nil show ?case by auto
  next
    case (snoc j bss bs)
    hence N1: "nfa_is_node (nfa_of_dfa M) n1" by (simp add: nfa_is_node_def nfa_of_dfa_def split_beta)
    from snoc have V2: "wf_nfa (nfa_of_dfa M) l" by (simp add: dfa2wf_nfa)
    from snoc have "\<exists>p. dfa_reach M q bss p \<and> j = (replicate (length (fst M)) False)[p := True]" by simp
    then obtain p where PR: "dfa_reach M q bss p" and J: "j = (replicate (length (fst M)) False)[p:=True]" by blast
    hence JL: "nfa_is_node (nfa_of_dfa M) j" by (simp add: nfa_is_node_def nfa_of_dfa_def split_beta)
    from snoc PR have PL: "dfa_is_node M p" by (simp add: dfa_reach_is_node)
    with snoc JL have PL': "p < length j" by (simp add: nfa_is_node_def dfa_is_node_def nfa_of_dfa_def split_beta)
    define m where "m = dfa_trans M p bs"
    with snoc PR have MR: "dfa_reach M q (bss @ [bs]) m" by (simp add: reach_snoc)
    with snoc have mL: "dfa_is_node M m" by (simp add: dfa_reach_is_node)
    from V2 JL snoc have "nfa_is_node (nfa_of_dfa M) (nfa_trans (nfa_of_dfa M) j bs)" by (simp add: nfa_trans_is_node)
    hence L: "length (nfa_trans (nfa_of_dfa M) j bs) = length (fst M)" by (simp add: nfa_is_node_def nfa_of_dfa_def split_beta)

    have "nfa_trans (nfa_of_dfa M) j bs = (replicate (length (fst M)) False)[m := True]" (is "?lhs = ?rhs")
    proof (simp add: list_eq_iff_nth_eq L, intro strip)
      fix i assume H: "i < length (fst M)"
      show "nfa_trans (nfa_of_dfa M) j bs ! i = (replicate (length (fst M)) False)[m := True] ! i" (is "?lhs = ?rhs")
      proof
        assume lhs: "?lhs"
        from V2 snoc have "wf_nfa (nfa_of_dfa M) (length bs)" by (simp add: is_alph_def) moreover
        note JL moreover
        from H have IL: "i < length (fst (nfa_of_dfa M))" by (simp add: nfa_of_dfa_def split_beta) moreover
        from \<open>?lhs\<close> have "bdd_lookup (subsetbdd (fst (nfa_of_dfa M)) j (nfa_emptybdd (length j))) bs ! i" by (simp add: nfa_trans_def) 
        ultimately have "\<exists>x < length j. j ! x \<and> bdd_lookup (fst (nfa_of_dfa M) ! x) bs ! i" by (simp add: bdd_lookup_subsetbdd)
        then obtain x where xl: "x < length j" and xj: "j ! x" and xs: "bdd_lookup (fst (nfa_of_dfa M) ! x) bs ! i" by blast
        with snoc J PL' have "x = p" by (cases "p = x") simp+
        with xs PL snoc(3,4) m_def show "(replicate (length (fst M)) False)[m := True] ! i"
          by (simp add: nfa_of_dfa_def split_beta dfa_trans_def dfa_is_node_def wf_dfa_def is_alph_def bdd_map_bdd_lookup list_all_iff)
      next
        assume rhs: "?rhs"
        with H mL have "m = i" by (cases "m = i") (simp add: dfa_is_node_def)+
        from PL snoc(3,4) m_def \<open>m = i\<close> H have "bdd_lookup (fst (nfa_of_dfa M) ! p) bs ! i"
          by (simp add: nfa_of_dfa_def split_beta dfa_is_node_def wf_dfa_def is_alph_def list_all_iff bdd_map_bdd_lookup dfa_trans_def)
        with PL' J have E: "\<exists>p < length j. j ! p \<and> bdd_lookup( fst (nfa_of_dfa M) ! p) bs ! i" by auto
        from snoc(4) V2 have V': "wf_nfa (nfa_of_dfa M) (length bs)" by (simp add: is_alph_def)
        from H have H': "i < length (fst (nfa_of_dfa M))" by (simp add: nfa_of_dfa_def split_beta)
        from H' V' E JL have "bdd_lookup (subsetbdd (fst (nfa_of_dfa M)) j (nfa_emptybdd (length j))) bs ! i" by (simp add: bdd_lookup_subsetbdd)
        thus "?lhs" by (simp add: nfa_trans_def)
      qed
    qed
    with MR show ?case by auto
  qed
qed


lemma nfa_of_dfa_reach:
  assumes V: "wf_dfa M l"
  and X: "list_all (is_alph l) bss"
  and N1: "n1 = (replicate (length (fst M)) False)[q:=True]"
  and N2: "n2 = (replicate (length (fst M)) False)[p:=True]"
  and Q: "dfa_is_node M q"
  shows "nfa_reach (nfa_of_dfa M) n1 bss n2 = dfa_reach M q bss p"
proof
  assume "nfa_reach (nfa_of_dfa M) n1 bss n2"
  with assms have "\<exists>p. dfa_reach M q bss p \<and> n2 = (replicate (length (fst M)) False)[p := True]" by (simp add: nfa_of_dfa_reach')
  then obtain p' where R: "dfa_reach M q bss p'" and N2': "n2 = (replicate (length (fst M)) False)[p' := True]" by blast
  from V R Q X have "dfa_is_node M p'" by (simp add: dfa_reach_is_node)
  with N2 N2' have "p' = p" by (simp add: dfa_is_node_def replicate_upd_inj)
  with R show "dfa_reach M q bss p" by simp
next
  assume H: "dfa_reach M q bss p"
  define n2' where "n2' = nfa_steps (nfa_of_dfa M) n1 bss"
  hence R': "nfa_reach (nfa_of_dfa M) n1 bss n2'" by (simp add: reach_def)
  with assms have "\<exists>p. dfa_reach M q bss p \<and> n2' = (replicate (length (fst M)) False)[p := True]" by (simp add: nfa_of_dfa_reach')
  then obtain p' where R: "dfa_reach M q bss p'" and N2': "n2' = (replicate (length (fst M)) False)[p' := True]" by blast
  with H have "p = p'" by (simp add: reach_inj)
  with N2' N2 have "n2 = n2'" by simp
  with R' show "nfa_reach (nfa_of_dfa M) n1 bss n2" by simp
qed

lemma nfa_accepting_replicate:
  assumes "q < length (fst N)"
  and "length (snd N) = length (fst N)"
  shows "nfa_accepting N ((replicate (length (fst N)) False)[q:=True]) = snd N ! q"
proof -
  from assms have "set_of_bv ((replicate (length (fst N)) False)[q:=True]) = {q}"
  proof (auto simp: set_of_bv_def)
    fix x assume "x < length (fst N)" and "(replicate (length (fst N)) False)[q := True] ! x"
    with assms show "x = q" by (cases "x = q") simp+
  qed
  hence "nfa_accepting N ((replicate (length (fst N)) False)[q:=True]) = (set_of_bv (snd N) \<inter> {q} \<noteq> {})"
    by (simp add: nfa_accepting_set_of_bv)
  also have "\<dots> = (q \<in> set_of_bv (snd N))" by auto
  also from assms have "\<dots> = snd N ! q" by (auto simp: set_of_bv_def)
  finally show ?thesis .
qed

lemma nfa_of_dfa_accepts:
  assumes V: "wf_dfa A n"
  and X: "list_all (is_alph n) bss"
  shows "nfa_accepts (nfa_of_dfa A) bss = dfa_accepts A bss"
proof -
  from V have Q: "dfa_is_node A 0" by (simp add: dfa_startnode_is_node)
  have S: "nfa_startnode (nfa_of_dfa A) = (replicate (length (fst A)) False)[0:= True]" by (simp add: nfa_startnode_def nfa_of_dfa_def split_beta)
  define p where "p = dfa_steps A 0 bss"
  define n2 where "n2 = (replicate (length (fst A)) False)[p := True]"
  from p_def have PR: "dfa_reach A 0 bss p" by (simp add: reach_def)
  with p_def n2_def Q S X V have "nfa_reach (nfa_of_dfa A) (nfa_startnode (nfa_of_dfa A)) bss n2" by (simp add: nfa_of_dfa_reach)
  hence N2: "n2 = nfa_steps (nfa_of_dfa A) (nfa_startnode (nfa_of_dfa A)) bss" by (simp add: reach_def)
  from PR Q X V have "dfa_is_node A p" by (simp add: dfa_reach_is_node)
  hence "p < length (fst (nfa_of_dfa A))" by (simp add: dfa_is_node_def nfa_of_dfa_def split_beta) moreover
  from dfa2wf_nfa[OF V] have "length (snd (nfa_of_dfa A)) = length (fst (nfa_of_dfa A))" by (auto simp add: wf_nfa_def) moreover
  from n2_def have "n2 = (replicate (length (fst (nfa_of_dfa A))) False)[p := True]" by (simp add: nfa_of_dfa_def split_beta)
  ultimately have "nfa_accepting (nfa_of_dfa A) n2 = snd (nfa_of_dfa A) ! p" by (simp add: nfa_accepting_replicate)
  with N2 p_def show ?thesis by (simp add: accepts_def accepts_def dfa_accepting_def nfa_of_dfa_def split_beta)
qed


subsection \<open>Transforming NFAs to DFAs\<close>

fun
  bddinsert :: "'a bdd \<Rightarrow> bool list \<Rightarrow> 'a \<Rightarrow> 'a bdd"
where
  "bddinsert (Leaf a) [] x = Leaf x" 
| "bddinsert (Leaf a) (w#ws) x = (if w then Branch (Leaf a) (bddinsert (Leaf a) ws x) else Branch (bddinsert (Leaf a) ws x) (Leaf a))"
| "bddinsert (Branch l r) (w#ws) x = (if w then Branch l (bddinsert r ws x) else Branch (bddinsert l ws x) r)"

lemma bddh_bddinsert:
  assumes "bddh x b"
  and "length w \<ge> x"
  shows "bddh (length w) (bddinsert b w y)"
using assms proof (induct b w y arbitrary: x rule: bddinsert.induct)
  case (2 aa ww wss yy xaa) 
  have "bddh 0 (Leaf aa) \<and> 0 \<le> length wss" by simp
  with 2(1) 2(2) have "bddh (length wss) (bddinsert (Leaf aa) wss yy)" by (cases ww) blast+
  with 2 show ?case by simp
next
  case (3 ll rr ww wss yy xx)
  from 3(3) obtain y where Y: "Suc y = xx" by (cases xx) simp+
  with 3 have 1: "bddh y rr \<and> bddh y ll \<and> y \<le> length wss" by auto
  show ?case proof (cases ww)
    case True
    with 1 3(1) have IV: "bddh (length wss) (bddinsert rr wss yy)" by blast
    with Y 3 have "y \<le> length wss" and "bddh y ll" by auto
    hence "bddh (length wss) ll" by (rule bddh_ge)
    with IV True show ?thesis by simp
  next
    case False
    with 1 3(2) have IV: "bddh (length wss) (bddinsert ll wss yy)" by blast
    with Y 3 have "y \<le> length wss" and "bddh y rr" by auto
    hence "bddh (length wss) rr" by (rule bddh_ge)
    with IV False show ?thesis by simp
  qed
qed simp+

lemma bdd_lookup_bddinsert:
  assumes "bddh (length w) bd"
  and "length w = length v"
  shows "bdd_lookup (bddinsert bd w y) v = (if w = v then y else bdd_lookup bd v)"
using assms proof (induct bd w y arbitrary: v rule: bddinsert.induct)
  case (2 aa ww wss xx vv)
  hence "\<exists>v vs. vv = v # vs" by (cases vv) simp+
  then obtain v vs where V: "vv = v # vs" by blast
  with 2 have "length wss = length vs" by simp
  with 2 have IV: "bdd_lookup (bddinsert (Leaf aa) wss xx) vs = (if wss = vs then xx else bdd_lookup (Leaf aa) vs)" by (cases ww) simp+
  have "bdd_lookup (bddinsert (Leaf aa) (ww # wss) xx) vv = bdd_lookup (if ww then (Branch (Leaf aa) (bddinsert (Leaf aa) wss xx)) else Branch (bddinsert (Leaf aa) wss xx) (Leaf aa)) vv" by simp 
  also have "\<dots> = (if ww then bdd_lookup (Branch (Leaf aa) (bddinsert (Leaf aa) wss xx)) vv else bdd_lookup (Branch (bddinsert (Leaf aa) wss xx) (Leaf aa)) vv)" by simp
  also from V IV have "\<dots> = (if ww # wss = v # vs then bdd_lookup (bddinsert (Leaf aa) wss xx) vs else bdd_lookup (Leaf aa) vs)" by (cases ww) auto
  also from V IV have "\<dots> = (if ww # wss = vv then xx else bdd_lookup (Leaf aa) vs)" by auto
  finally show ?case by simp
next
  case (3 ll rr ww wss xx vv)
  hence "\<exists>v vs. vv = v # vs" by (cases vv) simp+
  then obtain v vs where V: "vv = v # vs" by blast
  show ?case proof (cases ww)
    case True
    with 3 V have IV: "bdd_lookup (bddinsert rr wss xx) vs = (if wss = vs then xx else bdd_lookup rr vs)" by simp
    with True 3 V show ?thesis by auto
  next
    case False
    with 3 V have IV: "bdd_lookup (bddinsert ll wss xx) vs = (if wss = vs then xx else bdd_lookup ll vs)" by simp
    with False 3 V show ?thesis by auto
  qed
qed simp+

definition
  subset_succs :: "nfa \<Rightarrow> bool list \<Rightarrow> bool list list" where
  "subset_succs A qs = add_leaves (subsetbdd (fst A) qs (nfa_emptybdd (length qs))) []"

definition
  subset_invariant :: "nfa \<Rightarrow> nat option bdd \<times> bool list list \<Rightarrow> bool" where
  "subset_invariant A = (\<lambda>(bdd, qss). bddh (length (fst A)) bdd)"

definition
  "subset_ins qs = (\<lambda>(bdd, qss). (bddinsert bdd qs (Some (length qss)), qss @ [qs]))"

definition
  subset_memb :: "bool list \<Rightarrow> nat option bdd \<times> bool list list \<Rightarrow> bool" where
  "subset_memb qs = (\<lambda>(bdd, qss). bdd_lookup bdd qs \<noteq> None)"

definition
  subset_empt :: "nat option bdd \<times> bool list list" where
  "subset_empt = (Leaf None, [])"

definition
  subset_dfs :: "nfa \<Rightarrow> bool list \<Rightarrow> nat option bdd \<times> bool list list" where
  "subset_dfs A x = gen_dfs (subset_succs A) subset_ins subset_memb subset_empt [x]"

definition
  det_nfa :: "nfa \<Rightarrow> dfa" where
  "det_nfa A = (let (bdd, qss) = subset_dfs A (nfa_startnode A) in
             (map (\<lambda>qs. bdd_map (\<lambda>qs. the (bdd_lookup bdd qs)) (subsetbdd (fst A) qs (nfa_emptybdd (length qs)))) qss,
              map (\<lambda>qs. nfa_accepting A qs) qss))"

locale subset_DFS =
  fixes A n
  assumes well_formed: "wf_nfa A n"

lemma finite_list: "finite {xs::('a::finite) list. length xs = k}"
  apply (induct k)
  apply simp
  apply (subgoal_tac "{xs::('a::finite) list. length xs = Suc k} = (\<Union>x. Cons x ` {xs. length xs = k})")
  apply auto
  apply (case_tac x)
  apply auto
  done

sublocale subset_DFS < DFS "subset_succs A" "nfa_is_node A" "subset_invariant A" subset_ins subset_memb subset_empt
  apply (unfold_locales)
  apply (simp add: nfa_is_node_def subset_invariant_def subset_memb_def subset_ins_def bdd_lookup_bddinsert split_beta)
  apply (simp add: nfa_is_node_def subset_memb_def subset_empt_def)

  apply (insert well_formed)[]
  apply (simp add: subset_succs_def add_leaves_bdd_all_eq bdd_all_is_node_subsetbdd wf_nfa_def)

  apply (simp add: subset_invariant_def subset_empt_def)

  apply (simp add: nfa_is_node_def subset_invariant_def subset_memb_def subset_ins_def split_paired_all)
  apply (subgoal_tac "length (fst A) = length x")
  apply (auto simp: bddh_bddinsert)

  apply (simp add: nfa_is_node_def)
  apply (rule finite_list)
  done

context subset_DFS
begin

lemmas dfs_eq_rtrancl[folded subset_dfs_def] = dfs_eq_rtrancl

lemma  subset_dfs_bij:
  assumes H1: "nfa_is_node A q"
  and H2: "nfa_is_node A q0"
  shows "(bdd_lookup (fst (subset_dfs A q0)) q = Some v) = (v < length (snd (subset_dfs A q0)) \<and> (snd (subset_dfs A q0)) ! v = q)"
proof -
  from assms have "list_all (nfa_is_node A) [q0]" by simp
  with empt_invariant show ?thesis using H1 unfolding subset_dfs_def
  proof (induct arbitrary: v q rule: dfs_invariant)
    case (step S x vv qq)
    obtain bd1 l1 where S: "S = (bd1, l1)" by (cases S) blast+
    { assume "x \<in> set l1"
      hence "list_ex (\<lambda>l. l = x) l1" by (simp add: list_ex_iff)
      hence "\<exists>i < length l1. l1 ! i = x" by (simp add: list_ex_length)
      then obtain i where "i < length l1 \<and> l1 ! i = x" by blast
      with step S have "bdd_lookup bd1 x = Some i" by (simp add: nfa_is_node_def)
      with step S have "False" by (simp add: subset_memb_def) }
    hence X: "\<forall>i < length l1. l1 ! i \<noteq> x" by auto
    obtain bd2 l2 where S2: "subset_ins x S = (bd2, l2)" by (cases "subset_ins x S") blast+
    with S have SS: "bd2 = bddinsert bd1 x (Some (length l1))" "l2 = l1 @ [x]" by (simp add: subset_ins_def)+
    from step S H1 have "bdd_lookup (bddinsert bd1 x (Some (length l1))) qq = (if x = qq then Some (length l1) else bdd_lookup bd1 qq)"
      by (simp add: bdd_lookup_bddinsert subset_invariant_def nfa_is_node_def)
    with SS have "(bdd_lookup bd2 qq = Some vv) = (if x = qq then length l1 = vv else bdd_lookup bd1 qq = Some vv)" by simp
    also have "\<dots> = (x = qq \<and> length l1 = vv \<or> x \<noteq> qq \<and> bdd_lookup bd1 qq = Some vv)" by auto
    also have "\<dots> = (vv < length l2 \<and> l2 ! vv = qq)" proof (cases "x = qq")
      case True
      hence "(x = qq \<and> length l1 = vv \<or> x \<noteq> qq \<and> bdd_lookup bd1 qq = Some vv) = (x = qq \<and> length l1 = vv)" by simp
      also have "\<dots> = (vv < length l2 \<and> l2 ! vv = qq)" proof
        assume H: "vv < length l2 \<and> l2 ! vv = qq"
        show "x = qq \<and> length l1 = vv" proof (cases "vv = length l1")
          case False
          with H SS have "vv < length l1" by simp
          with SS have "l2 ! vv = l1 ! vv" by (simp add: nth_append)
          with False H SS \<open>x = qq\<close> have "vv < length l1 \<and> l1 ! vv = x" by auto
          with X show ?thesis by auto
        qed (simp add: True)
      qed (auto simp: SS)
      finally show ?thesis .
    next
      case False
      hence "(x = qq \<and> length l1 = vv \<or> x \<noteq> qq \<and> bdd_lookup bd1 qq = Some vv) = (x \<noteq> qq \<and> bdd_lookup bd1 qq = Some vv)" by simp
      also from step(4,5) S \<open>x\<noteq>qq\<close> have "\<dots> = (vv < length l1 \<and> l1 ! vv = qq)" by simp
      also from SS \<open>x\<noteq>qq\<close> have "\<dots> = (vv < length l2 \<and> l2 ! vv = qq)" by (simp add: nth_append)
      finally  show ?thesis .
    qed
    finally show ?case by (simp add: S2)
  qed (simp add: subset_empt_def)
qed

lemma subset_dfs_start:
  assumes H: "nfa_is_node A q0"
  shows "bdd_lookup (fst (subset_dfs A q0)) q0 = Some 0"
proof -
  obtain bd l where S: "subset_ins q0 subset_empt = (bd, l)" by (cases "subset_ins q0 subset_empt") blast+
  from H have "\<not> subset_memb q0 subset_empt" by (simp add: empt)
  with H empt_invariant have I: "subset_invariant A (subset_ins q0 subset_empt)"
    by (simp add: ins_invariant)
  from H have "list_all (nfa_is_node A) (subset_succs A q0)" by (simp add: succs_is_node)
  with I have "bdd_lookup (fst (gen_dfs (subset_succs A) subset_ins subset_memb (subset_ins q0 subset_empt) (subset_succs A q0))) q0 = Some 0"
  proof (induct rule: dfs_invariant)
    case base thus ?case unfolding subset_ins_def subset_empt_def by (induct q0) simp+
  next
    case (step S x)
    hence Q: "subset_memb q0 S" by (simp add: subset_memb_def split_beta)
    with step have "q0 \<noteq> x" by auto
    from step have I: "bddh (length (fst A)) (fst S)" by (simp add: subset_invariant_def split_beta)
    with H step \<open>q0\<noteq>x\<close> have V: "\<And>v. bdd_lookup (bddinsert (fst S) x v) q0 = bdd_lookup (fst S) q0" by (simp add: bdd_lookup_bddinsert nfa_is_node_def)
    with step show "bdd_lookup (fst (subset_ins x S)) q0 = Some 0" by (auto simp: subset_ins_def split_beta)
  qed
  thus ?thesis unfolding subset_dfs_def by (auto simp: nfa_is_node_def gen_dfs_simps subset_memb_def subset_empt_def)
qed

lemma subset_dfs_is_node:
  assumes "nfa_is_node A q0"
  shows "list_all (nfa_is_node A) (snd (subset_dfs A q0))"
proof -
  from assms have "list_all (nfa_is_node A) [q0]" by simp
  with empt_invariant show ?thesis unfolding subset_dfs_def
  proof (induct rule: dfs_invariant)
    case base thus ?case by (simp add: subset_empt_def)
  next
    case (step S x) thus ?case by (simp add: subset_ins_def split_beta)
  qed
qed

lemma det_wf_nfa:
  shows "wf_dfa (det_nfa A) n"
proof -
  obtain bt ls where BT: "subset_dfs A (nfa_startnode A) = (bt, ls)" by (cases "subset_dfs A (nfa_startnode A)") auto
  note Q = nfa_startnode_is_node[OF well_formed]
  from Q have N:"list_all (nfa_is_node A) (snd (subset_dfs A (nfa_startnode A)))" 
    by (simp add: subset_dfs_is_node)
  with BT have L: "list_all (nfa_is_node A) ls" by simp
  have D: "det_nfa A = (map (\<lambda>q. bdd_map (\<lambda>q. the (bdd_lookup bt q)) (subsetbdd (fst A) q (nfa_emptybdd (length q)))) ls, map (\<lambda>q. nfa_accepting A q) ls)"
    (is "_ = (?bdt, ?atbl)") unfolding det_nfa_def by (simp add: BT)
  from well_formed L have "list_all (\<lambda>q. bddh n (subsetbdd (fst A) q (nfa_emptybdd (length q)))) ls"
    by (induct ls) (simp add: bddh_subsetbdd wf_nfa_def nfa_emptybdd_def)+
  hence "list_all (\<lambda>q. bddh n (bdd_map (\<lambda>q. the (bdd_lookup bt q)) (subsetbdd (fst A) q (nfa_emptybdd (length q))))) ls"
    by (simp add: bddh_bdd_map)
  hence A: "list_all (bddh n) ?bdt" by (simp add: list_all_iff)
  {
    fix q assume "\<exists>i < length ls. ls ! i = q"
    then obtain i where len_i: "i < length ls" and i: "q = ls ! i" by blast
    from len_i i L have Q': "nfa_is_node A q" by (simp add: list_all_iff) 
    then have "(bdd_lookup (fst (subset_dfs A (nfa_startnode A))) q = Some i) =
      (i < length (snd (subset_dfs A (nfa_startnode A))) \<and> snd (subset_dfs A (nfa_startnode A)) ! i = q)"
      using Q
      by (rule subset_dfs_bij)
    with BT len_i i have "bdd_lookup bt q = Some i" by simp
    with BT have "subset_memb q (subset_dfs A (nfa_startnode A))" by (simp add: subset_memb_def)
    with Q' Q have TR: "(nfa_startnode A,q) \<in> (succsr (subset_succs A))\<^sup>*"
      by (simp add: dfs_eq_rtrancl)
    {
      fix p assume P: "p \<in> set (subset_succs A q)"
      with TR have 3: "(nfa_startnode A,p) \<in> (succsr (subset_succs A))\<^sup>*" by (simp add: succsr_def rtrancl_into_rtrancl)
      from Q' have "list_all (nfa_is_node A) (subset_succs A q)"
        by (rule succs_is_node)
      with P have 4: "nfa_is_node A p" by (simp add: list_all_iff)
      with Q 3 have "subset_memb p (subset_dfs A (nfa_startnode A))"
        by (simp add: dfs_eq_rtrancl)
      with BT have "bdd_lookup bt p \<noteq> None" by (simp add: subset_memb_def)
      with BT obtain j where j: "bdd_lookup (fst (subset_dfs A (nfa_startnode A))) p = Some j" by (cases "bdd_lookup bt p") simp+
      from 4 Q j have "j < length (snd (subset_dfs A (nfa_startnode A))) \<and> (snd (subset_dfs A (nfa_startnode A))) ! j = p"
        by (auto simp add: subset_dfs_bij)
      with j BT 4 have "\<exists>j. bdd_lookup bt p = Some j \<and> j < length ls" by auto
    }
    hence "\<forall>p \<in> set (subset_succs A q). \<exists>j. bdd_lookup bt p = Some j \<and> j < length ls" by auto
    hence "list_all (\<lambda>p. \<exists>j. bdd_lookup bt p = Some j \<and> j < length ls) (add_leaves (subsetbdd (fst A) q (nfa_emptybdd (length q))) [])" by (simp add: list_all_iff subset_succs_def)
    hence "bdd_all (\<lambda>p. \<exists>j. bdd_lookup bt p = Some j \<and> j < length ls) (subsetbdd (fst A) q (nfa_emptybdd (length q)))" by (simp add: add_leaves_bdd_all_eq)
    hence "bdd_all (\<lambda>l. l < length ls) (bdd_map (\<lambda>q. the (bdd_lookup bt q)) (subsetbdd (fst A) q (nfa_emptybdd (length q))))"
      by (induct ("subsetbdd (fst A) q (nfa_emptybdd (length q))")) auto
  }
  then have "\<forall>x \<in> set ls. bdd_all (\<lambda>l. l < length ls) (bdd_map (\<lambda>q. the (bdd_lookup bt q)) (subsetbdd (fst A) x (nfa_emptybdd (length x))))" by (simp add: in_set_conv_nth)
  hence "list_all (\<lambda>x. bdd_all (\<lambda>l. l < length ls) (bdd_map (\<lambda>q. the (bdd_lookup bt q)) (subsetbdd (fst A) x (nfa_emptybdd (length x))))) ls" by (simp add: list_all_iff)
  hence B: "list_all (bdd_all (\<lambda>l. l < length ls)) (map (\<lambda>x. bdd_map (\<lambda>q. the (bdd_lookup bt q)) (subsetbdd (fst A) x (nfa_emptybdd (length x)))) ls)" by (simp add: list_all_iff)
  from well_formed have "bdd_lookup (fst (subset_dfs A (nfa_startnode A))) (nfa_startnode A) = Some 0"
    by (simp add: subset_dfs_start nfa_startnode_is_node)
  with well_formed have "0 < length (snd (subset_dfs A (nfa_startnode A)))"
    by (simp add: subset_dfs_bij nfa_startnode_is_node)
  with A B D BT show ?thesis by (simp add: wf_dfa_def det_nfa_def dfa_is_node_def)
qed

lemma nfa_reach_rtrancl:
  assumes "nfa_is_node A i"
  shows "(\<exists>bss. nfa_reach A i bss j \<and> list_all (is_alph n) bss) = ((i, j) \<in> (succsr (subset_succs A))\<^sup>*)"
proof
  assume "\<exists>bss. nfa_reach A i bss j \<and> list_all (is_alph n) bss"
  then obtain bss where BS: "nfa_reach A i bss j" "list_all (is_alph n) bss" by blast
  show "(i,j) \<in> (succsr (subset_succs A))\<^sup>*"
  proof -
    from BS show "(i,j) \<in> (succsr (subset_succs A))\<^sup>*" proof induct
      case (snoc j bss bs)
      with assms well_formed have J: "nfa_is_node A j" by (simp add: nfa_reach_is_node)
      with snoc well_formed have "bddh n (subsetbdd (fst A) j (nfa_emptybdd (length j)))"
        by (simp add: wf_nfa_def bddh_subsetbdd nfa_emptybdd_def)
      with snoc(3) have "bdd_lookup (subsetbdd (fst A) j (nfa_emptybdd (length j))) bs \<in> set (add_leaves (subsetbdd (fst A) j (nfa_emptybdd (length j))) [])"
        by (auto simp: add_leaves_bdd_lookup)
      hence "(j, bdd_lookup (subsetbdd (fst A) j (nfa_emptybdd (length j))) bs) \<in> (succsr (subset_succs A))\<^sup>*"
        by (auto simp:  succsr_def subset_succs_def)
      with snoc show ?case by (simp add: nfa_trans_def)
    qed simp
  qed 
next
  assume ij: "(i,j) \<in> (succsr (subset_succs A))\<^sup>*"
  from ij show "\<exists>bss. nfa_reach A i bss j \<and> list_all (is_alph n) bss"
  proof induct
    case base
    from reach_nil[of "nfa_trans A" i] show ?case by auto
  next
    case (step y z)
    then obtain bss where BS: "nfa_reach A i bss y" "list_all (is_alph n) bss" by blast
    from assms well_formed BS have "nfa_is_node A y" by (simp add: nfa_reach_is_node)
    with well_formed BS have B: "bddh n (subsetbdd (fst A) y (nfa_emptybdd (length y)))"
      by (simp add: wf_nfa_def bddh_subsetbdd nfa_emptybdd_def)
    from step have "z \<in> set (add_leaves (subsetbdd (fst A) y (nfa_emptybdd (length y))) [])" by (simp add: succsr_def subset_succs_def)
    with B have "\<exists>bs. z = bdd_lookup (subsetbdd (fst A) y (nfa_emptybdd (length y))) bs \<and> is_alph n bs" by (simp add: add_leaves_bdd_lookup)
    then obtain bs where Z:"z = bdd_lookup (subsetbdd (fst A) y (nfa_emptybdd (length y))) bs" and L: "is_alph n bs" by blast
    from BS(1) L have "nfa_reach A i (bss @ [bs]) (nfa_trans A y bs)" by (simp add: reach_snoc)
    with Z have "nfa_reach A i (bss @ [bs]) z" by (simp add: nfa_trans_def) moreover
    from BS L have "list_all (is_alph n) (bss @ [bs])" by simp
    moreover note BS(2) L
    ultimately show ?case by auto
  qed
qed

lemma nfa_reach_subset_memb:
  assumes R: "nfa_reach A q0 bss q"
  and Q0: "nfa_is_node A q0"
  and X: "list_all (is_alph n) bss"
  shows "subset_memb q (subset_dfs A q0)"
proof -
  from assms well_formed have Q: "nfa_is_node A q" by (simp add: nfa_reach_is_node)
  from R X have "\<exists>bs. nfa_reach A q0 bs q \<and> list_all (is_alph n) bs" by auto
  with Q0 have "(q0,q) \<in> (succsr (subset_succs A))\<^sup>*" by (simp add: nfa_reach_rtrancl)
  with Q0 Q show ?thesis by (simp add: dfs_eq_rtrancl)
qed

lemma det_nfa_reach':
  fixes bd :: "nat option bdd" and ls :: "bool list list"
  assumes "subset_dfs A (nfa_startnode A) = (bd, ls)" (is "?subset_dfs = _")
  and "\<exists>bs. nfa_reach A (nfa_startnode A) bs q1 \<and> list_all (is_alph n) bs"
  and "q1 = ls ! i" and "q2 = ls ! j" and "i < length ls" and "j < length ls"
  and "list_all (is_alph n) bss"
  shows "nfa_reach A q1 bss q2 = (dfa_reach (det_nfa A) i bss j \<and> nfa_is_node A q2)"
  (is "_ = (dfa_reach ?M i bss j \<and> _)")
proof
  assume "nfa_reach A q1 bss q2"
  from this assms show "dfa_reach ?M i bss j \<and> nfa_is_node A q2"
  proof (induct arbitrary: j)
    case (Nil j)
    with well_formed have Q0: "nfa_is_node A (nfa_startnode A)" by (simp add: nfa_startnode_is_node)
    from Nil obtain bs where "nfa_reach A (nfa_startnode A) bs q1" and "list_all (is_alph n) bs" by blast
    with well_formed Q0 Nil have Q1: "nfa_is_node A q1" by (simp add: nfa_reach_is_node)
    with Q0 have "\<And>v. (bdd_lookup (fst (?subset_dfs)) q1 = Some v) = (v < length (snd (?subset_dfs)) \<and> snd (?subset_dfs) ! v = q1)"
      by (simp add: subset_dfs_bij)
    with Nil(1) have 1: "\<And>v. (bdd_lookup bd q1 = Some v) = (v < length ls \<and> ls ! v = q1)" by simp
    from Nil 1 have "bdd_lookup bd q1 = Some i" by simp
    moreover from Nil 1 have "bdd_lookup bd q1 = Some j" by simp
    ultimately have "i = j" by simp
    have "dfa_reach ?M i [] i" by (simp add: reach_nil)
    with \<open>i=j\<close> Q1 show ?case by simp
  next
    case (snoc p bss bs j)
    note S_len = nfa_startnode_is_node[OF well_formed]
    from snoc obtain bss' where BSS':"nfa_reach A (nfa_startnode A) bss' q1" and BSS'L: "list_all (is_alph n) bss'" by blast
    with well_formed S_len have Q_len: "nfa_is_node A q1" by (simp add: nfa_reach_is_node)
    with well_formed snoc have P_len: "nfa_is_node A p" by (simp add: nfa_reach_is_node)
    from BSS' snoc have "nfa_reach A (nfa_startnode A) (bss' @ bss) p" by (simp add: reach_trans) moreover
    note S_len moreover
    from snoc BSS'L have "list_all (is_alph n) (bss' @ bss)" by simp
    ultimately have "subset_memb p ?subset_dfs" by (rule nfa_reach_subset_memb)
    hence "bdd_lookup (fst ?subset_dfs) p \<noteq> None" by (simp add: subset_memb_def split_beta)
    then obtain v where P: "bdd_lookup (fst ?subset_dfs) p = Some v" by (cases "bdd_lookup (fst ?subset_dfs) p") simp+
    with P_len S_len have "v < length (snd (?subset_dfs)) \<and> snd ?subset_dfs ! v = p" by (simp add: subset_dfs_bij)
    with snoc have V: "v < length ls \<and> ls ! v = p" by simp
    with snoc P_len have R: "dfa_reach ?M i bss v \<and> nfa_is_node A p" by simp

    from snoc have BS: "is_alph n bs" by simp
    with well_formed P_len have Z: "nfa_is_node A (nfa_trans A p bs)" by (simp add: nfa_trans_is_node)

    with snoc have N: "nfa_is_node A (ls ! j)" by simp
    from snoc have "j < length (snd ?subset_dfs) \<and> snd ?subset_dfs ! j = ls ! j" by simp
    with N S_len have "bdd_lookup (fst ?subset_dfs) (ls ! j) = Some j" by (simp add: subset_dfs_bij)
    with snoc have J: "bdd_lookup bd (ls ! j) = Some j" by simp

    from snoc have BD: "fst ?M = map (\<lambda>q. bdd_map (\<lambda>q. the (bdd_lookup bd q)) (subsetbdd (fst A) q (nfa_emptybdd (length q)))) ls"
      by (simp add: det_nfa_def)
    with V have "fst ?M ! v = bdd_map (\<lambda>q. the (bdd_lookup bd q)) (subsetbdd (fst A) p (nfa_emptybdd (length p)))" by simp
    with well_formed BS P_len have "bdd_lookup (fst ?M ! v) bs = the (bdd_lookup bd (bdd_lookup (subsetbdd (fst A) p (nfa_emptybdd (length p))) bs))"
      by (auto simp add: bdd_map_bdd_lookup bddh_subsetbdd wf_nfa_def is_alph_def nfa_emptybdd_def)
    also from snoc J have "\<dots> = j" by (simp add: nfa_trans_def)
    finally have JJ: "bdd_lookup (fst ?M ! v) bs = j" .

    from R BS JJ have RR: "dfa_reach ?M i (bss @ [bs]) j" by (auto simp add: reach_snoc dfa_trans_def[symmetric])
    with Z show ?case by simp
  qed
next
  assume "dfa_reach ?M i bss j \<and> nfa_is_node A q2"
  hence "dfa_reach ?M i bss j" and "nfa_is_node A q2" by simp+
  from this assms show "nfa_reach A q1 bss q2"
  proof (induct arbitrary: q2)
    case (snoc j bss bs q2)
    define v where "v = bdd_lookup (fst ?M ! j) bs"
    define qq where "qq = nfa_trans A (ls ! j) bs"
    from well_formed have Q0: "nfa_is_node A (nfa_startnode A)" by (simp add: nfa_startnode_is_node)

    from snoc have L: "length (fst ?M) = length ls" by (simp add: det_nfa_def)
    with snoc have "dfa_is_node ?M i" by (simp add: dfa_is_node_def) moreover
    note \<open>dfa_reach ?M i bss j\<close> moreover
    from snoc have "wf_dfa ?M n" by (simp add: det_wf_nfa) moreover
    from snoc have "list_all (is_alph n) bss" by simp
    ultimately have "dfa_is_node ?M j" by (simp add: dfa_reach_is_node)
    with L have J_len: "j < length ls" by (simp add: dfa_is_node_def)
    from Q0 have "list_all (nfa_is_node A) (snd ?subset_dfs)" by (rule subset_dfs_is_node)
    with snoc J_len have J: "nfa_is_node A (ls ! j)" by (simp add: list_all_iff)
    moreover note snoc(4,5,6) refl[of "ls!j"] snoc(8) J_len
    moreover from snoc have "list_all (is_alph n) bss" by simp
    ultimately have R: "nfa_reach A q1 bss (ls ! j)" by (rule snoc(2))
    from snoc obtain bs' where R': "nfa_reach A (nfa_startnode A) bs' q1" and BS': "list_all (is_alph n) bs'" by blast
    with R have lsj: "nfa_reach A (nfa_startnode A) (bs' @ bss) (ls ! j)" by (simp add: reach_trans)
    hence "nfa_reach A (nfa_startnode A) ((bs' @ bss) @ [bs]) qq" unfolding qq_def by (rule reach_snoc)
    with well_formed snoc(10) Q0 BS' have M: "subset_memb qq ?subset_dfs" and QQ_len: "nfa_is_node A qq" by (simp add: nfa_reach_subset_memb nfa_reach_is_node)+
    with snoc(4) have QQ: "bdd_lookup bd qq \<noteq> None" by (simp add: subset_memb_def)
    
    from well_formed snoc J have H: "bddh (length bs) (subsetbdd (fst A) (ls ! j) (nfa_emptybdd (length (ls ! j))))" by (simp add: bddh_subsetbdd wf_nfa_def nfa_emptybdd_def is_alph_def)
    from v_def have "v = bdd_lookup (fst ?M ! j) bs" by simp
    also from snoc(4) have "\<dots> = bdd_lookup (map (\<lambda>q. bdd_map (\<lambda>q. the (bdd_lookup bd q)) (subsetbdd (fst A) q (nfa_emptybdd (length q)))) ls ! j) bs"
      by (simp add: det_nfa_def)
    also from J_len have "\<dots> = bdd_lookup (bdd_map (\<lambda>q. the (bdd_lookup bd q)) (subsetbdd (fst A) (ls ! j) (nfa_emptybdd (length (ls ! j))))) bs" by simp
    also from H have "\<dots> = the (bdd_lookup bd (bdd_lookup (subsetbdd (fst A) (ls ! j) (nfa_emptybdd (length (ls ! j)))) bs))" by (simp add: bdd_map_bdd_lookup)
    also from qq_def have "\<dots> = the (bdd_lookup bd qq)" by (simp add: nfa_trans_def)
    finally have "v = the (bdd_lookup bd qq)" .
    with QQ have QQ': "bdd_lookup bd qq = Some v" by (cases "bdd_lookup bd qq") simp+
    
    with snoc(4) have "bdd_lookup (fst ?subset_dfs) qq = Some v" by simp
    with QQ_len Q0 have "v < length (snd ?subset_dfs) \<and> (snd ?subset_dfs) ! v = qq" by (simp add: subset_dfs_bij)
    with snoc v_def have Q2: "qq = q2" by (simp add: dfa_trans_def)

    with R qq_def show "nfa_reach A q1 (bss @ [bs]) q2" by (simp add: reach_snoc)
  qed (simp add: reach_nil)
qed

lemma det_nfa_reach:
  fixes bd :: "nat option bdd" and ls :: "bool list list"
  assumes S: "subset_dfs A (nfa_startnode A) = (bd, ls)" (is "?subset_dfs = _")
  and Q1: "q1 = ls ! j" and J: "j < length ls"
  and X: "list_all (is_alph n) bss"
  shows "nfa_reach A (nfa_startnode A) bss q1 = dfa_reach (det_nfa A) 0 bss j"
proof -
  note SL = nfa_startnode_is_node[OF well_formed]
  have "nfa_reach A (nfa_startnode A) [] (nfa_startnode A)" by (rule reach_nil)
  hence 1: "\<exists>b. nfa_reach A (nfa_startnode A) b (nfa_startnode A) \<and> list_all (is_alph n) b" by auto
  from SL have "bdd_lookup (fst ?subset_dfs) (nfa_startnode A) = Some 0" by (simp add: subset_dfs_start)
  with SL have "0 < length (snd ?subset_dfs) \<and> snd ?subset_dfs ! 0 = nfa_startnode A" by (simp add: subset_dfs_bij)
  with S have 2: "0 < length ls \<and> ls ! 0 = nfa_startnode A" by simp
  from S 1 Q1 J 2 X have T: "nfa_reach A (nfa_startnode A) bss q1 = (dfa_reach (det_nfa A) 0 bss j \<and> nfa_is_node A q1)"
    by (simp only: det_nfa_reach')
  from SL have "list_all (nfa_is_node A) (snd ?subset_dfs)" by (simp add: subset_dfs_is_node)
  with Q1 J S have "nfa_is_node A q1" by (simp add: list_all_iff)
  with T show ?thesis by simp
qed

lemma det_nfa_accepts:
  assumes X: "list_all (is_alph n) w"
  shows "dfa_accepts (det_nfa A) w = nfa_accepts A w"
proof -
  note SL = nfa_startnode_is_node[OF well_formed]
  let ?q = "nfa_startnode A"
  let ?subset_dfs = "subset_dfs A (nfa_startnode A)"
  define bd where "bd = fst ?subset_dfs"
  define ls where "ls = snd ?subset_dfs"
  with bd_def have BD: "?subset_dfs = (bd,ls)" by simp
  define p where "p = nfa_steps A (nfa_startnode A) w"
  with well_formed X SL have P: "nfa_is_node A p" by (simp add: nfa_steps_is_node)
  from p_def have R: "nfa_reach A ?q w p" by (simp add: reach_def)
  with assms have "\<exists>bs. nfa_reach A ?q bs p \<and> list_all (is_alph n) bs" by auto
  with SL have "(?q, p) \<in> (succsr (subset_succs A))\<^sup>*" by (simp add: nfa_reach_rtrancl)
  with SL P have "subset_memb p ?subset_dfs" by (simp add: dfs_eq_rtrancl)
  with BD have "bdd_lookup bd p \<noteq> None" by (simp add: subset_memb_def)
  then obtain k where K: "bdd_lookup bd p = Some k" by (cases "bdd_lookup bd p") simp+
  with SL P have K_len: "k < length ls \<and> ls ! k = p" unfolding bd_def ls_def by (simp add: subset_dfs_bij)
  with BD X R have "dfa_reach (det_nfa A) 0 w k" by (blast dest: det_nfa_reach)
  hence "k = dfa_steps (det_nfa A) 0 w" by (simp add: reach_def)
  hence "dfa_accepts (det_nfa A) w = snd (det_nfa A) ! k" by (simp add: accepts_def dfa_accepting_def)
  also from ls_def have "\<dots> = map (nfa_accepting A) ls ! k" by (simp add: det_nfa_def split_beta)
  also from K_len p_def have "\<dots> = nfa_accepts A w" by (simp add: accepts_def)
  finally show "dfa_accepts (det_nfa A) w = nfa_accepts A w" .
qed

end

lemma det_wf_nfa:
  assumes A: "wf_nfa A n"
  shows "wf_dfa (det_nfa A) n"
proof -
  from A
  interpret subset_DFS A n by unfold_locales
  show ?thesis by (rule det_wf_nfa)
qed

lemma det_nfa_accepts:
  assumes A: "wf_nfa A n"
  and w: "list_all (is_alph n) bss"
  shows "dfa_accepts (det_nfa A) bss = nfa_accepts A bss"
proof -
  from A
  interpret subset_DFS A n by unfold_locales
  from w show ?thesis by (rule det_nfa_accepts)
qed


subsection \<open>Quantifiers\<close>

fun quantify_bdd :: "nat \<Rightarrow> bool list bdd \<Rightarrow> bool list bdd" where
  "quantify_bdd i (Leaf q) = Leaf q"
| "quantify_bdd 0 (Branch l r) = (bdd_binop bv_or l r)"
| "quantify_bdd (Suc i) (Branch l r) = Branch (quantify_bdd i l) (quantify_bdd i r)"

lemma bddh_quantify_bdd:
  assumes "bddh (Suc n) bdd" and "v \<le> n"
  shows "bddh n (quantify_bdd v bdd)"
  using assms by (induct v bdd arbitrary: n rule: quantify_bdd.induct) (auto simp: bddh_binop split: nat.splits)

lemma quantify_bdd_is_node:
  assumes "bdd_all (nfa_is_node N) bdd"
  shows "bdd_all (nfa_is_node N) (quantify_bdd v bdd)"
using assms by (induct v bdd rule: quantify_bdd.induct) (simp add: bdd_all_bdd_binop[of "nfa_is_node N" _ "nfa_is_node N" _ "nfa_is_node N" bv_or, OF _ _ bv_or_is_node])+

definition
  quantify_nfa :: "nat \<Rightarrow> nfa \<Rightarrow> nfa" where
  "quantify_nfa i = (\<lambda>(bdds, as). (map (quantify_bdd i) bdds, as))"

lemma quantify_nfa_well_formed_aut:
  assumes "wf_nfa N (Suc n)"
  and "v \<le> n"
  shows "wf_nfa (quantify_nfa v N) n"
proof -
  from assms have 1: "list_all (bddh (Suc n)) (fst N)" and 2: "list_all (bdd_all (nfa_is_node N)) (fst N)" by (simp add: wf_nfa_def)+
  from 1 assms have 3: "list_all (bddh n) (fst (quantify_nfa v N))" by (simp add: quantify_nfa_def bddh_quantify_bdd list_all_iff split_beta)
  from 2 have "list_all (bdd_all (nfa_is_node N)) (fst (quantify_nfa v N))" by (simp add: quantify_bdd_is_node list_all_iff split_beta quantify_nfa_def)
  hence "list_all (bdd_all (nfa_is_node (quantify_nfa v N))) (fst (quantify_nfa v N))" by (simp add: quantify_nfa_def split_beta nfa_is_node_def)
  with 3 assms show ?thesis by (simp add: wf_nfa_def quantify_nfa_def split_beta)
qed

fun insertl :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insertl i a [] = [a]"
| "insertl 0 a bs = a # bs"
| "insertl (Suc i) a (b # bs) = b # (insertl i a bs)"

lemma insertl_len: 
  "length (insertl n x vs) = Suc (length vs)"
by (induct n x vs rule: insertl.induct) simp+

lemma insertl_0_eq: "insertl 0 x xs = x # xs"
  by (cases xs) simp_all

lemma bdd_lookup_quantify_bdd_set_of_bv: 
  assumes "length w = n"
  and "bddh (Suc n) bdd"
  and "bdd_all (nfa_is_node N) bdd"
  and "v \<le> n"
  shows "set_of_bv (bdd_lookup (quantify_bdd v bdd) w) = (\<Union>b. set_of_bv (bdd_lookup bdd (insertl v b w)))"
using assms proof (induct v bdd arbitrary: n w rule: quantify_bdd.induct)
  case (2 l r w)
  hence N: "nfa_is_node N (bdd_lookup l w)" "nfa_is_node N (bdd_lookup r w)" by (simp add: bdd_all_bdd_lookup)+
  have "set_of_bv (bdd_lookup (quantify_bdd 0 (Branch l r)) w) = set_of_bv (bdd_lookup (bdd_binop bv_or l r) w)" by simp
  also from 2 have "\<dots> = set_of_bv (bv_or (bdd_lookup l w) (bdd_lookup r w))" by (simp add: bdd_lookup_binop)
  also from N have "\<dots> = set_of_bv (bdd_lookup l w) \<union> set_of_bv (bdd_lookup r w)" by (simp add: bv_or_set_of_bv)
  also have "\<dots> = set_of_bv (bdd_lookup (Branch l r) (insertl 0 False w)) \<union> set_of_bv (bdd_lookup (Branch l r) (insertl 0 True w))" by (cases w) simp+
  also have "\<dots> = (\<Union>b \<in> {True, False}. set_of_bv (bdd_lookup (Branch l r) (insertl 0 b w)))" by auto
  also have "\<dots> = (\<Union>b. set_of_bv (bdd_lookup (Branch l r) (insertl 0 b w)))" by blast
  finally show ?case .
next
  case (3 n l r k w)
  then obtain j where J: "k = Suc j" by (cases k) simp+
  with 3 obtain a as where W: "w = a # as" by (cases w) auto
  with 3 J show ?case by (cases a) simp+
qed simp

lemma subsetbdd_set_of_bv:
  assumes "wf_nfa N (length ws)"
  and "nfa_is_node N q"
  shows "set_of_bv (bdd_lookup (subsetbdd (fst N) q (nfa_emptybdd (length q))) ws) = (\<Union>i\<in>set_of_bv q. set_of_bv (bdd_lookup (fst N ! i) ws))"
  (is "set_of_bv ?q = _")
proof (simp only: set_eq_iff, rule allI)
  fix x :: nat
  from assms have "bdd_all (nfa_is_node N) (subsetbdd (fst N) q (nfa_emptybdd (length q)))"
    by (simp add: wf_nfa_def bdd_all_is_node_subsetbdd)
  with assms have "nfa_is_node N ?q"
    by (simp add: wf_nfa_def bdd_all_bdd_lookup bddh_subsetbdd nfa_emptybdd_def)
  hence L: "length ?q = length (fst N)" by (simp add: nfa_is_node_def)
  {
    fix i assume H: "i < length (fst N)"
    with assms have "nfa_is_node N (bdd_lookup (fst N ! i) ws)" by (simp add: wf_nfa_def list_all_iff bdd_all_bdd_lookup)
  }
  with assms have I: "\<And>i. i < length q \<Longrightarrow> nfa_is_node N (bdd_lookup (fst N ! i) ws)" by (simp add: nfa_is_node_def)

  from L assms have "x \<in> set_of_bv ?q = (x < length (fst N) \<and> (\<exists>i \<in> set_of_bv q. bdd_lookup (fst N ! i) ws ! x \<and> i < length q))" by (auto simp add: set_of_bv_def bdd_lookup_subsetbdd)
  also from I have "\<dots> = (x \<in> (\<Union>i \<in> set_of_bv q. set_of_bv (bdd_lookup (fst N ! i) ws)))" by (auto simp: nfa_is_node_def set_of_bv_def)
  finally show "x \<in> set_of_bv ?q = (x \<in> (\<Union>i \<in> set_of_bv q. set_of_bv (bdd_lookup (fst N ! i) ws)))" .
qed

lemma nfa_trans_quantify_nfa:
  assumes "wf_nfa N (Suc n)"
  and "v \<le> n"
  and "is_alph n w"
  and "nfa_is_node N q"
  shows "set_of_bv (nfa_trans (quantify_nfa v N) q w) = (\<Union>b. set_of_bv (nfa_trans N q (insertl v b w)))"
proof -
  from assms have V1: "wf_nfa (quantify_nfa v N) n" by (simp add: quantify_nfa_well_formed_aut)
  with assms have V2: "wf_nfa (quantify_nfa v N) (length w)" by (simp add: wf_nfa_def is_alph_def)
  from assms have N: "nfa_is_node (quantify_nfa v N) q" by (simp add: quantify_nfa_def wf_nfa_def split_beta nfa_is_node_def)
  { fix i assume H: "i \<in> set_of_bv q"
    with assms have "i < length (fst N)" by (simp add: nfa_is_node_def set_of_bv_def)
    with assms have "bddh (Suc n) (fst N ! i)" "bdd_all (nfa_is_node N) (fst N ! i)" by (simp add: wf_nfa_def list_all_iff)+
  }
  with assms have I: "\<And>i. i \<in> set_of_bv q \<Longrightarrow> length w = n \<and> bddh (Suc n) (fst N ! i) \<and> bdd_all (nfa_is_node N) (fst N ! i) \<and> v \<le> n" by (simp add: is_alph_def)
  from assms have V3: "\<And>b. wf_nfa N (length (insertl v b w))" by (simp add: wf_nfa_def is_alph_def insertl_len)
  from N V2  have "set_of_bv (bdd_lookup (subsetbdd (fst (quantify_nfa v N)) q (nfa_emptybdd (length q))) w) = (\<Union>i\<in>set_of_bv q. set_of_bv (bdd_lookup (fst (quantify_nfa v N) ! i) w))"
    by (simp add: subsetbdd_set_of_bv)
  also from assms have "\<dots> = (\<Union>i\<in>set_of_bv q.  set_of_bv (bdd_lookup (quantify_bdd v (fst N ! i)) w))" by (auto simp: quantify_nfa_def split_beta nfa_is_node_def set_of_bv_def)
  also have "\<dots> = (\<Union>i\<in>set_of_bv q. \<Union>b. set_of_bv (bdd_lookup (fst N ! i) (insertl v b w)))"
  proof (simp only: set_eq_iff, rule allI)
    fix x
    have "x \<in> (\<Union>i\<in>set_of_bv q. set_of_bv (bdd_lookup (quantify_bdd v (fst N ! i)) w)) = (\<exists>i\<in>set_of_bv q. x \<in> set_of_bv (bdd_lookup (quantify_bdd v (fst N ! i)) w))" by simp
    also have "\<dots> = ({i. i \<in> set_of_bv q \<and> x \<in> set_of_bv (bdd_lookup (quantify_bdd v (fst N ! i)) w)} \<noteq> {})" by auto
    also from I have "\<dots> = ({i. i \<in> set_of_bv q \<and> x \<in> (\<Union>b. set_of_bv (bdd_lookup (fst N ! i) (insertl v b w)))} \<noteq> {})" by (auto simp: bdd_lookup_quantify_bdd_set_of_bv[of w n _ N])
    also have "\<dots> = (\<exists>i\<in>set_of_bv q. x \<in> (\<Union>b. set_of_bv (bdd_lookup (fst N ! i) (insertl v b w))))" by auto 
    also have "\<dots> = (x \<in> (\<Union>i\<in>set_of_bv q. \<Union>b. set_of_bv (bdd_lookup (fst N ! i) (insertl v b w))))" by simp
    finally show "(x \<in> (\<Union>i\<in>set_of_bv q. set_of_bv (bdd_lookup (quantify_bdd v (fst N ! i)) w))) = (x \<in> (\<Union>i \<in> set_of_bv q. \<Union>b. set_of_bv (bdd_lookup (fst N ! i) (insertl v b w))))" .
  qed
  also have "\<dots> = (\<Union>b. \<Union>i\<in>set_of_bv q. set_of_bv (bdd_lookup (fst N ! i) (insertl v b w)))" by auto
  also from V3 assms have "\<dots> = (\<Union>b. set_of_bv (bdd_lookup (subsetbdd (fst N) q (nfa_emptybdd (length q))) (insertl v b w)))" by (simp add: subsetbdd_set_of_bv)
  finally show ?thesis by (simp add: nfa_trans_def)
qed

fun insertll :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list"
where
  "insertll i [] [] = []"
| "insertll i (a # as) (bs # bss) = insertl i a bs # insertll i as bss"

lemma insertll_len2:
  assumes "list_all (is_alph n) vs"
  and "length x = length vs"
  shows "list_all (is_alph (Suc n)) (insertll k x vs)"
using assms by (induct k x vs rule: insertll.induct) (auto simp: insertl_len is_alph_def)+

lemma insertll_append:
  assumes "length xs = length vs"
  shows "insertll k (xs @ [x]) (vs @ [v]) = insertll k xs vs @ [insertl k x v]"
using assms by (induct k xs vs rule: insertll.induct) simp+

lemma UN_UN_lenset: "(\<Union>b. \<Union>x\<in>{x. length x = n}. M b x) = (\<Union>bs\<in>{x. length x = Suc n}. M (last bs) (butlast bs))"
proof auto
  fix x b xa assume "x \<in> M b xa"
  hence "length (xa @ [b]) = Suc (length xa) \<and> x \<in> M (last (xa @ [b])) (butlast (xa @ [b]))" by simp
  thus "\<exists>bs. length bs = Suc (length xa) \<and> x \<in> M (last bs) (butlast bs)" ..
next
  fix x bs assume "x \<in> M (last bs) (butlast bs)" and "length bs = Suc n"
  hence "length (butlast bs) = n \<and> x \<in> M (last bs) (butlast bs)" by simp
  thus "\<exists>b xa. length xa = n \<and> x \<in> M b xa" by blast
qed

lemma nfa_steps_quantify_nfa:
  assumes "wf_nfa N (Suc n)"
  and "list_all (is_alph n) w"
  and "nfa_is_node N q"
  and "v \<le> n"
  shows "set_of_bv (nfa_steps (quantify_nfa v N) q w) = (\<Union>xs \<in> {x. length x = length w}. set_of_bv (nfa_steps N q (insertll v xs w)))"
using assms proof (induct w rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc x xs)
  hence "wf_nfa (quantify_nfa v N) n" by (simp add: quantify_nfa_well_formed_aut)
  moreover from snoc have "nfa_is_node (quantify_nfa v N) q" by (simp add: nfa_is_node_def quantify_nfa_def split_beta)
  moreover note snoc
  ultimately have "nfa_is_node (quantify_nfa v N) (nfa_steps (quantify_nfa v N) q xs)" by (simp add: nfa_steps_is_node[of _ n])
  hence N: "nfa_is_node N (nfa_steps (quantify_nfa v N) q xs)" (is "nfa_is_node N ?q") by (simp add: nfa_is_node_def quantify_nfa_def split_beta)
  from snoc have "\<And>b. length (insertl v b x) = Suc n" by (simp add: insertl_len is_alph_def)
  with snoc have B: "\<And>b. wf_nfa N (length (insertl v b x))" by simp
  from snoc have IV: "set_of_bv (nfa_steps (quantify_nfa v N) q xs) = (\<Union>x \<in>{x. length x = length xs}. set_of_bv (nfa_steps N q (insertll v x xs)))" by simp

  { fix bs :: "bool list" assume H: "length bs = length xs"
    with snoc have "list_all (is_alph (Suc n)) (insertll v bs xs)" by (simp add: insertll_len2)
    with snoc have "nfa_is_node N (nfa_steps N q (insertll v bs xs))" by (simp add: nfa_steps_is_node)
  } note N2 = this

  have "set_of_bv (nfa_steps (quantify_nfa v N) q (xs @ [x])) = set_of_bv (nfa_steps (quantify_nfa v N) ?q [x])"
    by simp
  also have "\<dots> = set_of_bv (nfa_trans (quantify_nfa v N) ?q x)" by simp
  also from snoc N have "\<dots> = (\<Union>b. set_of_bv (nfa_trans N ?q (insertl v b x)))" by (simp add: nfa_trans_quantify_nfa)
  also have "\<dots> = (\<Union>b. set_of_bv (bdd_lookup (subsetbdd (fst N) ?q (nfa_emptybdd (length ?q))) (insertl v b x)))" by (simp add: nfa_trans_def)
  also from N B have "\<dots> = (\<Union>b. \<Union>i\<in>set_of_bv ?q. set_of_bv (bdd_lookup (fst N ! i) (insertl v b x)))" by (simp add: subsetbdd_set_of_bv)
  also from IV have "\<dots> = (\<Union>b. \<Union>i\<in>(\<Union>x\<in>{x. length x = length xs}. set_of_bv (nfa_steps N q (insertll v x xs))). set_of_bv (bdd_lookup (fst N ! i) (insertl v b x)))" by simp
  also have "\<dots> = (\<Union>b. \<Union>y\<in>{x. length x = length xs}. \<Union>i\<in>set_of_bv (nfa_steps N q (insertll v y xs)). set_of_bv (bdd_lookup (fst N ! i) (insertl v b x)))" by simp
  also have "\<dots> = (\<Union>bs\<in>{x. length x = Suc (length xs)}. \<Union>i\<in>set_of_bv (nfa_steps N q (insertll v (butlast bs) xs)). set_of_bv (bdd_lookup (fst N ! i) (insertl v (last bs) x)))"
    by (simp add: UN_UN_lenset)
  also from N2 B have "\<dots> = (\<Union>bs\<in>{x. length x = Suc (length xs)}. set_of_bv (nfa_trans N (nfa_steps N q (insertll v (butlast bs) xs)) (insertl v (last bs) x)))" (is "?L = ?R")
    by (simp add: subsetbdd_set_of_bv[folded nfa_trans_def])
  also have "\<dots> = (\<Union>bs\<in>{x. length x = Suc (length xs)}. set_of_bv (nfa_steps N q (insertll v (butlast bs) xs @ [insertl v (last bs) x])))"
    by simp
  also have "\<dots> = (\<Union>bs\<in>{x. length x = Suc (length xs)}. set_of_bv (nfa_steps N q (insertll v (butlast bs @ [last bs]) (xs @ [x]))))" by (auto simp: insertll_append)
  also have "\<dots> = (\<Union>bs\<in>{x. length x = Suc (length xs)}. set_of_bv (nfa_steps N q (insertll v bs (xs @ [x]))))"
  proof (rule set_eqI)
    fix xa
    have "(xa \<in> (\<Union>bs\<in>{x. length x = Suc (length xs)}. set_of_bv (nfa_steps N q (insertll v (butlast bs @ [last bs]) (xs @ [x]))))) =
      (\<exists>bs \<in> {x. length x = Suc (length xs)}. bs \<noteq> [] \<and> xa \<in> set_of_bv (nfa_steps N q (insertll v (butlast bs @ [last bs]) (xs @ [x]))))" by auto
    also have "\<dots> = (\<exists>bs \<in> {x. length x = Suc (length xs)}. bs \<noteq> [] \<and> xa \<in> set_of_bv (nfa_steps N q (insertll v bs (xs @ [x]))))" by auto
    also have "\<dots> = (xa \<in> (\<Union>bs\<in>{x. length x = Suc (length xs)}. set_of_bv (nfa_steps N q (insertll v bs (xs @ [x])))))" by auto
    finally show "(xa \<in> (\<Union>bs\<in>{x. length x = Suc (length xs)}. set_of_bv (nfa_steps N q (insertll v (butlast bs @ [last bs]) (xs @ [x]))))) =
  (xa \<in> (\<Union>bs\<in>{x. length x = Suc (length xs)}. set_of_bv (nfa_steps N q (insertll v bs (xs @ [x])))))" .
  qed
  finally show ?case by simp
qed

lemma nfa_accepts_quantify_nfa:
  assumes "wf_nfa A (Suc n)"
  and "i \<le> n"
  and "list_all (is_alph n) bss"
  shows "nfa_accepts (quantify_nfa i A) bss = (\<exists>bs. nfa_accepts A (insertll i bs bss) \<and> length bs = length bss)" 
proof -
  note Q0 = nfa_startnode_is_node[OF assms(1)]
  hence "nfa_is_node A (nfa_startnode (quantify_nfa i A))" by (simp add: nfa_startnode_def quantify_nfa_def split_beta)
  with assms have I: "set_of_bv (nfa_steps (quantify_nfa i A) (nfa_startnode (quantify_nfa i A)) bss) =
    (\<Union>bs \<in> {bs. length bs = length bss}. set_of_bv (nfa_steps A (nfa_startnode (quantify_nfa i A)) (insertll i bs bss)))"
    by (simp add: nfa_steps_quantify_nfa)
  have "nfa_accepts (quantify_nfa i A) bss = nfa_accepting (quantify_nfa i A) (nfa_steps (quantify_nfa i A) (nfa_startnode (quantify_nfa i A)) bss)" by (simp add: accepts_def)
  also have "\<dots> = (set_of_bv (snd (quantify_nfa i A)) \<inter> set_of_bv (nfa_steps (quantify_nfa i A) (nfa_startnode (quantify_nfa i A)) bss) \<noteq> {})" by (simp add: nfa_accepting_set_of_bv)
  also from I have "\<dots> = (set_of_bv (snd A) \<inter> (\<Union>bs \<in> {bs. length bs = length bss}. set_of_bv (nfa_steps A (nfa_startnode (quantify_nfa i A)) (insertll i bs bss))) \<noteq> {})"
    by (simp add: quantify_nfa_def split_beta)
  also have "\<dots> = ((\<Union>bs \<in> {bs. length bs = length bss}. set_of_bv (snd A) \<inter> set_of_bv (nfa_steps A (nfa_startnode (quantify_nfa i A)) (insertll i bs bss))) \<noteq> {})" by simp
  also have "\<dots> = (\<exists>bs \<in> {bs. length bs = length bss}. set_of_bv (snd A) \<inter> set_of_bv (nfa_steps A (nfa_startnode A) (insertll i bs bss)) \<noteq> {})" by (auto simp: nfa_startnode_def quantify_nfa_def split_beta)
  also have "\<dots> = (\<exists>bs. nfa_accepts A (insertll i bs bss) \<and> length bs = length bss)" by (auto simp: accepts_def nfa_accepting_set_of_bv)
  finally show ?thesis .
qed


subsection \<open>Right Quotient\<close>

definition
  rquot_succs :: "nat bdd list \<times> bool list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "rquot_succs M = (\<lambda>n x. [bdd_lookup (fst M ! x) (replicate n False)])"

definition
  rquot_invariant :: "nat bdd list \<times> bool list \<Rightarrow> bool list \<Rightarrow> bool" where
  "rquot_invariant M = (\<lambda>l. length l = length (fst M))"

definition
  "rquot_ins = (\<lambda>x l. l[x:=True])"

definition
  rquot_memb :: "nat \<Rightarrow> bool list \<Rightarrow> bool" where
  "rquot_memb = (\<lambda>x l. l ! x)"

definition
  rquot_empt :: "nat bdd list \<times> bool list \<Rightarrow> bool list" where
  "rquot_empt M = replicate (length (fst M)) False"

definition 
  "rquot_dfs M n x = gen_dfs (rquot_succs M n) rquot_ins rquot_memb (rquot_empt M) [x]"

definition
  zeros :: "nat \<Rightarrow> nat \<Rightarrow> bool list list" where
  "zeros m n = replicate m (replicate n False)"

lemma zeros_is_alpha: "list_all (is_alph v) (zeros n v)"
  by (induct n) (simp add: zeros_def is_alph_def)+

lemma zeros_rone: "zeros (Suc n) v = zeros n v @ zeros 1 v"
  by (simp add: zeros_def replicate_append_same)

lemma zeros_len: "length (zeros n v) = n" 
  by (simp add: zeros_def)

lemma zeros_rtrancl: "(\<exists>n. dfa_reach M x (zeros n v) y) = ((x,y) \<in> (succsr (rquot_succs M v))\<^sup>*)"
proof
  assume "\<exists>n. dfa_reach M x (zeros n v) y"
  then obtain n where N: "dfa_reach M x (zeros n v) y" ..
  define w where "w = zeros n v"
  hence W: "\<exists>n. w = zeros n v" by auto
  from w_def N have "dfa_reach M x w y" by simp
  from this W show "(x,y) \<in> (succsr (rquot_succs M v))\<^sup>*"
  proof induct
    case (snoc k ws y)
    then obtain n' where N': "ws @ [y] = zeros n' v" by blast
    have "length (ws @ [y]) > 0" by simp
    with N' have "n' > 0" by (simp add: zeros_len)
    then obtain n where NL: "n' = Suc n" by (cases n') simp+
    hence "zeros n' v = zeros n v @ zeros 1 v" by (simp only: zeros_rone)
    also have "\<dots> = zeros n v @ [replicate v False]" by (simp add: zeros_def)
    finally have "zeros n' v = zeros n v @ [replicate v False]" .
    with N' have WS: "ws = zeros n v" "y = replicate v False" by auto
    hence "\<exists>n. ws = zeros n v" by auto
    with snoc have IV: "(x,k) \<in> (succsr (rquot_succs M v))\<^sup>*" by simp
    from WS have "dfa_trans M k y \<in> set (rquot_succs M v k)" by (simp add: rquot_succs_def dfa_trans_def)
    hence "(k, dfa_trans M k y) \<in> (succsr (rquot_succs M v))\<^sup>*" by (auto simp: succsr_def)
    with IV show ?case by simp
  qed simp
next
  assume "(x,y) \<in> (succsr (rquot_succs M v))\<^sup>*"
  thus "\<exists>n. dfa_reach M x (zeros n v) y"
  proof induct
    case base
    have "dfa_reach M x (zeros 0 v) x" by (simp add: reach_nil zeros_def)
    thus "\<exists>n. dfa_reach M x (zeros n v) x" by (rule exI)
  next
    case (step y z)
    then obtain n where N: "dfa_reach M x (zeros n v) y" by blast
    with step have Z: "z = dfa_trans M y (replicate v False)" by (simp add: succsr_def rquot_succs_def dfa_trans_def)
    from N Z have "dfa_reach M x (zeros n v @ zeros 1 v) z" by (simp add: reach_snoc zeros_def)
    hence "dfa_reach M x (zeros (Suc n) v) z" by (simp only: zeros_rone)
    thus ?case by (rule exI)
  qed
qed

primrec map_index :: "('a \<Rightarrow> nat \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> 'b list"
where
  "map_index f [] n = []"
| "map_index f (x#xs) n = f x n # map_index f xs (Suc n)"

lemma map_index_len:
  "length (map_index f ls n) = length ls"
 by (induct ls arbitrary: n) simp+

lemma map_index_nth:
  assumes "i < length l"
  shows "map_index f l n ! i = f (l ! i) (n + i)"
using assms proof (induct l arbitrary: n i)
  case (Cons a l n i)
  show ?case proof (cases "i = 0")
    case False
    then obtain j where J: "i = Suc j" by (cases i) simp+
    with Cons show ?thesis by simp
  qed simp
qed simp

definition
  rquot :: "dfa \<Rightarrow> nat \<Rightarrow> dfa" where
  "rquot = (\<lambda>(bd, as) v. (bd, map_index (\<lambda>x n. nfa_accepting' as (rquot_dfs (bd, as) v n)) as 0))"

lemma rquot_well_formed_aut:
  assumes "wf_dfa M n"
  shows "wf_dfa (rquot M n) n"
using assms by (simp add: rquot_def split_beta wf_dfa_def map_index_len dfa_is_node_def)

lemma rquot_node:
  "dfa_is_node (rquot M n) q = dfa_is_node M q"
  by (simp add: rquot_def dfa_is_node_def split_beta)

lemma rquot_steps:
  "dfa_steps (rquot M n) x w = dfa_steps M x w"
  by (simp add: rquot_def dfa_trans_def [abs_def] split_beta)

locale rquot_DFS =
  fixes A :: dfa and n :: nat
  assumes well_formed: "wf_dfa A n"

sublocale rquot_DFS < DFS "rquot_succs A n" "dfa_is_node A"
  "rquot_invariant A" rquot_ins rquot_memb "rquot_empt A"
proof (insert well_formed, unfold_locales)
  fix x y S assume "dfa_is_node A x" and "dfa_is_node A y" and "rquot_invariant A S" and "\<not> rquot_memb y S"
  thus "rquot_memb x (rquot_ins y S) = (x = y \<or> rquot_memb x S)"
    by (cases "x=y") (simp add: dfa_is_node_def rquot_invariant_def rquot_memb_def rquot_ins_def)+
qed (simp add: dfa_is_node_def rquot_memb_def rquot_empt_def
     rquot_succs_def rquot_invariant_def rquot_ins_def
     bounded_nat_set_is_finite[of _ "length (fst A)"]
     dfa_trans_is_node[unfolded dfa_trans_def dfa_is_node_def is_alph_def])+

context rquot_DFS
begin

lemma rquot_dfs_invariant:
  assumes "dfa_is_node A x"
  shows "rquot_invariant A (rquot_dfs A n x)"
  using assms well_formed unfolding rquot_dfs_def
  by (auto simp: dfs_invariant' empt_invariant)

lemma dfa_reach_rquot:
  assumes "dfa_is_node A x"
  and "dfa_is_node A y"
  shows "rquot_memb y (rquot_dfs A n x) = (\<exists>m. dfa_reach A x (zeros m n) y)"
proof -
  from assms have "rquot_memb y (rquot_dfs A n x) = ((x,y) \<in> (succsr (rquot_succs A n))\<^sup>*)"
    by (simp add: dfs_eq_rtrancl rquot_dfs_def)
  also have "\<dots> = (\<exists>m. dfa_reach A x (zeros m n) y)" by (simp add: zeros_rtrancl)
  finally show ?thesis .
qed

lemma rquot_accepting:
  assumes "dfa_is_node (rquot A n) q"
  shows "dfa_accepting (rquot A n) q = (\<exists>m. dfa_accepting A (dfa_steps A q (zeros m n)))"
proof -
  from assms have Q: "dfa_is_node A q" by (simp add: rquot_node)
  with assms have "rquot_invariant A (rquot_dfs A n q)" by (simp add: rquot_dfs_invariant)
  hence L: "length (rquot_dfs A n q) = length (fst A)" by (simp add: rquot_invariant_def)
  
  have "nfa_accepting' (snd A) (rquot_dfs A n q) = (set_of_bv (snd A) \<inter> set_of_bv (rquot_dfs A n q) \<noteq> {})" by (simp add: nfa_accepting'_set_of_bv)
  also have "\<dots> = (\<exists>i. i < length (snd A) \<and> snd A ! i \<and> i < length (rquot_dfs A n q) \<and> rquot_dfs A n q ! i)" by (auto simp: set_of_bv_def)
  also from well_formed L have "\<dots> = (\<exists>i. dfa_is_node A i \<and> snd A ! i \<and> rquot_memb i (rquot_dfs A n q))" by (auto simp add: wf_dfa_def dfa_is_node_def rquot_memb_def)
  also have "\<dots> = ({i. dfa_is_node A i \<and> snd A ! i \<and> rquot_memb i (rquot_dfs A n q)} \<noteq> {})" by auto
  also from assms Q have "\<dots> = ({i. dfa_is_node A i \<and> snd A ! i \<and> (\<exists>m. dfa_reach A q (zeros m n) i)} \<noteq> {})" by (auto simp: dfa_reach_rquot)
  also have "\<dots> = ({i. \<exists>m. dfa_is_node A i \<and> snd A ! i \<and> i = dfa_steps A q (zeros m n)} \<noteq> {})" by (simp add: reach_def)
  also have "\<dots> = (\<exists>i m. dfa_is_node A i \<and> snd A ! i \<and> i = dfa_steps A q (zeros m n))" by auto
  also have "\<dots> = (\<exists>m. snd A ! dfa_steps A q (zeros m n))"
  proof
    assume "\<exists>m. snd A ! dfa_steps A q (zeros m n)"
    then obtain m where N: "snd A ! dfa_steps A q (zeros m n)" ..
    from well_formed Q zeros_is_alpha[of n m] have "dfa_is_node A (dfa_steps A q (zeros m n))" by (simp add: dfa_steps_is_node)
    with N show "\<exists>i m. dfa_is_node A i \<and> snd A ! i \<and> i = dfa_steps A q (zeros m n)" by auto
  qed auto
  finally have "nfa_accepting' (snd A) (rquot_dfs A n q) = (\<exists>m. snd A ! dfa_steps A q (zeros m n))" .
  with well_formed assms show ?thesis by (simp add: dfa_accepting_def rquot_def split_beta dfa_is_node_def map_index_nth wf_dfa_def)
qed

end

lemma rquot_accepts:
  assumes A: "wf_dfa A n"
  and "list_all (is_alph n) bss"
  shows "dfa_accepts (rquot A n) bss = (\<exists>m. dfa_accepts A (bss @ zeros m n))"
proof -
  from A
  interpret rquot_DFS A n by unfold_locales
  from assms have V: "wf_dfa (rquot A n) n" by (simp add: rquot_well_formed_aut)
  hence "dfa_is_node (rquot A n) 0" by (simp add: dfa_startnode_is_node)
  with assms V have q: "dfa_is_node (rquot A n) (dfa_steps (rquot A n) 0 bss)" by (simp add: dfa_steps_is_node)
  
  have "dfa_accepts (rquot A n) bss = dfa_accepting (rquot A n) (dfa_steps (rquot A n) 0 bss)" by (simp add: accepts_def)
  also from assms q have "\<dots> = (\<exists>m. dfa_accepting A (dfa_steps A (dfa_steps A 0 bss) (zeros m n)))" by (simp add: rquot_accepting rquot_steps)
  also have "\<dots> = (\<exists>m. dfa_accepting A (dfa_steps A 0 (bss @ zeros m n)))" by simp
  also have "\<dots> = (\<exists>m. dfa_accepts A (bss @ zeros m n))" by (simp add: accepts_def)
  finally show ?thesis .
qed


subsection \<open>Diophantine Equations\<close>

fun eval_dioph :: "int list \<Rightarrow> nat list \<Rightarrow> int"
where
  "eval_dioph (k # ks) (x # xs) = k * int x + eval_dioph ks xs"
| "eval_dioph ks xs = 0"

lemma eval_dioph_mult:
  "eval_dioph ks xs * int n = eval_dioph ks (map (\<lambda>x. x * n) xs)"
  by(induct ks xs rule: eval_dioph.induct) (simp_all add: distrib_right)

lemma eval_dioph_add_map:
  "eval_dioph ks (map f xs) + eval_dioph ks (map g xs) =
   eval_dioph ks (map (\<lambda>x. f x + g x) (xs::nat list))"
proof (induct ks xs rule: eval_dioph.induct)
  case (1 k ks x xs)
  have "eval_dioph (k # ks) (map f (x # xs)) + eval_dioph (k # ks) (map g (x # xs)) =
    (k * int (f x) + k * int (g x)) + (eval_dioph ks (map f xs) + eval_dioph ks (map g xs))"
    by simp
  also have "\<dots> = (k * int (f x) + k * int (g x)) + eval_dioph ks (map (\<lambda>x. f x + g x) xs)"
    by (simp add: 1)
  finally show ?case by (simp add: ac_simps distrib_left)
qed simp_all

lemma eval_dioph_div_mult:
  "eval_dioph ks (map (\<lambda>x. x div n) xs) * int n +
   eval_dioph ks (map (\<lambda>x. x mod n) xs) = eval_dioph ks xs"
  by (simp add: eval_dioph_mult o_def eval_dioph_add_map)

lemma eval_dioph_mod:
  "eval_dioph ks xs mod int n = eval_dioph ks (map (\<lambda>x. x mod n) xs) mod int n"
proof (induct ks xs rule: eval_dioph.induct)
  case (1 k ks x xs)
  have "eval_dioph (k # ks) (x # xs) mod int n =
    ((k * int x) mod int n + eval_dioph ks xs mod int n) mod int n"
    by (simp add: mod_add_eq)
  also have "\<dots> = ((k * (int x mod int n)) mod int n +
    eval_dioph ks (map (\<lambda>x. x mod n) xs) mod int n) mod int n"
    by (simp add: 1 mod_mult_right_eq)
  finally show ?case by (simp add: zmod_int mod_add_eq)
qed simp_all

lemma eval_dioph_div_mod:
  "(eval_dioph ks xs = l) =
   (eval_dioph ks (map (\<lambda>x. x mod 2) xs) mod 2 = l mod 2 \<and>
    eval_dioph ks (map (\<lambda>x. x div 2) xs) =
      (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2)" (is "?l = ?r")
proof
  assume eq: ?l
  then have "eval_dioph ks xs mod 2 = l mod 2" by simp
  with eval_dioph_mod [of _ _ 2]
  have eq': "eval_dioph ks (map (\<lambda>x. x mod 2) xs) mod 2 = l mod 2"
    by simp
  from eval_dioph_div_mult [symmetric, of ks xs 2] eq
  have "eval_dioph ks (map (\<lambda>x. x div 2) xs) * 2 + eval_dioph ks (map (\<lambda>x. x mod 2) xs) = l"
    by simp
  then have "eval_dioph ks (map (\<lambda>x. x div 2) xs) * 2 = l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)"
    by (simp add: eq_diff_eq)
  then have "(eval_dioph ks (map (\<lambda>x. x div 2) xs) * 2) div 2 =
    (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2"
    by simp
  with eq' show ?r by simp
next
  assume ?r (is "?r1 \<and> ?r2")
  then obtain eq1: ?r1 and eq2: ?r2 ..
  from eq1 have "(l - eval_dioph ks (map (\<lambda>x. x mod 2) xs) mod 2) mod 2 =
    (l - l mod 2) mod 2"
    by simp
  then have "(l mod 2 - eval_dioph ks (map (\<lambda>x. x mod 2) xs) mod 2 mod 2) mod 2 =
    (l mod 2 - l mod 2 mod 2) mod 2"
    by (simp only: mod_diff_eq)
  then have eq1': "(l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) mod 2 = 0"
    by (simp add: mod_diff_eq)
  from eq2 have
    "eval_dioph ks (map (\<lambda>x. x div 2) xs) * 2 +
     (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) mod 2 =
     (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2 * 2 +
     (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) mod 2"
    by simp
  then have
    "eval_dioph ks (map (\<lambda>x. x div 2) xs) * 2 +
     (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) mod 2 =
     l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)"
    by simp
  with eq1' eval_dioph_div_mult [of _ 2] show ?l
    by (simp add: eq_diff_eq)
qed

lemma eval_dioph_ineq_div_mod:
  "(eval_dioph ks xs \<le> l) =
   (eval_dioph ks (map (\<lambda>x. x div 2) xs) \<le>
      (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2)" (is "?l = ?r")
proof
  assume ?l
  with eval_dioph_div_mult [symmetric, of ks xs 2]
  have "eval_dioph ks (map (\<lambda>x. x div 2) xs) * 2 + eval_dioph ks (map (\<lambda>x. x mod 2) xs) \<le> l"
    by simp
  then have "eval_dioph ks (map (\<lambda>x. x div 2) xs) * 2 \<le> l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)"
    by (simp add: le_diff_eq)
  then have "(eval_dioph ks (map (\<lambda>x. x div 2) xs) * 2) div 2 \<le>
    (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2"
    by (rule zdiv_mono1) simp
  then show ?r by simp
next
  assume ?r
  have "eval_dioph ks xs \<le> eval_dioph ks xs +
    (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) mod 2"
    by simp
  also {
  from \<open>?r\<close> have "eval_dioph ks (map (\<lambda>x. x div 2) xs) * 2 \<le>
    (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2 * 2"
    by simp
  also have "\<dots> = l - eval_dioph ks (map (\<lambda>x. x mod 2) xs) -
    (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) mod 2"
    by (simp add: eq_diff_eq)
  finally have "(eval_dioph ks (map (\<lambda>x. x div 2) xs) * 2 +
    eval_dioph ks (map (\<lambda>x. x mod 2) xs)) +
    (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) mod 2 \<le> l"
    by simp
  with eval_dioph_div_mult [of _ 2]
  have "eval_dioph ks xs +
    (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) mod 2 \<le> l"
    by simp }
  finally show ?l .
qed

lemma sum_list_abs_ge_0: "(0::int) \<le> sum_list (map abs ks)"
  by (induct ks) simp_all

lemma zmult_div_aux1:
  assumes b: "b \<noteq> 0"
  shows "(a - a mod b) div b = (a::int) div b"
proof -
  from minus_mod_eq_mult_div [symmetric, of b a]
  have "(b * (a div b)) div b = (a - a mod b) div b"
    by simp
  with b show ?thesis by simp
qed

lemma zmult_div_aux2:
  assumes b: "b \<noteq> 0"
  shows "((a::int) - a mod b) mod b = 0"
  using b minus_mod_eq_mult_div [symmetric, of b a, symmetric]
  by simp

lemma div_abs_eq:
  assumes mod: "(a::int) mod b = 0"
  and b: "0 < b"
  shows "\<bar>a div b\<bar> = \<bar>a\<bar> div b"
proof (cases "0 \<le> a")
  case True with pos_imp_zdiv_nonneg_iff [OF b]
  show ?thesis by auto
next
  from b have "b \<noteq> 0" by auto
  case False
  then have "a < 0" by auto
  have "\<bar>a div b\<bar> = - (a div b)"
    by (simp add: div_neg_pos_less0 [OF \<open>a < 0\<close> b] zabs_def)
  with abs_of_neg [OF \<open>a < 0\<close>] zdiv_zminus1_eq_if [OF \<open>b \<noteq> 0\<close>] mod
  show ?thesis by simp
qed

lemma add_div_trivial: "0 \<le> c \<Longrightarrow> c < b \<Longrightarrow> ((a::int) * b + c) div b = a"
  by (simp add: div_add1_eq div_pos_pos_trivial)

lemma dioph_rhs_bound:
  "\<bar>(l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2\<bar> \<le> max \<bar>l\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>)"
proof -
  have "\<bar>(l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2\<bar> =
    \<bar>(l - eval_dioph ks (map (\<lambda>x. x mod 2) xs) -
     (l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) mod 2) div 2\<bar>"
    (is "_ = \<bar>(_ - ?r) div 2\<bar>")
    by (simp add: zmult_div_aux1)
  also have "\<dots> = \<bar>l - eval_dioph ks (map (\<lambda>x. x mod 2) xs) - ?r\<bar> div 2"
    by (simp add: zmult_div_aux2 div_abs_eq)
  also have "\<bar>l - eval_dioph ks (map (\<lambda>x. x mod 2) xs) - ?r\<bar> \<le>
    \<bar>l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)\<bar> + \<bar>?r\<bar>"
    by (rule abs_triangle_ineq4)
  also have "\<bar>l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)\<bar> \<le>
    \<bar>l\<bar> + \<bar>eval_dioph ks (map (\<lambda>x. x mod 2) xs)\<bar>"
    by (rule abs_triangle_ineq4)
  also have "\<bar>eval_dioph ks (map (\<lambda>x. x mod 2) xs)\<bar> \<le> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>)"
  proof (induct ks xs rule: eval_dioph.induct)
    case (1 k ks x xs)
    have "\<bar>k * int (x mod 2) + eval_dioph ks (map (\<lambda>x. x mod 2) xs)\<bar> \<le>
      \<bar>k * int (x mod 2)\<bar> + \<bar>eval_dioph ks (map (\<lambda>x. x mod 2) xs)\<bar>"
      by (rule abs_triangle_ineq)
    also have "\<bar>k * int (x mod 2)\<bar> \<le> \<bar>k\<bar> * \<bar>int (x mod 2)\<bar>"
      by (simp add: abs_mult)
    also have "\<bar>int (x mod 2)\<bar> \<le> 1" by simp
    finally have "\<bar>k * int (x mod 2) + eval_dioph ks (map (\<lambda>x. x mod 2) xs)\<bar> \<le>
      \<bar>k\<bar> + \<bar>eval_dioph ks (map (\<lambda>x. x mod 2) xs)\<bar>"
      by (auto simp add: mult_left_mono)
    with 1 show ?case by simp
  qed (simp_all add: sum_list_abs_ge_0)
  finally have ineq: "\<bar>(l - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2\<bar> \<le>
    (\<bar>l\<bar> + (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) + \<bar>?r\<bar>) div 2"
    by (simp add: zdiv_mono1)
  show ?thesis
  proof (cases "(\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) \<le> \<bar>l\<bar>")
    case True
    note ineq
    also from True
    have "(\<bar>l\<bar> + (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) + \<bar>?r\<bar>) div 2 \<le> (\<bar>l\<bar> * 2 + \<bar>?r\<bar>) div 2"
      by (simp add: zdiv_mono1)
    also have "\<dots> = \<bar>l\<bar>"
      by (simp add: add_div_trivial)
    finally show ?thesis by simp
  next
    case False
    note ineq
    also from False
    have "(\<bar>l\<bar> + (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) + \<bar>?r\<bar>) div 2 \<le> ((\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) * 2 + \<bar>?r\<bar>) div 2"
      by (simp add: zdiv_mono1)
    also have "\<dots> = (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>)"
      by (simp add: add_div_trivial)
    finally show ?thesis by simp
  qed
qed

lemma dioph_rhs_invariant:
  assumes m: "\<bar>m\<bar> \<le> max \<bar>l\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>)"
  shows "\<bar>(m - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2\<bar> \<le> max \<bar>l\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>)"
proof (cases "(\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) \<le> \<bar>l\<bar>")
  case True
  have "\<bar>(m - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2\<bar> \<le> max \<bar>m\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>)"
    by (rule dioph_rhs_bound)
  also from True m have "\<bar>m\<bar> \<le> \<bar>l\<bar>" by simp
  finally show ?thesis by simp
next
  case False
  have "\<bar>(m - eval_dioph ks (map (\<lambda>x. x mod 2) xs)) div 2\<bar> \<le> max \<bar>m\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>)"
    by (rule dioph_rhs_bound)
  also from False m have "\<bar>m\<bar> \<le> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>)" by simp
  also have "max (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) \<le> max \<bar>l\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>)"
    by simp
  finally show ?thesis by simp
qed

lemma bounded_int_set_is_finite:
  assumes S: "\<forall>(i::int)\<in>S. \<bar>i\<bar> < j"
  shows "finite S"
proof (rule finite_subset)
  have "finite (int ` {n. n < nat j})"
    by (rule nat_seg_image_imp_finite [OF refl])
  moreover have "finite ((\<lambda>n. - int n) ` {n. n < nat j})"
    by (rule nat_seg_image_imp_finite [OF refl])
  ultimately show "finite (int ` {n. n < nat j} \<union> (\<lambda>n. - int n) ` {n. n < nat j})"
    by (rule finite_UnI)
  show "S \<subseteq> int ` {n. n < nat j} \<union> (\<lambda>n. - int n) ` {n. n < nat j}"
  proof
    fix i
    assume i: "i \<in> S"
    show "i \<in> int ` {n. n < nat j} \<union> (\<lambda>n. - int n) ` {n. n < nat j}"
    proof (cases "0 \<le> i")
      case True
      then have "i = int (nat i)" by simp
      moreover from i S have "nat i \<in> {n. n < nat j}"
        by auto
      ultimately have "i \<in> int ` {n. n < nat j}"
        by (rule image_eqI)
      then show ?thesis ..
    next
      case False
      then have "i = - int (nat (- i))" by simp
      moreover from i S have "nat (- i) \<in> {n. n < nat j}"
        by auto
      ultimately have "i \<in> (\<lambda>n. - int n) ` {n. n < nat j}"
        by (rule image_eqI)
      then show ?thesis ..
    qed
  qed
qed

primrec mk_nat_vecs :: "nat \<Rightarrow> nat list list" where
  "mk_nat_vecs 0 = [[]]"
| "mk_nat_vecs (Suc n) =
     (let yss = mk_nat_vecs n
      in map (Cons 0) yss @ map (Cons 1) yss)"

lemma mk_nat_vecs_bound: "\<forall>xs\<in>set (mk_nat_vecs n). \<forall>x\<in>set xs. x < 2"
  by (induct n) (auto simp add: Let_def)

lemma mk_nat_vecs_mod_eq: "xs \<in> set (mk_nat_vecs n) \<Longrightarrow> map (\<lambda>x. x mod 2) xs = xs"
  apply (drule bspec [OF mk_nat_vecs_bound])
  apply (induct xs)
  apply simp_all
  done

definition
  "dioph_succs n ks m = List.map_filter (\<lambda>xs.
     if eval_dioph ks xs mod 2 = m mod 2
     then Some ((m - eval_dioph ks xs) div 2)
     else None) (mk_nat_vecs n)"

definition
  dioph_is_node :: "int list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "dioph_is_node ks l m = (\<bar>m\<bar> \<le> max \<bar>l\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>))"

definition
  dioph_invariant :: "int list \<Rightarrow> int \<Rightarrow> nat option list \<times> int list \<Rightarrow> bool" where
  "dioph_invariant ks l = (\<lambda>(is, js). length is = nat (2 * max \<bar>l\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) + 1))"

definition
  "dioph_ins m = (\<lambda>(is, js). (is[int_encode m := Some (length js)], js @ [m]))"

definition
  dioph_memb :: "int \<Rightarrow> nat option list \<times> int list \<Rightarrow> bool" where
  "dioph_memb m = (\<lambda>(is, js). is ! int_encode m \<noteq> None)"

definition
  dioph_empt :: "int list \<Rightarrow> int \<Rightarrow> nat option list \<times> int list" where
  "dioph_empt ks l = (replicate (nat (2 * max \<bar>l\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) + 1)) None, [])"

lemma int_encode_bound: "dioph_is_node ks l m \<Longrightarrow>
  int_encode m < nat (2 * max \<bar>l\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) + 1)"
  by (simp add: dioph_is_node_def int_encode_def sum_encode_def) arith

interpretation dioph_dfs: DFS "dioph_succs n ks" "dioph_is_node ks l"
  "dioph_invariant ks l" dioph_ins dioph_memb "dioph_empt ks l"
proof (standard, goal_cases)
  case (1 x y)
  then show ?case
    apply (simp add: dioph_memb_def dioph_ins_def split_beta dioph_invariant_def)
    apply (cases "x = y")
    apply (simp add: int_encode_bound)
    apply (simp add: inj_eq [OF inj_int_encode])
    done
next
  case 2
  then show ?case
    by (simp add: dioph_memb_def dioph_empt_def int_encode_bound)
next
  case 3
  then show ?case
    apply (simp add: dioph_succs_def map_filter_def list_all_iff dioph_is_node_def)
    apply (rule allI impI)+
    apply (erule subst [OF mk_nat_vecs_mod_eq])
    apply (drule dioph_rhs_invariant)
    apply assumption
    done
next
  case 4
  then show ?case
    by (simp add: dioph_invariant_def dioph_empt_def)
next
  case 5
  then show ?case
    by (simp add: dioph_invariant_def dioph_ins_def split_beta)
next
  case 6
  then show ?case
    apply (rule bounded_int_set_is_finite [of _ "max \<bar>l\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) + 1"])
    apply (rule ballI)
    apply (simp add: dioph_is_node_def)
    done
qed

definition
  "dioph_dfs n ks l = gen_dfs (dioph_succs n ks) dioph_ins dioph_memb (dioph_empt ks l) [l]"

primrec make_bdd :: "(nat list \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a bdd"
where
  "make_bdd f 0 xs = Leaf (f xs)"
| "make_bdd f (Suc n) xs = Branch (make_bdd f n (xs @ [0])) (make_bdd f n (xs @ [1]))"

definition
  "eq_dfa n ks l =
    (let (is, js) = dioph_dfs n ks l
     in
       (map (\<lambda>j. make_bdd (\<lambda>xs.
          if eval_dioph ks xs mod 2 = j mod 2
          then the (is ! int_encode ((j - eval_dioph ks xs) div 2))
          else length js) n []) js @ [Leaf (length js)],
        map (\<lambda>j. j = 0) js @ [False]))"

abbreviation (input) nat_of_bool :: "bool \<Rightarrow> nat"
where
  "nat_of_bool \<equiv> of_bool"

lemma nat_of_bool_bound: "nat_of_bool b < 2"
  by (cases b) simp_all

lemma nat_of_bool_mk_nat_vecs:
  "length bs = n \<Longrightarrow> map nat_of_bool bs \<in> set (mk_nat_vecs n)"
  apply (induct n arbitrary: bs)
  apply simp
  apply (case_tac bs)
  apply simp
  apply (case_tac a)
  apply (simp_all add: Let_def)
  done

lemma bdd_lookup_make_bdd:
  "length bs = n \<Longrightarrow> bdd_lookup (make_bdd f n xs) bs = f (xs @ map nat_of_bool bs)"
  apply (induct n arbitrary: bs xs)
  apply simp
  apply (case_tac bs)
  apply auto
  done

primrec nat_of_bools :: "bool list \<Rightarrow> nat"
where
  "nat_of_bools [] = 0"
| "nat_of_bools (b # bs) = nat_of_bool b + 2 * nat_of_bools bs"

primrec nats_of_boolss :: "nat \<Rightarrow> bool list list \<Rightarrow> nat list"
where
  Nil: "nats_of_boolss n [] = replicate n 0"
| Cons: "nats_of_boolss n (bs # bss) =
     map (\<lambda>(b, x). nat_of_bool b + 2 * x) (zip bs (nats_of_boolss n bss))"

lemma nats_of_boolss_length:
  "list_all (is_alph n) bss \<Longrightarrow> length (nats_of_boolss n bss) = n"
  by (induct bss) (simp_all add: is_alph_def)

lemma nats_of_boolss_mod2:
  assumes bs: "length bs = n" and bss: "list_all (is_alph n) bss"
  shows "map (\<lambda>x. x mod 2) (nats_of_boolss n (bs # bss)) = map nat_of_bool bs"
proof -
  from bs bss
  have "map nat_of_bool (map fst (zip bs (nats_of_boolss n bss))) = map nat_of_bool bs"
    by (simp add: nats_of_boolss_length)
  then show ?thesis
    by (simp add: split_def o_def nat_of_bool_bound)
qed

lemma nats_of_boolss_div2:
  assumes bs: "length bs = n" and bss: "list_all (is_alph n) bss"
  shows "map (\<lambda>x. x div 2) (nats_of_boolss n (bs # bss)) = nats_of_boolss n bss"
  using bs bss
  by (simp add: split_def o_def nat_of_bool_bound nats_of_boolss_length)

lemma zip_insertl: "length xs = length ys \<Longrightarrow>
  zip (insertl n x xs) (insertl n y ys) = insertl n (x, y) (zip xs ys)"
  by (induct n x xs arbitrary: ys rule: insertl.induct)
    (auto simp add: Suc_length_conv)

lemma map_insertl: "map f (insertl i x xs) = insertl i (f x) (map f xs)"
  by (induct i x xs rule: insertl.induct) simp_all

lemma insertl_replicate: "m \<le> n \<Longrightarrow>
  insertl m x (replicate n x) = x # replicate n x"
  apply (induct n arbitrary: m)
  apply simp
  apply (case_tac m)
  apply simp_all
  done

lemma nats_of_boolss_insertll:
  "list_all (is_alph n) bss \<Longrightarrow> length bs = length bss \<Longrightarrow> i \<le> n \<Longrightarrow>
   nats_of_boolss (Suc n) (insertll i bs bss) = insertl i (nat_of_bools bs) (nats_of_boolss n bss)"
  by (induct i bs bss rule: insertll.induct)
    (simp_all add: zip_insertl nats_of_boolss_length insertll_len2 is_alph_def
     map_insertl insertl_replicate cong: conj_cong)

lemma zip_replicate_map: "length xs = n \<Longrightarrow> zip (replicate n x) xs = map (Pair x) xs"
  apply (induct n arbitrary: xs)
  apply simp
  apply (case_tac xs)
  apply simp_all
  done

lemma zip_replicate_mapr: "length xs = n \<Longrightarrow> zip xs (replicate n x) = map (\<lambda>y. (y, x)) xs"
  apply (induct n arbitrary: xs)
  apply simp
  apply (case_tac xs)
  apply simp_all
  done

lemma zip_assoc: "map f (zip xs (zip ys zs)) = map (\<lambda>((x, y), z). f (x, (y, z))) (zip (zip xs ys) zs)"
  apply (induct xs arbitrary: ys zs)
  apply simp
  apply (case_tac ys)
  apply simp
  apply (case_tac zs)
  apply simp_all
  done

lemma nats_of_boolss_append:
  "list_all (is_alph n) bss \<Longrightarrow> list_all (is_alph n) bss' \<Longrightarrow>
     nats_of_boolss n (bss @ bss') =
     map (\<lambda>(x, y). x + 2 ^ length bss * y) (zip (nats_of_boolss n bss) (nats_of_boolss n bss'))"
  by (induct bss)
    (auto simp add: nats_of_boolss_length zip_replicate_map o_def
     map_zip_map map_zip_map2 zip_assoc is_alph_def)

lemma nats_of_boolss_zeros: "nats_of_boolss n (zeros m n) = replicate n 0"
  by (induct m) (simp_all add: zeros_def)

declare nats_of_boolss.Cons [simp del]

fun bools_of_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool list"
where
  "bools_of_nat k n =
     (if n = 0 then
        (if k = 0 then [] else False # bools_of_nat (k - 1) n)
      else (n mod 2 = 1) # bools_of_nat (k - 1) (n div 2))"

lemma bools_of_nat_length: "k \<le> length (bools_of_nat k n)"
  apply (induct k n rule: bools_of_nat.induct)
  apply (case_tac "n = 0")
  apply (case_tac "k = 0")
  apply simp
  apply simp
  apply (subst bools_of_nat.simps)
  apply (simp del: bools_of_nat.simps)
  done

lemma nat_of_bool_mod_eq: "nat_of_bool (n mod 2 = 1) = n mod 2"
  by (cases "n mod 2 = 1") simp_all

lemma bools_of_nat_inverse: "nat_of_bools (bools_of_nat k n) = n"
  apply (induct k n rule: bools_of_nat.induct)
  apply (case_tac "n = 0")
  apply (case_tac "k = 0")
  apply simp
  apply simp
  apply (subst bools_of_nat.simps)
  apply (simp add: nat_of_bool_mod_eq [simplified] del: bools_of_nat.simps)
  done

declare bools_of_nat.simps [simp del]

lemma eval_dioph_replicate_0: "eval_dioph ks (replicate n 0) = 0"
  apply (induct n arbitrary: ks)
  apply simp
  apply (case_tac ks)
  apply simp_all
  done

lemma dioph_dfs_bij:
  "(fst (dioph_dfs n ks l) ! int_encode i = Some k \<and> dioph_is_node ks l i) =
    (k < length (snd (dioph_dfs n ks l)) \<and> (snd (dioph_dfs n ks l) ! k = i))"
proof -
  let ?dfs = "gen_dfs (dioph_succs n ks) dioph_ins dioph_memb (dioph_empt ks l) [l]"
  have "list_all (dioph_is_node ks l) [l]"
    by (simp add: dioph_is_node_def)
  with dioph_dfs.empt_invariant [of ks l]
  have "(fst ?dfs ! int_encode i = Some k \<and> dioph_is_node ks l i) =
    (k < length (snd ?dfs) \<and> (snd ?dfs ! k = i))"
  proof (induct rule: dioph_dfs.dfs_invariant)
    case base
    show ?case
      by (auto simp add: dioph_empt_def dioph_is_node_def int_encode_bound)
  next
    case (step S y)
    then show ?case
      by (cases "y = i")
        (auto simp add: dioph_ins_def dioph_memb_def dioph_is_node_def split_beta dioph_invariant_def
          int_encode_bound nth_append inj_eq [OF inj_int_encode])
  qed
  then show ?thesis by (simp add: dioph_dfs_def)
qed

lemma dioph_dfs_mono:
  assumes z: "dioph_invariant ks l z"
  and xs: "list_all (dioph_is_node ks l) xs"
  and H: "fst z ! i = Some k"
  shows "fst (gen_dfs (dioph_succs n ks) dioph_ins dioph_memb z xs) ! i = Some k"
  using z xs H
  apply (rule dioph_dfs.dfs_invariant)
  apply (simp add: dioph_ins_def dioph_memb_def split_paired_all)
  apply (case_tac "i = int_encode x")
  apply simp_all
  done

lemma dioph_dfs_start:
  "fst (dioph_dfs n ks l) ! int_encode l = Some 0"
  apply (simp add: dioph_dfs_def gen_dfs_simps dioph_dfs.empt dioph_is_node_def)
  apply (rule dioph_dfs_mono [of _ l])
  apply (rule dioph_dfs.ins_invariant)
  apply (simp add: dioph_is_node_def)
  apply (rule dioph_dfs.empt_invariant)
  apply (simp add: dioph_dfs.empt dioph_is_node_def)
  apply (simp add: dioph_dfs.succs_is_node dioph_is_node_def)
  apply (simp add: dioph_ins_def dioph_empt_def int_encode_bound dioph_is_node_def)
  done

lemma eq_dfa_error: "\<not> dfa_accepting (eq_dfa n ks l) (dfa_steps (eq_dfa n ks l) (length (snd (dioph_dfs n ks l))) bss)"
  apply (induct bss)
  apply (simp add: eq_dfa_def split_beta dfa_accepting_def nth_append)
  apply (simp add: eq_dfa_def split_beta nth_append dfa_trans_def)
  done

lemma eq_dfa_accepting:
  "(l, m) \<in> (succsr (dioph_succs n ks))\<^sup>* \<Longrightarrow> list_all (is_alph n) bss \<Longrightarrow>
  dfa_accepting (eq_dfa n ks l) (dfa_steps (eq_dfa n ks l) (the (fst (dioph_dfs n ks l) ! int_encode m)) bss) =
  (eval_dioph ks (nats_of_boolss n bss) = m)"
proof (induct bss arbitrary: m)
  case Nil
  have l: "dioph_is_node ks l l"
    by (simp add: dioph_is_node_def)
  with \<open>(l, m) \<in> (succsr (dioph_succs n ks))\<^sup>*\<close>
  have m: "dioph_is_node ks l m"
    by (rule dioph_dfs.succsr_is_node)
  with l Nil
  have "dioph_memb m (dioph_dfs n ks l)"
    by (simp add: dioph_dfs.dfs_eq_rtrancl dioph_dfs_def)
  then obtain k where k: "fst (dioph_dfs n ks l) ! int_encode m = Some k"
    by (auto simp add: dioph_memb_def)
  with m have "k < length (snd (dioph_dfs n ks l)) \<and> (snd (dioph_dfs n ks l) ! k = m)"
    by (simp add: dioph_dfs_bij [symmetric])
  with k show ?case
    by (simp add: eval_dioph_replicate_0 dfa_accepting_def eq_dfa_def split_beta nth_append)
next
  case (Cons bs bss)
  have l: "dioph_is_node ks l l"
    by (simp add: dioph_is_node_def)
  with \<open>(l, m) \<in> (succsr (dioph_succs n ks))\<^sup>*\<close>
  have m: "dioph_is_node ks l m"
    by (rule dioph_dfs.succsr_is_node)
  with l Cons
  have "dioph_memb m (dioph_dfs n ks l)"
    by (simp add: dioph_dfs.dfs_eq_rtrancl dioph_dfs_def)
  then obtain k where k: "fst (dioph_dfs n ks l) ! int_encode m = Some k"
    by (auto simp add: dioph_memb_def)
  with m have k': "k < length (snd (dioph_dfs n ks l)) \<and> (snd (dioph_dfs n ks l) ! k = m)"
    by (simp add: dioph_dfs_bij [symmetric])
  show ?case
  proof (cases "eval_dioph ks (map nat_of_bool bs) mod 2 = m mod 2")
    case True
    with k' Cons
    have "bdd_lookup (fst (eq_dfa n ks l) ! k) bs =
      the (fst (dioph_dfs n ks l) ! int_encode ((m - eval_dioph ks (map nat_of_bool bs)) div 2))"
      by (simp add: eq_dfa_def split_beta nth_append bdd_lookup_make_bdd is_alph_def)
    moreover have "(l, (m - eval_dioph ks (map nat_of_bool bs)) div 2) \<in> (succsr (dioph_succs n ks))\<^sup>*"
      apply (rule rtrancl_into_rtrancl)
      apply (rule Cons)
      apply (simp add: dioph_succs_def succsr_def map_filter_def)
      apply (rule image_eqI [of _ _ "map nat_of_bool bs"])
      using Cons
      apply (simp_all add: True nat_of_bool_mk_nat_vecs is_alph_def)
      done
    ultimately show ?thesis using True k k' Cons
      by (subst eval_dioph_div_mod)
        (simp add: nats_of_boolss_div2 nats_of_boolss_mod2 is_alph_def dfa_trans_def [abs_def])
  next
    case False
    with k' Cons
    have "bdd_lookup (fst (eq_dfa n ks l) ! k) bs = length (snd (dioph_dfs n ks l))"
      by (simp add: eq_dfa_def split_beta nth_append bdd_lookup_make_bdd is_alph_def)
    with False k k' Cons show ?thesis
      by (subst eval_dioph_div_mod)
        (simp add: nats_of_boolss_div2 nats_of_boolss_mod2 is_alph_def
         dfa_trans_def eq_dfa_error)
  qed
qed

lemma eq_dfa_accepts:
  assumes bss: "list_all (is_alph n) bss"
  shows "dfa_accepts (eq_dfa n ks l) bss = (eval_dioph ks (nats_of_boolss n bss) = l)"
  by (simp add: accepts_def)
    (rule eq_dfa_accepting [of l l n ks, OF _ bss, simplified dioph_dfs_start, simplified])

lemma bddh_make_bdd: "bddh n (make_bdd f n xs)"
  by (induct n arbitrary: xs) simp_all

lemma bdd_all_make_bdd: "bdd_all P (make_bdd f n xs) = (\<forall>ys\<in>set (mk_nat_vecs n). P (f (xs @ ys)))"
  by (induct n arbitrary: xs) (auto simp add: Let_def)

lemma eq_wf_dfa: "wf_dfa (eq_dfa n ks l) n"
proof -
  have "\<forall>x\<in>set (snd (dioph_dfs n ks l)). \<forall>ys\<in>set (mk_nat_vecs n).
    eval_dioph ks ys mod 2 = x mod 2 \<longrightarrow>
      the (fst (dioph_dfs n ks l) ! int_encode ((x - eval_dioph ks ys) div 2)) <
        Suc (length (snd (dioph_dfs n ks l)))"
  proof (intro ballI impI)
    fix x ys
    assume x: "x \<in> set (snd (dioph_dfs n ks l))"
    and ys: "ys \<in> set (mk_nat_vecs n)"
    and ys': "eval_dioph ks ys mod 2 = x mod 2"
    from x obtain k where k: "fst (dioph_dfs n ks l) ! int_encode x = Some k"
      and k': "dioph_is_node ks l x"
      by (auto simp add: in_set_conv_nth dioph_dfs_bij [symmetric])
    from k have "dioph_memb x (dioph_dfs n ks l)"
      by (simp add: dioph_memb_def split_beta)
    moreover have ll: "dioph_is_node ks l l"
      by (simp add: dioph_is_node_def)
    ultimately have "(l, x) \<in> (succsr (dioph_succs n ks))\<^sup>*" using k'
      by (simp add: dioph_dfs.dfs_eq_rtrancl dioph_dfs_def)
    then have "(l, (x - eval_dioph ks ys) div 2) \<in> (succsr (dioph_succs n ks))\<^sup>*"
      apply (rule rtrancl_into_rtrancl)
      apply (simp add: succsr_def dioph_succs_def map_filter_def)
      apply (rule image_eqI [of _ _ ys])
      apply (simp_all add: ys ys')
      done
    moreover from dioph_dfs.succs_is_node [OF k', of n] ys ys'
    have x': "dioph_is_node ks l ((x - eval_dioph ks ys) div 2)"
      by (auto simp add: dioph_succs_def map_filter_def list_all_iff)
    ultimately have "dioph_memb ((x - eval_dioph ks ys) div 2) (dioph_dfs n ks l)"
      by (simp add: dioph_dfs.dfs_eq_rtrancl dioph_dfs_def ll)
    then obtain k' where k': "fst (dioph_dfs n ks l) !
      int_encode ((x - eval_dioph ks ys) div 2) = Some k'"
      by (auto simp add: dioph_memb_def)
    with x' have "k' < length (snd (dioph_dfs n ks l)) \<and>
      snd (dioph_dfs n ks l) ! k' = ((x - eval_dioph ks ys) div 2)"
      by (simp add: dioph_dfs_bij [symmetric])
    with k'
    show "the (fst (dioph_dfs n ks l) ! int_encode ((x - eval_dioph ks ys) div 2)) <
      Suc (length (snd (dioph_dfs n ks l)))"
      by simp
  qed
  then show ?thesis
    by (simp add: eq_dfa_def split_beta wf_dfa_def dfa_is_node_def list_all_iff
      bddh_make_bdd bdd_all_make_bdd)
qed


subsection \<open>Diophantine Inequations\<close>

definition
  "dioph_ineq_succs n ks m = map (\<lambda>xs.
     (m - eval_dioph ks xs) div 2) (mk_nat_vecs n)"

interpretation dioph_ineq_dfs: DFS "dioph_ineq_succs n ks" "dioph_is_node ks l"
  "dioph_invariant ks l" dioph_ins dioph_memb "dioph_empt ks l"
proof (standard, goal_cases)
  case (1 x y)
  then show ?case
    apply (simp add: dioph_memb_def dioph_ins_def split_beta dioph_invariant_def)
    apply (cases "x = y")
    apply (simp add: int_encode_bound)
    apply (simp add: inj_eq [OF inj_int_encode])
    done
next
  case 2
  then show ?case
    by (simp add: dioph_memb_def dioph_empt_def int_encode_bound)
next
  case 3
  then show ?case
    apply (simp add: dioph_ineq_succs_def map_filter_def list_all_iff dioph_is_node_def)
    apply (rule ballI)
    apply (erule subst [OF mk_nat_vecs_mod_eq])
    apply (drule dioph_rhs_invariant)
    apply assumption
    done
next
  case 4
  then show ?case
    by (simp add: dioph_invariant_def dioph_empt_def)
next
  case 5
  then show ?case
    by (simp add: dioph_invariant_def dioph_ins_def split_beta)
next
  case 6
  then show ?case
    apply (rule bounded_int_set_is_finite [of _ "max \<bar>l\<bar> (\<Sum>k\<leftarrow>ks. \<bar>k\<bar>) + 1"])
    apply (rule ballI)
    apply (simp add: dioph_is_node_def)
    done
qed

definition
  "dioph_ineq_dfs n ks l = gen_dfs (dioph_ineq_succs n ks) dioph_ins dioph_memb (dioph_empt ks l) [l]"

definition
  "ineq_dfa n ks l =
    (let (is, js) = dioph_ineq_dfs n ks l
     in
       (map (\<lambda>j. make_bdd (\<lambda>xs.
          the (is ! int_encode ((j - eval_dioph ks xs) div 2))) n []) js,
        map (\<lambda>j. 0 \<le> j) js))"

lemma dioph_ineq_dfs_bij:
  "(fst (dioph_ineq_dfs n ks l) ! int_encode i = Some k \<and> dioph_is_node ks l i) =
    (k < length (snd (dioph_ineq_dfs n ks l)) \<and> (snd (dioph_ineq_dfs n ks l) ! k = i))"
proof -
  let ?dfs = "gen_dfs (dioph_ineq_succs n ks) dioph_ins dioph_memb (dioph_empt ks l) [l]"
  have "list_all (dioph_is_node ks l) [l]"
    by (simp add: dioph_is_node_def)
  with dioph_dfs.empt_invariant [of ks l]
  have "(fst ?dfs ! int_encode i = Some k \<and> dioph_is_node ks l i) =
    (k < length (snd ?dfs) \<and> (snd ?dfs ! k = i))"
  proof (induct rule: dioph_ineq_dfs.dfs_invariant)
    case base
    show ?case
      by (auto simp add: dioph_empt_def dioph_is_node_def int_encode_bound)
  next
    case (step S y)
    then show ?case
      by (cases "y = i")
        (auto simp add: dioph_ins_def dioph_memb_def dioph_is_node_def split_beta dioph_invariant_def
          int_encode_bound nth_append inj_eq [OF inj_int_encode])
  qed
  then show ?thesis by (simp add: dioph_ineq_dfs_def)
qed

lemma dioph_ineq_dfs_mono:
  assumes z: "dioph_invariant ks l z"
  and xs: "list_all (dioph_is_node ks l) xs"
  and H: "fst z ! i = Some k"
  shows "fst (gen_dfs (dioph_ineq_succs n ks) dioph_ins dioph_memb z xs) ! i = Some k"
  using z xs H
  apply (rule dioph_ineq_dfs.dfs_invariant)
  apply (simp add: dioph_ins_def dioph_memb_def split_paired_all)
  apply (case_tac "i = int_encode x")
  apply simp_all
  done

lemma dioph_ineq_dfs_start:
  "fst (dioph_ineq_dfs n ks l) ! int_encode l = Some 0"
  apply (simp add: dioph_ineq_dfs_def gen_dfs_simps dioph_ineq_dfs.empt dioph_is_node_def)
  apply (rule dioph_ineq_dfs_mono [of _ l])
  apply (rule dioph_ineq_dfs.ins_invariant)
  apply (simp add: dioph_is_node_def)
  apply (rule dioph_ineq_dfs.empt_invariant)
  apply (simp add: dioph_ineq_dfs.empt dioph_is_node_def)
  apply (simp add: dioph_ineq_dfs.succs_is_node dioph_is_node_def)
  apply (simp add: dioph_ins_def dioph_empt_def int_encode_bound dioph_is_node_def)
  done

lemma ineq_dfa_accepting:
  "(l, m) \<in> (succsr (dioph_ineq_succs n ks))\<^sup>* \<Longrightarrow> list_all (is_alph n) bss \<Longrightarrow>
  dfa_accepting (ineq_dfa n ks l) (dfa_steps (ineq_dfa n ks l) (the (fst (dioph_ineq_dfs n ks l) ! int_encode m)) bss) =
  (eval_dioph ks (nats_of_boolss n bss) \<le> m)"
proof (induct bss arbitrary: m)
  case Nil
  have l: "dioph_is_node ks l l"
    by (simp add: dioph_is_node_def)
  with \<open>(l, m) \<in> (succsr (dioph_ineq_succs n ks))\<^sup>*\<close>
  have m: "dioph_is_node ks l m"
    by (rule dioph_ineq_dfs.succsr_is_node)
  with l Nil
  have "dioph_memb m (dioph_ineq_dfs n ks l)"
    by (simp add: dioph_ineq_dfs.dfs_eq_rtrancl dioph_ineq_dfs_def)
  then obtain k where k: "fst (dioph_ineq_dfs n ks l) ! int_encode m = Some k"
    by (auto simp add: dioph_memb_def)
  with m have "k < length (snd (dioph_ineq_dfs n ks l)) \<and> (snd (dioph_ineq_dfs n ks l) ! k = m)"
    by (simp add: dioph_ineq_dfs_bij [symmetric])
  with k show ?case
    by (simp add: eval_dioph_replicate_0 dfa_accepting_def ineq_dfa_def split_beta nth_append)
next
  case (Cons bs bss)
  have l: "dioph_is_node ks l l"
    by (simp add: dioph_is_node_def)
  with \<open>(l, m) \<in> (succsr (dioph_ineq_succs n ks))\<^sup>*\<close>
  have m: "dioph_is_node ks l m"
    by (rule dioph_ineq_dfs.succsr_is_node)
  with l Cons
  have "dioph_memb m (dioph_ineq_dfs n ks l)"
    by (simp add: dioph_ineq_dfs.dfs_eq_rtrancl dioph_ineq_dfs_def)
  then obtain k where k: "fst (dioph_ineq_dfs n ks l) ! int_encode m = Some k"
    by (auto simp add: dioph_memb_def)
  with m have k': "k < length (snd (dioph_ineq_dfs n ks l)) \<and> (snd (dioph_ineq_dfs n ks l) ! k = m)"
    by (simp add: dioph_ineq_dfs_bij [symmetric])
  moreover with Cons have "bdd_lookup (fst (ineq_dfa n ks l) ! k) bs =
    the (fst (dioph_ineq_dfs n ks l) ! int_encode ((m - eval_dioph ks (map nat_of_bool bs)) div 2))"
    by (simp add: ineq_dfa_def split_beta nth_append bdd_lookup_make_bdd is_alph_def)
  moreover have "(l, (m - eval_dioph ks (map nat_of_bool bs)) div 2) \<in> (succsr (dioph_ineq_succs n ks))\<^sup>*"
    apply (rule rtrancl_into_rtrancl)
    apply (rule Cons)
    apply (simp add: dioph_ineq_succs_def succsr_def)
    apply (rule image_eqI [of _ _ "map nat_of_bool bs"])
    using Cons
    apply (simp_all add: nat_of_bool_mk_nat_vecs is_alph_def)
    done
  ultimately show ?case using k Cons
    by (subst eval_dioph_ineq_div_mod)
      (simp add: nats_of_boolss_div2 nats_of_boolss_mod2 is_alph_def dfa_trans_def [abs_def])
qed

lemma ineq_dfa_accepts:
  assumes bss: "list_all (is_alph n) bss"
  shows "dfa_accepts (ineq_dfa n ks l) bss = (eval_dioph ks (nats_of_boolss n bss) \<le> l)"
  by (simp add: accepts_def)
    (rule ineq_dfa_accepting [of l l n ks, OF _ bss, simplified dioph_ineq_dfs_start, simplified])

lemma ineq_wf_dfa: "wf_dfa (ineq_dfa n ks l) n"
proof -
  have "\<forall>x\<in>set (snd (dioph_ineq_dfs n ks l)). \<forall>ys\<in>set (mk_nat_vecs n).
    the (fst (dioph_ineq_dfs n ks l) ! int_encode ((x - eval_dioph ks ys) div 2)) <
      length (snd (dioph_ineq_dfs n ks l))"
  proof (intro ballI impI)
    fix x ys
    assume x: "x \<in> set (snd (dioph_ineq_dfs n ks l))"
    and ys: "ys \<in> set (mk_nat_vecs n)"
    from x obtain k where k: "fst (dioph_ineq_dfs n ks l) ! int_encode x = Some k"
      and k': "dioph_is_node ks l x"
      by (auto simp add: in_set_conv_nth dioph_ineq_dfs_bij [symmetric])
    from k have "dioph_memb x (dioph_ineq_dfs n ks l)"
      by (simp add: dioph_memb_def split_beta)
    moreover have ll: "dioph_is_node ks l l"
      by (simp add: dioph_is_node_def)
    ultimately have "(l, x) \<in> (succsr (dioph_ineq_succs n ks))\<^sup>*" using k'
      by (simp add: dioph_ineq_dfs.dfs_eq_rtrancl dioph_ineq_dfs_def)
    then have "(l, (x - eval_dioph ks ys) div 2) \<in> (succsr (dioph_ineq_succs n ks))\<^sup>*"
      apply (rule rtrancl_into_rtrancl)
      apply (simp add: succsr_def dioph_ineq_succs_def)
      apply (rule image_eqI [of _ _ ys])
      apply (simp_all add: ys)
      done
    moreover from dioph_ineq_dfs.succs_is_node [OF k', of n] ys
    have x': "dioph_is_node ks l ((x - eval_dioph ks ys) div 2)"
      by (simp add: dioph_ineq_succs_def list_all_iff)
    ultimately have "dioph_memb ((x - eval_dioph ks ys) div 2) (dioph_ineq_dfs n ks l)"
      by (simp add: dioph_ineq_dfs.dfs_eq_rtrancl dioph_ineq_dfs_def ll)
    then obtain k' where k': "fst (dioph_ineq_dfs n ks l) !
      int_encode ((x - eval_dioph ks ys) div 2) = Some k'"
      by (auto simp add: dioph_memb_def)
    with x' have "k' < length (snd (dioph_ineq_dfs n ks l)) \<and>
      snd (dioph_ineq_dfs n ks l) ! k' = ((x - eval_dioph ks ys) div 2)"
      by (simp add: dioph_ineq_dfs_bij [symmetric])
    with k'
    show "the (fst (dioph_ineq_dfs n ks l) ! int_encode ((x - eval_dioph ks ys) div 2)) <
      length (snd (dioph_ineq_dfs n ks l))"
      by simp
  qed
  moreover have "fst (dioph_ineq_dfs n ks l) ! int_encode l = Some 0 \<and> dioph_is_node ks l l"
    by (simp add: dioph_ineq_dfs_start dioph_is_node_def)
  then have "snd (dioph_ineq_dfs n ks l) \<noteq> []"
    by (simp add: dioph_ineq_dfs_bij)
  ultimately show ?thesis
    by (simp add: ineq_dfa_def split_beta wf_dfa_def dfa_is_node_def list_all_iff
      bddh_make_bdd bdd_all_make_bdd)
qed


section \<open>Presburger Arithmetic\<close>

datatype pf =
    Eq "int list" int
  | Le "int list" int
  | And pf pf
  | Or pf pf
  | Imp pf pf
  | Forall pf
  | Exist pf
  | Neg pf

type_synonym passign = "nat list"

primrec eval_pf :: "pf \<Rightarrow> passign \<Rightarrow> bool"
where
  "eval_pf (Eq ks l) xs = (eval_dioph ks xs = l)"
| "eval_pf (Le ks l) xs = (eval_dioph ks xs \<le> l)"
| "eval_pf (And p q) xs = (eval_pf p xs \<and> eval_pf q xs)"
| "eval_pf (Or p q) xs = (eval_pf p xs \<or> eval_pf q xs)"
| "eval_pf (Imp p q) xs = (eval_pf p xs \<longrightarrow> eval_pf q xs)"
| "eval_pf (Forall p) xs = (\<forall>x. eval_pf p (x # xs))"
| "eval_pf (Exist p) xs = (\<exists>x. eval_pf p (x # xs))"
| "eval_pf (Neg p) xs = (\<not> eval_pf p xs)"

function dfa_of_pf :: "nat \<Rightarrow> pf \<Rightarrow> dfa"
where
  Eq: "dfa_of_pf n (Eq ks l) = eq_dfa n ks l"
| Le: "dfa_of_pf n (Le ks l) = ineq_dfa n ks l"
| And: "dfa_of_pf n (And p q) = and_dfa (dfa_of_pf n p) (dfa_of_pf n q)"
| Or: "dfa_of_pf n (Or p q) = or_dfa (dfa_of_pf n p) (dfa_of_pf n q)"
| Imp: "dfa_of_pf n (Imp p q) = imp_dfa (dfa_of_pf n p) (dfa_of_pf n q)"
| Exist: "dfa_of_pf n (Exist p) = rquot (det_nfa (quantify_nfa 0 (nfa_of_dfa (dfa_of_pf (Suc n) p)))) n"
| Forall: "dfa_of_pf n (Forall p) = dfa_of_pf n (Neg (Exist (Neg p)))"
| Neg: "dfa_of_pf n (Neg p) = negate_dfa (dfa_of_pf n p)"
  by pat_completeness auto

text \<open>Auxiliary measure function for termination proof\<close>

primrec count_forall :: "pf \<Rightarrow> nat"
where
  "count_forall (Eq ks l) = 0"
| "count_forall (Le ks l) = 0"
| "count_forall (And p q) = count_forall p + count_forall q"
| "count_forall (Or p q) = count_forall p + count_forall q"
| "count_forall (Imp p q) = count_forall p + count_forall q"
| "count_forall (Exist p) = count_forall p"
| "count_forall (Forall p) = 1 + count_forall p"
| "count_forall (Neg p) = count_forall p"

termination dfa_of_pf
  by (relation "measures [\<lambda>(n, pf). count_forall pf, \<lambda>(n, pf). size pf]") auto

lemmas dfa_of_pf_induct =
  dfa_of_pf.induct [case_names Eq Le And Or Imp Exist Forall Neg]

lemma dfa_of_pf_well_formed: "wf_dfa (dfa_of_pf n p) n"
proof (induct n p rule: dfa_of_pf_induct)
  case (Eq n ks l)
  show ?case by (simp add: eq_wf_dfa)
next
  case (Le n ks l)
  show ?case by (simp add: ineq_wf_dfa)
next
  case (And n p q)
  then show ?case by (simp add: and_wf_dfa)
next
  case (Or n p q)
  then show ?case by (simp add: or_wf_dfa)
next
  case (Imp n p q)
  then show ?case by (simp add: imp_wf_dfa)
next
  case (Neg n p)
  then show ?case by (simp add: negate_wf_dfa)
next
  case (Exist n p)
  then show ?case
    by (simp add: rquot_well_formed_aut det_wf_nfa quantify_nfa_well_formed_aut dfa2wf_nfa)
next
  case (Forall n p)
  then show ?case by simp
qed

lemma dfa_of_pf_correctness:
  "list_all (is_alph n) bss \<Longrightarrow>
     dfa_accepts (dfa_of_pf n p) bss = eval_pf p (nats_of_boolss n bss)"
proof (induct n p arbitrary: bss rule: dfa_of_pf_induct)
  case (Eq n ks l)
  then show ?case by (simp add: eq_dfa_accepts)
next
  case (Le n ks l)
  then show ?case by (simp add: ineq_dfa_accepts)
next
  case (And n p q)
  then show ?case by (simp add: and_dfa_accepts [of _ n] dfa_of_pf_well_formed)
next
  case (Or n p q)
  then show ?case by (simp add: or_dfa_accepts [of _ n] dfa_of_pf_well_formed)
next
  case (Imp n p q)
  then show ?case by (simp add: imp_dfa_accepts [of _ n] dfa_of_pf_well_formed)
next
  case (Neg n p)
  then show ?case by (simp add: dfa_accepts_negate [of _ n] dfa_of_pf_well_formed)
next
  case (Exist n p)
  have "(\<exists>k bs. eval_pf p (nat_of_bools bs # nats_of_boolss n bss) \<and> length bs = length bss + k) =
    (\<exists>x. eval_pf p (x # nats_of_boolss n bss))"
    apply (rule iffI)
    apply (erule exE conjE)+
    apply (erule exI)
    apply (erule exE)
    apply (rule_tac x="length (bools_of_nat (length bss) x) - length bss" in exI)
    apply (rule_tac x="bools_of_nat (length bss) x" in exI)
    apply (simp add: bools_of_nat_inverse bools_of_nat_length)
    done
  with Exist show ?case by (simp add:
    rquot_accepts det_wf_nfa quantify_nfa_well_formed_aut dfa2wf_nfa
    det_nfa_accepts [of _ n] zeros_is_alpha nfa_accepts_quantify_nfa [of _ n]
    nfa_of_dfa_accepts [of _ "Suc n"] insertll_len2 nats_of_boolss_insertll
    zeros_len nats_of_boolss_append nats_of_boolss_zeros zip_replicate_mapr
    nats_of_boolss_length o_def insertl_0_eq
    dfa_of_pf_well_formed cong: rev_conj_cong)
next
  case (Forall n p)
  then show ?case by simp
qed

text \<open>The same with minimization after quantification.\<close>

function dfa_of_pf' :: "nat \<Rightarrow> pf \<Rightarrow> dfa"
where
  "dfa_of_pf' n (Eq ks l) = eq_dfa n ks l"
| "dfa_of_pf' n (Le ks l) = ineq_dfa n ks l"
| "dfa_of_pf' n (And p q) = and_dfa (dfa_of_pf' n p) (dfa_of_pf' n q)"
| "dfa_of_pf' n (Or p q) = or_dfa (dfa_of_pf' n p) (dfa_of_pf' n q)"
| "dfa_of_pf' n (Imp p q) = imp_dfa (dfa_of_pf' n p) (dfa_of_pf' n q)"
| "dfa_of_pf' n (Exist p) = min_dfa (rquot (det_nfa (quantify_nfa 0 (nfa_of_dfa (dfa_of_pf' (Suc n) p)))) n)"
| "dfa_of_pf' n (Forall p) = dfa_of_pf' n (Neg (Exist (Neg p)))"
| "dfa_of_pf' n (Neg p) = negate_dfa (dfa_of_pf' n p)"
  by pat_completeness auto

termination dfa_of_pf'
  by (relation "measures [\<lambda>(n, pf). count_forall pf, \<lambda>(n, pf). size pf]") auto

lemmas dfa_of_pf'_induct =
  dfa_of_pf'.induct [case_names Eq Le And Or Imp Exist Forall Neg]

lemma dfa_of_pf'_well_formed: "wf_dfa (dfa_of_pf' n p) n"
proof (induct n p rule: dfa_of_pf'_induct)
  case (Eq n ks l)
  show ?case by (simp add: eq_wf_dfa)
next
  case (Le n ks l)
  show ?case by (simp add: ineq_wf_dfa)
next
  case (And n p q)
  then show ?case by (simp add: and_wf_dfa)
next
  case (Or n p q)
  then show ?case by (simp add: or_wf_dfa)
next
  case (Imp n p q)
  then show ?case by (simp add: imp_wf_dfa)
next
  case (Neg n p)
  then show ?case by (simp add: negate_wf_dfa)
next
  case (Exist n p)
  then show ?case
    by (simp add: rquot_well_formed_aut det_wf_nfa quantify_nfa_well_formed_aut dfa2wf_nfa min_dfa_wf)
next
  case (Forall n p)
  then show ?case by simp
qed

lemma dfa_of_pf'_correctness:
  "list_all (is_alph n) bss \<Longrightarrow>
     dfa_accepts (dfa_of_pf' n p) bss = eval_pf p (nats_of_boolss n bss)"
proof (induct n p arbitrary: bss rule: dfa_of_pf'_induct)
  case (Eq n ks l)
  then show ?case by (simp add: eq_dfa_accepts)
next
  case (Le n ks l)
  then show ?case by (simp add: ineq_dfa_accepts)
next
  case (And n p q)
  then show ?case by (simp add: and_dfa_accepts [of _ n] dfa_of_pf'_well_formed)
next
  case (Or n p q)
  then show ?case by (simp add: or_dfa_accepts [of _ n] dfa_of_pf'_well_formed)
next
  case (Imp n p q)
  then show ?case by (simp add: imp_dfa_accepts [of _ n] dfa_of_pf'_well_formed)
next
  case (Neg n p)
  then show ?case by (simp add: dfa_accepts_negate [of _ n] dfa_of_pf'_well_formed)
next
  case (Exist n p)
  have "(\<exists>k bs. eval_pf p (nat_of_bools bs # nats_of_boolss n bss) \<and> length bs = length bss + k) =
    (\<exists>x. eval_pf p (x # nats_of_boolss n bss))"
    apply (rule iffI)
    apply (erule exE conjE)+
    apply (erule exI)
    apply (erule exE)
    apply (rule_tac x="length (bools_of_nat (length bss) x) - length bss" in exI)
    apply (rule_tac x="bools_of_nat (length bss) x" in exI)
    apply (simp add: bools_of_nat_inverse bools_of_nat_length)
    done
  with Exist show ?case by (simp add:
    rquot_accepts det_wf_nfa quantify_nfa_well_formed_aut dfa2wf_nfa
    det_nfa_accepts [of _ n] zeros_is_alpha nfa_accepts_quantify_nfa [of _ n]
    nfa_of_dfa_accepts [of _ "Suc n"] insertll_len2 nats_of_boolss_insertll
    zeros_len nats_of_boolss_append nats_of_boolss_zeros zip_replicate_mapr
    nats_of_boolss_length o_def insertl_0_eq
    dfa_of_pf'_well_formed min_dfa_accept [of _ n] min_dfa_wf rquot_well_formed_aut
    cong: rev_conj_cong)
next
  case (Forall n p)
  then show ?case by simp
qed

end
