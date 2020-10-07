(*
  File:      Treap.thy
  Authors:   Tobias Nipkow, Max Haslbeck
*)
section \<open>Treaps\<close>
theory Treap
imports
  "HOL-Library.Tree"
begin

definition treap :: "('k::linorder * 'p::linorder) tree \<Rightarrow> bool" where
"treap t = (bst (map_tree fst t) \<and> heap (map_tree snd t))"

abbreviation "keys t \<equiv> set_tree (map_tree fst t)"
abbreviation "prios t \<equiv> set_tree (map_tree snd t)"

function treap_of :: "('k::linorder * 'p::linorder) set \<Rightarrow> ('k * 'p) tree" where
"treap_of KP = (if infinite KP \<or> KP = {} then Leaf else
  let m = arg_min_on snd KP;
      L = {p \<in> KP. fst p < fst m};
      R = {p \<in> KP. fst p > fst m}
  in Node (treap_of L) m (treap_of R))"
by pat_completeness auto
termination
proof (relation "measure card")
  show "wf (measure card)"  by simp
next
  fix KP :: "('a \<times> 'b) set" and m L
  assume KP: "\<not> (infinite KP \<or> KP = {})"
  and m: "m = arg_min_on snd KP"
  and L: "L = {p \<in> KP. fst p < fst m}"
  have "m \<in> KP" using KP arg_min_if_finite(1) m by blast
  thus  "(L, KP) \<in> measure card" using KP L by(auto intro!: psubset_card_mono)
next
  fix KP :: "('a \<times> 'b) set" and m R
  assume KP: "\<not> (infinite KP \<or> KP = {})"
  and m: "m = arg_min_on snd KP"
  and R: "R = {p \<in> KP. fst m < fst p}"
  have "m \<in> KP" using KP arg_min_if_finite(1) m by blast
  thus  "(R, KP) \<in> measure card" using KP R by(auto intro!: psubset_card_mono)
qed

declare treap_of.simps [simp del]

lemma treap_of_unique:
  "\<lbrakk> treap t;  inj_on snd (set_tree t) \<rbrakk>
  \<Longrightarrow> treap_of (set_tree t) = t"
proof(induction "set_tree t" arbitrary: t rule: treap_of.induct)
  case (1 t)
  show ?case
  proof (cases "infinite (set_tree t) \<or> set_tree t = {}")
    case True
    thus ?thesis by(simp add: treap_of.simps)
  next
    case False
    let ?m = "arg_min_on snd (set_tree t)"
    let ?L = "{p \<in> set_tree t. fst p < fst ?m}"
    let ?R = "{p \<in> set_tree t. fst p > fst ?m}"
    obtain l a r where t: "t = Node l a r"
      using False by (cases t) auto
    have "\<forall>kp \<in> set_tree t. snd a \<le> snd kp"
      using "1.prems"(1)
      by(auto simp add: t treap_def ball_Un)
        (metis image_eqI snd_conv tree.set_map)+
    hence "a = ?m"
      by (metis "1.prems"(2) False arg_min_if_finite(1) arg_min_if_finite(2) inj_on_def 
          le_neq_trans t tree.set_intros(2))
    have "treap l" "treap r" using "1.prems"(1) by(auto simp: treap_def t)
    have l: "set_tree l = {p \<in> set_tree t. fst p < fst a}"
      using "1.prems"(1) by(auto simp add: treap_def t ball_Un tree.set_map)
    have r: "set_tree r = {p \<in> set_tree t. fst p > fst a}"
      using "1.prems"(1) by(auto simp add: treap_def t ball_Un tree.set_map)
    have "l = treap_of ?L"
      using "1.hyps"(1)[OF False \<open>a = ?m\<close> l r \<open>treap l\<close>]
        l \<open>a = ?m\<close> "1.prems"(2)
      by (fastforce simp add: inj_on_def)
    have "r = treap_of ?R"
      using "1.hyps"(2)[OF False \<open>a = ?m\<close> l r \<open>treap r\<close>]
        r \<open>a = ?m\<close> "1.prems"(2)
      by (fastforce simp add: inj_on_def)
    have "t = Node (treap_of ?L) ?m (treap_of ?R)"
      using \<open>a = ?m\<close> \<open>l = treap_of ?L\<close> \<open>r = treap_of ?R\<close> by(subst t) simp
    thus ?thesis using False
      by (subst treap_of.simps) simp
  qed
qed

lemma treap_unique:
  "\<lbrakk> treap t1; treap t2; set_tree t1 = set_tree t2; inj_on snd (set_tree t1) \<rbrakk>
  \<Longrightarrow> t1 = t2"
  for t1 t2 :: "('k::linorder * 'p::linorder) tree"
by (metis treap_of_unique)

fun ins :: "'k::linorder \<Rightarrow> 'p::linorder \<Rightarrow> ('k \<times> 'p) tree \<Rightarrow> ('k \<times> 'p) tree" where
"ins k p Leaf = \<langle>Leaf, (k,p), Leaf\<rangle>" |
"ins k p \<langle>l, (k1,p1), r\<rangle> =
  (if k < k1 then
     (case ins k p l of
       \<langle>l2, (k2,p2), r2\<rangle> \<Rightarrow>
         if p1 \<le> p2 then \<langle>\<langle>l2, (k2,p2), r2\<rangle>, (k1,p1), r\<rangle>
         else \<langle>l2, (k2,p2), \<langle>r2, (k1,p1), r\<rangle>\<rangle>)
   else
   if k > k1 then
     (case ins k p r of
       \<langle>l2, (k2,p2), r2\<rangle> \<Rightarrow>
         if p1 \<le> p2 then \<langle>l, (k1,p1), \<langle>l2, (k2,p2), r2\<rangle>\<rangle>
         else \<langle>\<langle>l, (k1,p1), l2\<rangle>, (k2,p2), r2\<rangle>)
   else \<langle>l, (k1,p1), r\<rangle>)"

lemma ins_neq_Leaf: "ins k p t \<noteq> \<langle>\<rangle>"
  by (induction t rule: ins.induct) (auto split: tree.split)

lemma keys_ins: "keys (ins k p t) = Set.insert k (keys t)"
proof (induction t rule: ins.induct)
  case 2
  then show ?case
    by (simp add: ins_neq_Leaf split: tree.split prod.split) (safe; fastforce)
qed (simp)

lemma prios_ins: "prios (ins k p t) \<subseteq> {p} \<union> prios t"
apply(induction t rule: ins.induct)
 apply simp
  apply (simp add: ins_neq_Leaf split: tree.split prod.split)
  by (safe; fastforce)

lemma prios_ins': "k \<notin> keys t \<Longrightarrow> prios (ins k p t) = {p} \<union> prios t"
apply(induction t rule: ins.induct)
 apply simp
  apply (simp add: ins_neq_Leaf split: tree.split prod.split)
  by (safe; fastforce)

lemma set_tree_ins: "set_tree (ins k p t) \<subseteq> {(k,p)} \<union> set_tree t"
  by (induction t rule: ins.induct) (auto simp add: ins_neq_Leaf split: tree.split prod.split)
    
lemma set_tree_ins': "k \<notin> keys t \<Longrightarrow>  {(k,p)} \<union> set_tree t \<subseteq> set_tree (ins k p t)"
  by (induction t rule: ins.induct) (auto simp add: ins_neq_Leaf split: tree.split prod.split)

lemma set_tree_ins_eq: "k \<notin> keys t \<Longrightarrow> set_tree (ins k p t) = {(k,p)} \<union> set_tree t"
  using set_tree_ins set_tree_ins' by blast

lemma prios_ins_special:
  "\<lbrakk> ins k p t = Node l (k',p') r;  p' = p; p \<in> prios r \<union> prios l \<rbrakk>
  \<Longrightarrow> p \<in> prios t"
  by (induction k p t arbitrary: l k' p' r rule: ins.induct)
     (fastforce simp add: ins_neq_Leaf split: tree.splits prod.splits if_splits)+

lemma treap_NodeI:
  "\<lbrakk> treap l; treap r;
     \<forall>k' \<in> keys l. k' < k; \<forall>k' \<in> keys r. k < k';
     \<forall>p' \<in> prios l. p \<le> p'; \<forall>p' \<in> prios r. p \<le> p' \<rbrakk>
  \<Longrightarrow> treap (Node l (k,p) r)"
 by (auto simp: treap_def)

lemma treap_rotate1:
  assumes "treap l2" "treap r2" "treap r" "\<not> p1 \<le> p2" "k < k1" and
  ins: "ins k p l = Node l2 (k2,p2) r2" and treap_ins: "treap (ins k p l)"
  and treap: "treap \<langle>l, (k1, p1), r\<rangle>"
  shows "treap (Node l2 (k2,p2) (Node r2 (k1,p1) r))"
proof(rule treap_NodeI[OF \<open>treap l2\<close> treap_NodeI[OF \<open>treap r2\<close> \<open>treap r\<close>]])
  from keys_ins[of k p l] have 1: "keys r2 \<subseteq> {k} \<union> keys l" by(auto simp: ins)
  from treap have 2: "\<forall>k'\<in>keys l. k' < k1" by (simp add: treap_def)
  show "\<forall>k'\<in>keys r2. k' < k1" using 1 2 \<open>k < k1\<close> by blast
next
  from treap have 2: "\<forall>p'\<in>prios l. p1 \<le> p'" by (simp add: treap_def)
  show "\<forall>p'\<in>prios r2. p1 \<le> p'"
  proof
    fix p' assume "p' \<in> prios r2"
    hence "p' = p \<or> p' \<in> prios l" using prios_ins[of k p l] ins by auto
    thus "p1 \<le> p'"
    proof
      assume [simp]: "p' = p"
      have "p2 = p \<or> p2 \<in> prios l" using prios_ins[of k p l] ins by simp
      thus "p1 \<le> p'"
      proof
        assume "p2 = p"
        thus "p1 \<le> p'"
          using prios_ins_special[OF ins] \<open>p' \<in> prios r2\<close> 2 by auto
      next
        assume "p2 \<in> prios l"
        thus "p1 \<le> p'" using 2 \<open>\<not> p1 \<le> p2\<close> by blast
      qed
    next
      assume "p' \<in> prios l"
      thus "p1 \<le> p'" using 2 by blast
    qed
  qed
next
  have "k2 = k \<or> k2 \<in> keys l" using keys_ins[of k p l] ins by (auto)
  hence 1: "k2 < k1"
  proof
    assume "k2 = k" thus "k2 < k1" using \<open>k < k1\<close> by simp
  next
    assume "k2 \<in> keys l"
    thus "k2 < k1" using treap by (auto simp: treap_def)
  qed
  have 2: "\<forall>k'\<in>keys r2. k2 < k'"
    using treap_ins by(simp add: ins treap_def)
  have 3: "\<forall>k'\<in>keys r. k2 < k'"
    using 1 treap by(auto simp: treap_def)
  show "\<forall>k'\<in>keys \<langle>r2, (k1, p1), r\<rangle>. k2 < k'" using 1 2 3 by auto
next
  show "\<forall>p'\<in>prios \<langle>r2, (k1, p1), r\<rangle>. p2 \<le> p'"
    using ins treap_ins treap \<open>\<not> p1 \<le> p2\<close> by (auto simp: treap_def ball_Un)
qed (use ins treap_ins treap in \<open>auto simp: treap_def ball_Un\<close>)


lemma treap_rotate2:
  assumes "treap l" "treap l2" "treap r2" "\<not> p1 \<le> p2" "k1 < k" and
  ins: "ins k p r = Node l2 (k2,p2) r2" and treap_ins: "treap (ins k p r)"
  and treap: "treap \<langle>l, (k1, p1), r\<rangle>"
  shows "treap (Node (Node l (k1,p1) l2) (k2,p2) r2)"
proof(rule treap_NodeI[OF treap_NodeI[OF \<open>treap l\<close> \<open>treap l2\<close>] \<open>treap r2\<close>])
  from keys_ins[of k p r] have 1: "keys l2 \<subseteq> {k} \<union> keys r" by(auto simp: ins)
  from treap have 2: "\<forall>k'\<in>keys r. k1 < k'" by (simp add: treap_def)
  show "\<forall>k'\<in>keys l2. k1 < k'" using 1 2 \<open>k1 < k\<close> by blast
next
  from treap have 2: "\<forall>p'\<in>prios r. p1 \<le> p'" by (simp add: treap_def)
  show "\<forall>p'\<in>prios l2. p1 \<le> p'"
  proof
    fix p' assume "p' \<in> prios l2"
    hence "p' = p \<or> p' \<in> prios r" using prios_ins[of k p r] ins by auto
    thus "p1 \<le> p'"
    proof
      assume [simp]: "p' = p"
      have "p2 = p \<or> p2 \<in> prios r" using prios_ins[of k p r] ins by simp
      thus "p1 \<le> p'"
      proof
        assume "p2 = p"
        thus "p1 \<le> p'"
          using prios_ins_special[OF ins] \<open>p' \<in> prios l2\<close> 2 by auto
      next
        assume "p2 \<in> prios r"
        thus "p1 \<le> p'" using 2 \<open>\<not> p1 \<le> p2\<close> by blast
      qed
    next
      assume "p' \<in> prios r"
      thus "p1 \<le> p'" using 2 by blast
    qed
  qed
next
  have "k2 = k \<or> k2 \<in> keys r" using keys_ins[of k p r] ins by (auto)
  hence 1: "k1 < k2"
  proof
    assume "k2 = k" thus "k1 < k2" using \<open>k1 < k\<close> by simp
  next
    assume "k2 \<in> keys r"
    thus "k1 < k2" using treap by (auto simp: treap_def)
  qed
  have 2: "\<forall>k'\<in>keys l. k' < k2" using 1 treap by(auto simp: treap_def)
  have 3: "\<forall>k'\<in>keys l2. k' < k2"
    using treap_ins by(auto simp: ins treap_def)
  show "\<forall>k'\<in>keys \<langle>l, (k1, p1), l2\<rangle>. k' < k2" using 1 2 3 by auto
next
  show "\<forall>p'\<in>prios \<langle>l, (k1, p1), l2\<rangle>. p2 \<le> p'"
    using ins treap_ins treap \<open>\<not> p1 \<le> p2\<close> by (auto simp: treap_def ball_Un)
qed (use ins treap_ins treap in \<open>auto simp: treap_def ball_Un\<close>)

lemma treap_ins: "treap t \<Longrightarrow> treap (ins k p t)"
proof(induction t rule: ins.induct)
  case 1 thus ?case by (simp add: treap_def)
next
  case (2 k p l k1 p1 r)
  have "treap l" "treap r"
    using "2.prems" by(auto simp: treap_def tree.set_map)
  show ?case
  proof cases
    assume "k < k1"
    obtain l2 k2 p2 r2 where ins: "ins k p l = Node l2 (k2,p2) r2"
      by (metis ins_neq_Leaf neq_Leaf_iff prod.collapse)
    note treap_ins = "2.IH"(1)[OF \<open>k < k1\<close> \<open>treap l\<close>]
    hence "treap l2" "treap r2" using ins by (auto simp add: treap_def)
    show ?thesis
    proof cases
      assume "p1 \<le> p2"
      have "treap (Node (Node l2 (k2,p2) r2) (k1,p1) r)"
        apply(rule treap_NodeI[OF treap_ins[unfolded ins] \<open>treap r\<close>])
        using ins treap_ins \<open>k < k1\<close> "2.prems" keys_ins[of k p l]
        by (auto simp add: treap_def ball_Un order_trans[OF \<open>p1 \<le> p2\<close>])
      thus ?thesis using \<open>k < k1\<close> ins \<open>p1 \<le> p2\<close> by simp
    next
      assume "\<not> p1 \<le> p2"
      have "treap (Node l2 (k2,p2) (Node r2 (k1,p1) r))"
        by(rule treap_rotate1[OF \<open>treap l2\<close> \<open>treap r2\<close>  \<open>treap r\<close> \<open>\<not> p1 \<le> p2\<close>
            \<open>k < k1\<close> ins treap_ins "2.prems"])
      thus ?thesis using \<open>k < k1\<close> ins \<open>\<not> p1 \<le> p2\<close> by simp
    qed
  next
    assume "\<not> k < k1"
    show ?thesis
    proof cases
    assume "k > k1"
    obtain l2 k2 p2 r2 where ins: "ins k p r = Node l2 (k2,p2) r2"
      by (metis ins_neq_Leaf neq_Leaf_iff prod.collapse)
    note treap_ins = "2.IH"(2)[OF \<open>\<not> k < k1\<close> \<open>k > k1\<close> \<open>treap r\<close>]
    hence "treap l2" "treap r2" using ins by (auto simp add: treap_def)
    have fst: "\<forall>k' \<in> set_tree (map_tree fst (ins k p r)).
                 k' = k \<or> k' \<in> set_tree (map_tree fst r)"
      by(simp add: keys_ins)
    show ?thesis
    proof cases
      assume "p1 \<le> p2"
      have "treap (Node l (k1,p1) (ins k p r))"
        apply(rule treap_NodeI[OF \<open>treap l\<close> treap_ins])
        using ins treap_ins \<open>k > k1\<close> "2.prems" keys_ins[of k p r]
        by (auto simp: treap_def ball_Un order_trans[OF \<open>p1 \<le> p2\<close>])
      thus ?thesis using \<open>\<not> k < k1\<close> \<open>k > k1\<close> ins \<open>p1 \<le> p2\<close> by simp
    next
      assume "\<not> p1 \<le> p2"
      have "treap (Node (Node l (k1,p1) l2) (k2,p2) r2)"
        by(rule treap_rotate2[OF \<open>treap l\<close> \<open>treap l2\<close> \<open>treap r2\<close> \<open>\<not> p1 \<le> p2\<close>
             \<open>k1 < k\<close> ins treap_ins "2.prems"])
      thus ?thesis using \<open>\<not> k < k1\<close>  \<open>k > k1\<close> ins \<open>\<not> p1 \<le> p2\<close> by simp
    qed
    next
      assume "\<not> k > k1"
      hence "k = k1" using \<open>\<not> k < k1\<close> by auto
      thus ?thesis using "2.prems" by(simp)
    qed
  qed  
qed

lemma treap_of_set_tree_unique:
  "\<lbrakk> finite A; inj_on fst A; inj_on snd A \<rbrakk>
  \<Longrightarrow> set_tree (treap_of A) = A"  
proof(induction "A" rule: treap_of.induct)
  case (1 A)
  note IH = 1
  show ?case
  proof (cases "infinite A \<or> A = {}")
    assume "infinite A \<or> A = {}"
    with IH show ?thesis by (simp add: treap_of.simps)
  next
    assume not_inf_or_empty: "\<not> (infinite A \<or> A = {})"
    let ?m = "arg_min_on snd A"
    let ?L = "{p \<in> A. fst p < fst ?m}"
    let ?R = "{p \<in> A. fst p > fst ?m}"
    obtain l a r where t: "treap_of A = Node l a r"
      using not_inf_or_empty
      by (cases "treap_of A") (auto simp: Let_def elim!: treap_of.elims split: if_splits)
    have [simp]: "inj_on fst {p \<in> A. fst p < fst (arg_min_on snd A)}"
                 "inj_on snd {p \<in> A. fst p < fst (arg_min_on snd A)}"
                 "inj_on fst {p \<in> A. fst (arg_min_on snd A) < fst p}"
                 "inj_on snd {p \<in> A. fst (arg_min_on snd A) < fst p}"
      using IH by (auto intro: inj_on_subset)
    have lr: "l = treap_of ?L" "r = treap_of ?R"
      using t by (auto simp: Let_def elim: treap_of.elims split: if_splits)
    then have l: "set_tree l = ?L"
       using not_inf_or_empty IH by auto
     have "r = treap_of ?R"
       using t by (auto simp: Let_def elim: treap_of.elims split: if_splits)
    then have r: "set_tree r = ?R"
      using not_inf_or_empty IH(2) by (auto)
    have a: "a = ?m"
      using t by (elim treap_of.elims) (simp add: Let_def split: if_splits)
    have "a \<noteq> fst (arg_min_on snd A)" if "(a,b) \<in> A" "(a, b) \<noteq> arg_min_on snd A" for a b
      using IH(4,5) that not_inf_or_empty arg_min_if_finite(1) inj_on_eq_iff by fastforce
    then have "a < fst (arg_min_on snd A)" 
       if "(a,b) \<in> A" "(a, b) \<noteq> arg_min_on snd A" "fst (arg_min_on snd A) \<ge> a" for a b
      using le_neq_trans that by auto
    moreover have "arg_min_on snd A \<in> A"
      using not_inf_or_empty arg_min_if_finite by auto
    ultimately have A: "A = {?m} \<union> ?L \<union> ?R"
      by auto
    show ?thesis using l r a A t by force
  qed
qed

lemma treap_of_subset: "set_tree (treap_of A) \<subseteq> A"
proof(induction "A" rule: treap_of.induct)
  case (1 A)
  note IH = 1
  show ?case
  proof (cases "infinite A \<or> A = {}")
    assume "infinite A \<or> A = {}"
    with IH show ?thesis by (simp add: treap_of.simps)
  next
    assume not_inf_or_empty: "\<not> (infinite A \<or> A = {})"
    let ?m = "arg_min_on snd A"
    let ?L = "{p \<in> A. fst p < fst ?m}"
    let ?R = "{p \<in> A. fst p > fst ?m}"
    obtain l a r where t: "treap_of A = Node l a r"
      using not_inf_or_empty by (cases "treap_of A")
                                (auto simp add: Let_def  elim!: treap_of.elims split: if_splits)
    have "l = treap_of ?L" "r = treap_of ?R"
      using t by (auto simp: Let_def elim: treap_of.elims split: if_splits)
    have "set_tree l \<subseteq> ?L" "set_tree r \<subseteq> ?R"
    proof -
      have "set_tree (treap_of {p \<in> A. fst p < fst (arg_min_on snd A)})
            \<subseteq> {p \<in> A. fst p < fst (arg_min_on snd A)}"
        by (rule IH) (use not_inf_or_empty in auto)
      then show "set_tree l \<subseteq> ?L"
        using \<open>l = treap_of ?L\<close> by auto
    next
      have "set_tree (treap_of {p \<in> A. fst (arg_min_on snd A) < fst p})
            \<subseteq> {p \<in> A. fst (arg_min_on snd A) < fst p}"
        by (rule IH) (use not_inf_or_empty in auto)
      then show "set_tree r \<subseteq> ?R"
        using \<open>r = treap_of ?R\<close> by auto
    qed
    moreover have "a = ?m"
      using t by (auto elim!: treap_of.elims simp add: Let_def split: if_splits)
    moreover have "{?m} \<union> ?L \<union> ?R \<subseteq> A"
      using not_inf_or_empty arg_min_if_finite by auto
    ultimately show ?thesis by (auto simp add: t)
  qed
qed

lemma treap_treap_of:
  "treap (treap_of A)"
proof(induction "A" rule: treap_of.induct)
  case (1 A)
  show ?case
  proof (cases "infinite A \<or> A = {}")
    case True
    with 1 show ?thesis by (simp add: treap_of.simps treap_def)
  next
    case False
    let ?m = "arg_min_on snd A"
    let ?L = "{p \<in> A. fst p < fst ?m}"
    let ?R = "{p \<in> A. fst p > fst ?m}"
    obtain l a r where t: "treap_of A = Node l a r"
      using False by (cases "treap_of A") (auto simp: Let_def elim!: treap_of.elims split: if_splits)
    have l: "l = treap_of ?L"
      using t by (auto simp: Let_def elim: treap_of.elims split: if_splits)
    then have treap_l: "treap l"
      using False by (auto intro: 1) 
    from l have keys_l: "keys l \<subseteq> fst ` ?L"
      by (auto simp add: tree.set_map intro!: image_mono treap_of_subset)
    have r: "r = treap_of ?R"
      using t by (auto simp: Let_def elim: treap_of.elims split: if_splits)
    then have treap_r: "treap r"
      using False by (auto intro: 1) 
    from r have keys_r: "keys r \<subseteq> fst ` ?R"
      by (auto simp add: tree.set_map intro!: image_mono treap_of_subset)
    have prios: "prios l \<subseteq> snd ` A" "prios r \<subseteq> snd ` A"
      using l r treap_of_subset image_mono by (auto simp add: tree.set_map)
    have a: "a = ?m"
      using t by(auto simp: Let_def elim: treap_of.elims split: if_splits)
    have prios_l: "\<And>x. x \<in> prios l \<Longrightarrow> snd a \<le> x"
      by (drule rev_subsetD[OF _ prios(1)]) (use arg_min_least a False in fast)
    have prios_r: "\<And>x. x \<in> prios r \<Longrightarrow> snd a \<le> x"
      by (drule rev_subsetD[OF _ prios(2)]) (use arg_min_least a False in fast)
    show ?thesis
      using prios_r prios_l treap_l treap_r keys_l keys_r a 
      by (auto simp add: t treap_def dest: rev_subsetD[OF _ keys_l] rev_subsetD[OF _ keys_r])
    qed
qed

lemma treap_Leaf: "treap \<langle>\<rangle>"
  by (simp add: treap_def)

lemma foldl_ins_treap: "treap t \<Longrightarrow> treap (foldl (\<lambda>t' (x, p). ins x p t') t xs)"
  using treap_ins by (induction xs arbitrary: t) auto

lemma foldl_ins_set_tree: 
  assumes "inj_on fst (set ys)" "inj_on snd (set ys)" "distinct ys" "fst ` (set ys) \<inter> keys t = {}"
  shows "set_tree (foldl (\<lambda>t' (x, p). ins x p t') t ys) = set ys \<union> set_tree t"
  using assms
  by (induction ys arbitrary: t) (auto simp add: case_prod_beta' set_tree_ins_eq keys_ins)

lemma foldl_ins_treap_of:
  assumes "distinct ys" "inj_on fst (set ys)" "inj_on snd (set ys)"
 shows "(foldl (\<lambda>t' (x, p). ins x p t') Leaf ys) = treap_of (set ys)"
  using assms by (intro treap_unique) (auto simp: treap_Leaf foldl_ins_treap foldl_ins_set_tree 
                                                  treap_treap_of treap_of_set_tree_unique)

end
