theory EigbyzProof
imports EigbyzDefs "../Majorities" "../Reduction"
begin

subsection \<open>Preliminary Lemmas\<close>

text \<open>Some technical lemmas about labels and trees.\<close>

lemma not_leaf_length:
  assumes l: "\<not>(is_leaf l)"
  shows "length_lbl l \<le> f"
  using l length_lbl[of l] by (simp add: is_leaf_def)

lemma nil_is_Label: "[] \<in> Label"
  by (auto simp: Label_def)

lemma card_set_lbl: "card (set_lbl l) = length_lbl l"
  unfolding set_lbl_def length_lbl_def
  using Rep_Label[of l, unfolded Label_def]
  by (auto elim: distinct_card)

lemma Rep_Label_root_node [simp]: "Rep_Label root_node = []"
  using nil_is_Label by (simp add: root_node_def Abs_Label_inverse)

lemma root_node_length [simp]: "length_lbl root_node = 0"
  by (simp add: length_lbl_def)

lemma root_node_not_leaf: "\<not>(is_leaf root_node)"
  by (simp add: is_leaf_def)

text \<open>Removing the last element of a non-root label gives a label.\<close>

lemma butlast_rep_in_label:
  assumes l:"l \<noteq> root_node"
  shows "butlast (Rep_Label l) \<in> Label"
proof -
  have "Rep_Label l \<noteq> []"
  proof
    assume "Rep_Label l = []"
    hence "Rep_Label l = Rep_Label root_node" by simp
    with l show "False" by (simp only: Rep_Label_inject)
  qed
  with Rep_Label[of l] show ?thesis
    by (auto simp: Label_def elim: distinct_butlast)
qed

text \<open>
  The label of a child is well-formed.
\<close>

lemma Rep_Label_append:
  assumes l: "\<not>(is_leaf l)"
  shows "(Rep_Label l @ [p] \<in> Label) = (p \<notin> set_lbl l)"
     (is "?lhs = ?rhs" is "(?l' \<in> _) = _")
proof
  assume lhs: "?lhs" thus ?rhs
    by (auto simp: Label_def set_lbl_def)
next
  assume p: "?rhs"
  from l[THEN not_leaf_length] have "length ?l' \<le> Suc f"
    by (simp add: length_lbl_def)
  moreover
  from Rep_Label[of l] have "distinct (Rep_Label l)"
    by (simp add: Label_def)
  with p have "distinct ?l'" by (simp add: set_lbl_def)
  ultimately
  show ?lhs by (simp add: Label_def)
qed

text \<open>
  The label of a child is the label of the parent, extended by a process.
\<close>
lemma label_children:
  assumes c: "c \<in> children l"
  shows "\<exists>p. p \<notin> set_lbl l \<and> Rep_Label c = Rep_Label l @ [p]"
proof -
  from c obtain p 
    where p: "p \<notin> set_lbl l" and l: "\<not>(is_leaf l)"
      and c: "c = Abs_Label (Rep_Label l @ [p])"
    by (auto simp: children_def)
  with Rep_Label_append[OF l] show ?thesis
    by (auto simp: Abs_Label_inverse)
qed

text \<open>
  The label of any child node is one longer than the label of its parent.
\<close>

lemma children_length:
  assumes "l \<in> children h"
  shows "length_lbl l = Suc (length_lbl h)"
  using label_children[OF assms] by (auto simp: length_lbl_def)

text \<open>The root node is never a child.\<close>

lemma children_not_root:
  assumes "root_node \<in> children l"
  shows "P"
  using label_children[OF assms] Abs_Label_inverse[OF nil_is_Label]
  by (auto simp: root_node_def)

text \<open>
  The label of a child with the last element removed is the label of
  the parent.
\<close>

lemma children_butlast_lbl:
  assumes "c \<in> children l"
  shows "butlast_lbl c = l"
  using label_children[OF assms]
  by (auto simp: butlast_lbl_def Rep_Label_inverse)

text \<open>
  The root node is not a child, and it is the only such node.
\<close>

lemma root_iff_no_child: "(l = root_node) = (\<forall>l'. l \<notin> children l')"
proof
  assume "l = root_node"
  thus "\<forall>l'. l \<notin> children l'" by (auto elim: children_not_root)
next
  assume rhs: "\<forall>l'. l \<notin> children l'"
  show "l = root_node"
  proof (rule rev_exhaust[of "Rep_Label l"])
    assume "Rep_Label l = []"
    hence "Rep_Label l = Rep_Label root_node" by simp
    thus ?thesis by (simp only: Rep_Label_inject)
  next
    fix l' q 
    assume l': "Rep_Label l = l' @ [q]"
    let ?l' = "Abs_Label l'"
    from Rep_Label[of l] l' have "l' \<in> Label" by (simp add: Label_def)
    hence repl': "Rep_Label ?l' = l'" by (rule Abs_Label_inverse)

    from Rep_Label[of l] l' have "l' @ [q] \<in> Label" by (simp add: Label_def)
    with l' have "Rep_Label l = Rep_Label (Abs_Label (l' @ [q]))"
      by (simp add: Abs_Label_inverse)
    hence "l = Abs_Label (l' @ [q])" by (simp add: Rep_Label_inject)
    moreover
    from Rep_Label[of l] l' have "length l' < Suc f" "q \<notin> set l'"
      by (auto simp: Label_def)
    moreover
    note repl'
    ultimately have "l \<in> children ?l'"
      by (auto simp: children_def is_leaf_def length_lbl_def set_lbl_def)
    with rhs show ?thesis by blast
  qed
qed

text \<open>
  If some label \<open>l\<close> is not a leaf, then the set of processes that
  appear at the end of the labels of its children is the set of all 
  processes that do not appear in \<open>l\<close>.
\<close>

lemma children_last_set:
  assumes l: "\<not>(is_leaf l)"
  shows "last_lbl ` (children l) = UNIV - set_lbl l"
proof
  show "last_lbl ` (children l) \<subseteq> UNIV - set_lbl l"
    by (auto dest: label_children simp: last_lbl_def)
next
  show "UNIV - set_lbl l \<subseteq> last_lbl ` (children l)"
  proof (auto simp: image_def)
    fix p
    assume p: "p \<notin> set_lbl l"
    with l have c: "Abs_Label (Rep_Label l @ [p]) \<in> children l"
      by (auto simp: children_def)
    with Rep_Label_append[OF l] p
    show "\<exists>c \<in> children l. p = last_lbl c"
      by (force simp: last_lbl_def Abs_Label_inverse)
  qed
qed

text \<open>
  The function returning the last element of a label is injective on the
  set of children of some given label.
\<close>

lemma last_lbl_inj_on_children:"inj_on last_lbl (children l)"
proof (auto simp: inj_on_def)
  fix c c'
  assume c: "c \<in> children l" and c': "c' \<in> children l"
     and eq: "last_lbl c = last_lbl c'"
  from c c' obtain p p'
    where p: "Rep_Label c = Rep_Label l @ [p]"
      and p': "Rep_Label c' = Rep_Label l @ [p']"
    by (auto dest!: label_children)
  from p p' eq have "p = p'" by (simp add: last_lbl_def)
  with p p' have "Rep_Label c = Rep_Label c'" by simp
  thus "c = c'" by (simp add: Rep_Label_inject)
qed

text \<open>
  The number of children of any non-leaf label \<open>l\<close> is the
  number of processes that do not appear in \<open>l\<close>.
\<close>

lemma card_children:
  assumes "\<not>(is_leaf l)"
  shows "card (children l) = N - (length_lbl l)"
proof -
  from assms
  have "last_lbl ` (children l) = UNIV - set_lbl l"
    by (rule children_last_set)
  moreover
  have "card (UNIV - set_lbl l) = card (UNIV::Proc set) - card (set_lbl l)"
    by (auto simp: card_Diff_subset_Int)
  moreover
  from last_lbl_inj_on_children 
  have "card (children l) = card (last_lbl ` children l)"
    by (rule sym[OF card_image])
  moreover
  note card_set_lbl[of l]
  ultimately
  show ?thesis by auto
qed

text \<open>
  Suppose a non-root label \<open>l'\<close> of length \<open>r+1\<close> ending in \<open>q\<close>, 
  and suppose that \<open>q\<close> is well heard by process \<open>p\<close> in round
  \<open>r\<close>. Then the value with which \<open>p\<close> decorates \<open>l\<close> is the one
  that \<open>q\<close> associates to the parent of \<open>l\<close>.
\<close>

lemma sho_correct_vals:
  assumes run: "SHORun EIG_M rho HOs SHOs"
      and l': "l' \<in> children l"
      and shop: "last_lbl l' \<in> SHOs (length_lbl l) p \<inter> HOs (length_lbl l) p"
                (is "?q \<in> SHOs (?len l) p \<inter> _")
  shows "vals (rho (?len l') p) l' = vals (rho (?len l) ?q) l"
proof -
  let ?r = "?len l"
  from run obtain \<mu>p
    where nxt: "nextState EIG_M ?r p (rho ?r p) \<mu>p (rho (Suc ?r) p)"
      and mu: "\<mu>p \<in> SHOmsgVectors EIG_M ?r p (rho ?r) (HOs ?r p) (SHOs ?r p)"
    by (auto simp: EIG_SHOMachine_def SHORun_eq SHOnextConfig_eq)
  with shop 
  have msl:"\<mu>p ?q = Some (vals (rho ?r ?q))"
    by (auto simp: EIG_SHOMachine_def EIG_sendMsg_def SHOmsgVectors_def)
  from nxt length_lbl[of l'] children_length[OF l']
  have "extend_vals ?r p (rho ?r p) \<mu>p (rho (Suc ?r) p)"
    by (auto simp: EIG_SHOMachine_def nextState_def EIG_nextState_def
                   next_main_def next_end_def)
  with msl l' show ?thesis
    by (auto simp: extend_vals_def children_length children_butlast_lbl)
qed

text \<open>
  A process fixes the value \<open>vals l\<close> of a label at state
  \<open>length_lbl l\<close>, and then never modifies the value.
\<close>
(* currently nowhere used *)
lemma keep_vals:
  assumes run: "SHORun EIG_M rho HOs SHOs"
  shows "vals (rho (length_lbl l + n) p) l = vals (rho (length_lbl l) p) l"
     (is "?v n = ?vl")
proof (induct n)
  show "?v 0 = ?vl" by simp
next
  fix n
  assume ih: "?v n = ?vl"
  let ?r = "length_lbl l + n"
  from run obtain \<mu>p
    where nxt: "nextState EIG_M ?r p (rho ?r p) \<mu>p (rho (Suc ?r) p)"
    by (auto simp: EIG_SHOMachine_def SHORun_eq SHOnextConfig_eq)
  with ih show "?v (Suc n) = ?vl"
    by (auto simp: EIG_SHOMachine_def nextState_def EIG_nextState_def
                   next_main_def next_end_def extend_vals_def)
qed


subsection \<open>Lynch's Lemmas and Theorems\<close>

text \<open>
  If some process is safely heard by all processes at round \<open>r\<close>,
  then all processes agree on the value associated to labels of length 
  \<open>r+1\<close> ending in that process.
\<close>

lemma lynch_6_15:
  assumes run: "SHORun EIG_M rho HOs SHOs"
  and l': "l' \<in> children l"
  and skr: "last_lbl l' \<in> SKr (HOs (length_lbl l)) (SHOs (length_lbl l))"
  shows "vals (rho (length_lbl l') p) l' = vals (rho (length_lbl l') q) l'"
  using assms unfolding SKr_def by (auto simp: sho_correct_vals)

text \<open>
  Suppose that \<open>l\<close> is a non-root label whose last element was well
  heard by all processes at round \<open>r\<close>, and that \<open>l'\<close> is a
  child of \<open>l\<close> corresponding to process \<open>q\<close> that is also
  well heard by all processes at round \<open>r+1\<close>. Then the values
  associated with \<open>l\<close> and \<open>l'\<close> by any process \<open>p\<close>
  are identical.
\<close>

lemma lynch_6_16_a:
  assumes run: "SHORun EIG_M rho HOs SHOs"
      and l: "l \<in> children t"
      and skrl: "last_lbl l \<in> SKr (HOs (length_lbl t)) (SHOs (length_lbl t))"
      and l': "l' \<in> children l"
      and skrl':"last_lbl l' \<in> SKr (HOs (length_lbl l)) (SHOs (length_lbl l))"
    shows "vals (rho (length_lbl l') p) l' = vals (rho (length_lbl l) p) l"
  using assms by (auto simp: SKr_def sho_correct_vals)

text \<open>
  For any non-leaf label \<open>l\<close>, more than half of its children end with a 
  process that is well heard by everyone at round \<open>length_lbl l\<close>.
\<close>

lemma lynch_6_16_c:
  assumes commR: "EIG_commPerRd (HOs (length_lbl l)) (SHOs (length_lbl l))"
                 (is "EIG_commPerRd (HOs ?r) _")
      and l: "\<not>(is_leaf l)"
  shows "card {l' \<in> children l. last_lbl l' \<in> SKr (HOs ?r) (SHOs ?r)}
         > card (children l) div 2"
    (is "card ?lhs > _")
proof -
  let ?skr = "SKr (HOs ?r) (SHOs ?r)"

  have "last_lbl ` ?lhs = ?skr - set_lbl l"
  proof
    from children_last_set[OF l]
    show "last_lbl ` ?lhs \<subseteq> ?skr - set_lbl l"
      by (auto simp: children_length)
  next
    {
      fix p
      assume p: "p \<in> ?skr" "p \<notin> set_lbl l"
      with  children_last_set[OF l]
      have "p \<in> last_lbl ` children l" by auto
      with p have "p \<in> last_lbl ` ?lhs"
        by (auto simp: image_def children_length)
    }
    thus "?skr - set_lbl l \<subseteq> last_lbl ` ?lhs" by auto
  qed
  moreover
  from last_lbl_inj_on_children[of l]
  have "inj_on last_lbl ?lhs" by (auto simp: inj_on_def)
  ultimately
  have "card ?lhs = card (?skr - set_lbl l)" by (auto dest: card_image)
  also have "\<dots> \<ge> (card ?skr) - (card (set_lbl l))"
    by (simp add: diff_card_le_card_Diff)
  finally have "card ?lhs \<ge> (card ?skr) - ?r"
    using card_set_lbl[of l] by simp

  moreover
  from commR have "card ?skr > (N + f) div 2"
    by (auto simp: EIG_commPerRd_def)
  with not_leaf_length[OF l] f
  have "(card ?skr) - ?r > (N - ?r) div 2" by auto
  with card_children[OF l]
  have "(card ?skr) - ?r > card (children l) div 2" by simp

  ultimately show ?thesis by simp
qed

text \<open>
  If \<open>l\<close> is a non-leaf label such that all of its children corresponding
  to well-heard processes at round \<open>length_lbl l\<close> have a uniform
  \<open>newvals\<close> decoration at round \<open>f+1\<close>, then \<open>l\<close>
  itself is decorated with that same value.
\<close>
lemma newvals_skr_uniform:
  assumes run: "SHORun EIG_M rho HOs SHOs"
      and commR: "EIG_commPerRd (HOs (length_lbl l)) (SHOs (length_lbl l))"
                 (is "EIG_commPerRd (HOs ?r) _")
      and notleaf: "\<not>(is_leaf l)"
      and unif: "\<And>l'. \<lbrakk>l' \<in> children l;
                   last_lbl l' \<in> SKr (HOs (length_lbl l)) (SHOs (length_lbl l))
                  \<rbrakk> \<Longrightarrow> newvals (rho (Suc f) p) l' = v"
  shows "newvals (rho (Suc f) p) l = v"
proof -
  from unif
  have "card {l' \<in> children l. last_lbl l' \<in> SKr (HOs ?r) (SHOs ?r)}
      \<le> card {l' \<in> children l. newvals (rho (Suc f) p) l' = v}"
    by (auto intro: card_mono)
  with lynch_6_16_c[of HOs l SHOs, OF commR notleaf]
  have maj: "has_majority v (newvals (rho (Suc f) p)) (children l)"
    by (simp add: has_majority_def)

  from run have "check_newvals (rho (Suc f) p)"
    by (auto simp: EIG_SHOMachine_def SHORun_eq SHOnextConfig_eq
                   nextState_def EIG_nextState_def next_end_def)
  with maj notleaf obtain w 
    where wmaj: "has_majority w (newvals (rho (Suc f) p)) (children l)"
      and wupd: "newvals (rho (Suc f) p) l = w"
    by (auto simp: check_newvals_def)
  from maj wmaj have "w = v"
    by (auto simp: has_majority_def elim: abs_majoritiesE')
  with wupd show ?thesis by simp
qed

text \<open>
  A node whose label \<open>l\<close> ends with a process which is well heard
  at round \<open>length_lbl l\<close> will have its \<open>newvals\<close> field set
  (at round \<open>f+1\<close>) to the ``fixed-up'' value given by \<open>vals\<close>.
\<close>

lemma lynch_6_16_d:
  assumes run: "SHORun EIG_M rho HOs SHOs"
      and commR: "\<forall>r. EIG_commPerRd (HOs r) (SHOs r)"
      and notroot: "l \<in> children t"
      and skr: "last_lbl l \<in> SKr (HOs (length_lbl t)) (SHOs (length_lbl t))"
            (is "_ \<in> SKr (HOs (?len t)) _")
  shows "newvals (rho (Suc f) p) l = fixupval (vals (rho (?len l) p) l)"
    (is "?P l")
using notroot skr proof (induct "Suc f - (?len l)" arbitrary: l t)
  fix l t
  assume "0 = Suc f - ?len l"
  with length_lbl[of l] have leaf: "is_leaf l" by (simp add: is_leaf_def)

  from run have "check_newvals (rho (Suc f) p)"
    by (auto simp: EIG_SHOMachine_def SHORun_eq SHOnextConfig_eq
                   nextState_def EIG_nextState_def next_end_def)
  with leaf show "?P l"
    by (auto simp: check_newvals_def is_leaf_def)
next
  fix k l t
  assume ih: "\<And> l' t'.
                \<lbrakk>k = Suc f - length_lbl l'; l' \<in> children t';
                 last_lbl l' \<in> SKr (HOs (?len t')) (SHOs (?len t'))\<rbrakk>
                \<Longrightarrow> ?P l'"
    and flk: "Suc k = Suc f - ?len l"
    and notroot: "l \<in> children t"
    and skr: "last_lbl l \<in> SKr (HOs (?len t)) (SHOs (?len t))"

  let ?v = "fixupval (vals (rho (?len l) p) l)"
  from flk have notlf: "\<not>(is_leaf l)" by (simp add: is_leaf_def)

  {
    fix l'
    assume l': "l' \<in> children l"
       and skr': "last_lbl l' \<in> SKr (HOs (?len l)) (SHOs (?len l))"

    from run notroot skr l' skr'
    have "vals (rho (?len l') p) l' = vals (rho (?len l) p) l"
      by (rule lynch_6_16_a)
    moreover
    from flk l' have "k = Suc f - ?len l'" by (simp add: children_length)
    from this l' skr' have "?P l'" by (rule ih)
    ultimately
    have "newvals (rho (Suc f) p) l' = ?v" 
      using notroot l' by (simp add: children_length)
  }
  with run commR notlf show "?P l" by (auto intro: newvals_skr_uniform)
qed

text \<open>
  Following Lynch~\cite{lynch:distributed}, we introduce some more useful
  concepts for reasoning about the data structure.
\<close>

text \<open>
  A label is \emph{common} if all processes agree on the final value it is
  decorated with.
\<close>

definition common where
  "common rho l \<equiv> 
   \<forall>p q. newvals (rho (Suc f) p) l = newvals (rho (Suc f) q) l"

text \<open>
  The subtrees of a given label are all its possible extensions.
\<close>

definition subtrees where
  "subtrees h \<equiv> { l . \<exists>t. Rep_Label l = (Rep_Label h) @ t }"

lemma children_in_subtree:
  assumes "l \<in> children h"
  shows "l \<in> subtrees h"
  using label_children[OF assms] by (auto simp: subtrees_def)

lemma subtrees_refl [iff]: "l \<in> subtrees l"
  by (auto simp: subtrees_def)

lemma subtrees_root [iff]: "l \<in> subtrees root_node"
  by (auto simp: subtrees_def)

lemma subtrees_trans:
  assumes "l'' \<in> subtrees l'" and "l' \<in> subtrees l"
  shows "l'' \<in> subtrees l"
  using assms by (auto simp: subtrees_def)

lemma subtrees_antisym:
  assumes "l \<in> subtrees l'" and "l' \<in> subtrees l"
  shows "l' = l"
  using assms by (auto simp: subtrees_def Rep_Label_inject)

lemma subtrees_tree:
  assumes l': "l \<in> subtrees l'" and l'': "l \<in> subtrees l''"
  shows "l' \<in> subtrees l'' \<or> l'' \<in> subtrees l'"
using assms proof (auto simp: subtrees_def append_eq_append_conv2)
  fix xs
  assume "Rep_Label l'' @ xs = Rep_Label l'"
  hence "Rep_Label l' = Rep_Label l'' @ xs" by (rule sym)
  thus "\<exists>ys. Rep_Label l' = Rep_Label l'' @ ys" ..
qed

lemma subtrees_cases:
  assumes l': "l' \<in> subtrees l"
      and self: "l' = l \<Longrightarrow> P"
      and child: "\<And>c. \<lbrakk> c \<in> children l; l' \<in> subtrees c \<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from l' obtain t where t: "Rep_Label l' = (Rep_Label l) @ t"
    by (auto simp: subtrees_def)
  have "l' = l \<or> (\<exists>c \<in> children l. l' \<in> subtrees c)"
  proof (cases t)
    assume "t = []"
    with t show ?thesis by (simp add: Rep_Label_inject)
  next
    fix p t'
    assume cons: "t = p # t'"
    from Rep_Label[of l'] t have "length (Rep_Label l @ t) \<le> Suc f"
      by (simp add: Label_def)
    with cons have notleaf: "\<not>(is_leaf l)"
      by (auto simp: is_leaf_def length_lbl_def)

    let ?c = "Abs_Label (Rep_Label l @ [p])"
    from t cons Rep_Label[of l'] have p: "p \<notin> set_lbl l"
      by (auto simp: Label_def set_lbl_def)
    with notleaf have c: "?c \<in> children l"
      by (auto simp: children_def)
    moreover
    from notleaf p have "Rep_Label l @ [p] \<in> Label"
      by (simp add: Rep_Label_append)
    hence "Rep_Label ?c = (Rep_Label l @ [p])"
      by (simp add: Abs_Label_inverse)
    with cons t have "l' \<in> subtrees ?c"
      by (auto simp: subtrees_def)
    ultimately show ?thesis by blast
  qed
  thus ?thesis by (auto elim!: self child)
qed

lemma subtrees_leaf:
  assumes l: "is_leaf l" and l': "l' \<in> subtrees l"
  shows "l' = l"
using l' proof (rule subtrees_cases)
  fix c
  assume "c \<in> children l"  \<comment> \<open>impossible\<close>
  with l show ?thesis by (simp add: children_def)
qed

lemma children_subtrees_equal:
  assumes c: "c \<in> children l" and c': "c' \<in> children l"
      and sub: "c' \<in> subtrees c"
  shows "c' = c"
proof -
  from assms have "Rep_Label c' = Rep_Label c"
    by (auto simp: subtrees_def dest!: label_children)
  thus ?thesis by (simp add: Rep_Label_inject)
qed

text \<open>
  A set \<open>C\<close> of labels is a \emph{subcovering} w.r.t. label \<open>l\<close>
  if for all leaf subtrees \<open>s\<close> of \<open>l\<close> there
  exists some label \<open>h \<in> C\<close> such that \<open>s\<close> is a subtree of
  \<open>h\<close> and \<open>h\<close> is a subtree of \<open>l\<close>.
\<close>
definition subcovering where
 "subcovering C l \<equiv> 
  \<forall>s \<in> subtrees l. is_leaf s \<longrightarrow> (\<exists>h \<in> C. h \<in> subtrees l \<and> s \<in> subtrees h)"

text \<open>
  A \emph{covering} is a subcovering w.r.t. the root node.
\<close>
abbreviation covering where
  "covering C \<equiv> subcovering C root_node"

text \<open>
  The set of labels whose last element is well heard by all processes
  throughout the execution forms a covering, and all these labels are common.
\<close>

lemma lynch_6_18_a:
  assumes "SHORun EIG_M rho HOs SHOs"
      and "\<forall>r. EIG_commPerRd (HOs r) (SHOs r)"
      and "l \<in> children t"
      and "last_lbl l \<in> SKr (HOs (length_lbl t)) (SHOs (length_lbl t))"
  shows "common rho l"
  using assms
  by (auto simp: common_def lynch_6_16_d lynch_6_15
           intro: arg_cong[where f="fixupval"])

lemma lynch_6_18_b:
  assumes run: "SHORun EIG_M rho HOs SHOs"
      and commG: "EIG_commGlobal HOs SHOs"
      and commR: "\<forall>r. EIG_commPerRd (HOs r) (SHOs r)"
  shows "covering {l. \<exists>t. l \<in> children t \<and> last_lbl l \<in> (SK HOs SHOs)}"
proof (clarsimp simp: subcovering_def)
  fix l
  assume "is_leaf l"
  with card_set_lbl[of l] have "card (set_lbl l) = Suc f"
    by (simp add: is_leaf_def)
  with commG have "N < card (SK HOs SHOs) + card (set_lbl l)"
    by (simp add: EIG_commGlobal_def)
  hence "\<exists>q \<in> set_lbl l . q \<in> SK HOs SHOs"
    by (auto dest: majorities_intersect)
  then obtain l1 q l2 where
    l: "Rep_Label l = (l1 @ [q]) @ l2" and q: "q \<in> SK HOs SHOs"
    unfolding set_lbl_def by (auto intro: split_list_propE)

  let ?h = "Abs_Label (l1 @ [q])"
  from Rep_Label[of l] l have "l1 @ [q] \<in> Label" by (simp add: Label_def)
  hence reph: "Rep_Label ?h = l1 @ [q]" by (rule Abs_Label_inverse)
  hence "length_lbl ?h \<noteq> 0" by (simp add: length_lbl_def)
  hence "?h \<noteq> root_node" by auto
  then obtain t where t: "?h \<in> children t"
    by (auto simp: root_iff_no_child)
  moreover
  from reph q have "last_lbl ?h \<in> SK HOs SHOs" by (simp add: last_lbl_def)
  moreover
  from reph l have "l \<in> subtrees ?h" by (simp add: subtrees_def)
  ultimately
  show "\<exists>h. (\<exists>t. h \<in> children t) \<and> last_lbl h \<in> SK HOs SHOs \<and> l \<in> subtrees h"
    by blast
qed

text \<open>
  If \<open>C\<close> covers the subtree rooted at label \<open>l\<close> and if
  \<open>l \<notin> C\<close> then \<open>C\<close> also covers subtrees rooted at
  \<open>l\<close>'s children.
\<close>

lemma lynch_6_19_a:
  assumes cov: "subcovering C l"
      and l: "l \<notin> C"
      and e: "e \<in> children l"
  shows "subcovering C e"
proof (clarsimp simp: subcovering_def)
  fix s
  assume s: "s \<in> subtrees e" and leaf: "is_leaf s"
  from s children_in_subtree[OF e] have "s \<in> subtrees l"
    by (rule subtrees_trans)
  with leaf cov obtain h where h: "h \<in> C" "h \<in> subtrees l" "s \<in> subtrees h"
    by (auto simp: subcovering_def)
  with l obtain e' where e': "e' \<in> children l" "h \<in> subtrees e'"
    by (auto elim: subtrees_cases)
  from \<open>s \<in> subtrees h\<close> \<open>h \<in> subtrees e'\<close> have "s \<in> subtrees e'"
    by (rule subtrees_trans)
  with s have "e \<in> subtrees e' \<or> e' \<in> subtrees e"
    by (rule subtrees_tree)
  with e e' have "e' = e"
    by (auto dest: children_subtrees_equal)
  with e' h show "\<exists>h\<in>C. h \<in> subtrees e \<and> s \<in> subtrees h" by blast
qed

text \<open>
  If there is a subcovering \<open>C\<close> for a label \<open>l\<close> such that all labels
  in \<open>C\<close> are common, then \<open>l\<close> itself is common as well.
\<close>

lemma lynch_6_19_b:
  assumes run: "SHORun EIG_M rho HOs SHOs"
      and cov: "subcovering C l"
      and com: "\<forall>l' \<in> C. common rho l'"
  shows "common rho l"
using cov proof (induct "Suc f - length_lbl l" arbitrary: l)
  fix l
  assume 0: "0 = Suc f - length_lbl l"
    and C: "subcovering C l"
  from 0 length_lbl[of l] have "is_leaf l"
    by (simp add: is_leaf_def)
  with C obtain h where h: "h \<in> C" "h \<in> subtrees l" "l \<in> subtrees h"
    by (auto simp: subcovering_def)
  hence "l \<in> C" by (auto dest: subtrees_antisym)
  with com show "common rho l" ..
next
  fix k l
  assume k: "Suc k = Suc f - length_lbl l"
     and C: "subcovering C l"
     and ih: "\<And>l'. \<lbrakk>k = Suc f - length_lbl l'; subcovering C l'\<rbrakk> \<Longrightarrow> common rho l'"
  show "common rho l"
  proof (cases "l \<in> C")
    case True 
    with com show ?thesis ..
  next
    case False
    with C have "\<forall>e \<in> children l. subcovering C e"
      by (blast intro: lynch_6_19_a)
    moreover
    from k have "\<forall>e \<in> children l. k = Suc f - length_lbl e"
      by (auto simp: children_length)
    ultimately
    have com_ch: "\<forall>e \<in> children l. common rho e"
      by (blast intro: ih)

    show ?thesis
    proof (clarsimp simp: common_def)
      fix p q
      from k have notleaf: "\<not>(is_leaf l)" by (simp add: is_leaf_def)
      let ?r = "Suc f"
      from com_ch
      have "\<forall>e \<in> children l. newvals (rho ?r p) e = newvals (rho ?r q) e"
        by (auto simp: common_def)
      hence "\<forall>w. {e \<in> children l. newvals (rho ?r p) e = w}
               = {e \<in> children l. newvals (rho ?r q) e = w}"
        by auto
      moreover
      from run
      have "check_newvals (rho ?r p)" "check_newvals (rho ?r q)"
        by (auto simp: EIG_SHOMachine_def SHORun_eq SHOnextConfig_eq nextState_def
                       EIG_nextState_def next_end_def)
      with notleaf have
        "(\<exists>w. has_majority w (newvals (rho ?r p)) (children l)
              \<and> newvals (rho ?r p) l = w)
       \<or> \<not>(\<exists>w. has_majority w (newvals (rho ?r p)) (children l))
              \<and> newvals (rho ?r p) l = undefined"
        "(\<exists>w. has_majority w (newvals (rho ?r q)) (children l)
              \<and> newvals (rho ?r q) l = w)
       \<or> \<not>(\<exists>w. has_majority w (newvals (rho ?r q)) (children l))
              \<and> newvals (rho ?r q) l = undefined"
        by (auto simp: check_newvals_def)
      ultimately show "newvals (rho ?r p) l = newvals (rho ?r q) l"
        by (auto simp: has_majority_def elim: abs_majoritiesE')
    qed
  qed
qed

text \<open>The root of the tree is a common node.\<close>

lemma lynch_6_20:
  assumes run: "SHORun EIG_M rho HOs SHOs"
      and commG: "EIG_commGlobal HOs SHOs"
      and commR: "\<forall>r. EIG_commPerRd (HOs r) (SHOs r)"
  shows "common rho root_node"
using run lynch_6_18_b[OF assms]
proof (rule lynch_6_19_b, clarify)
  fix l t
  assume "l \<in> children t" "last_lbl l \<in> SK HOs SHOs"
  thus "common rho l" by (auto simp: SK_def elim: lynch_6_18_a[OF run commR])
qed
  
text \<open>
  A decision is taken only at state \<open>f+1\<close> and then stays stable.
\<close>
lemma decide:
  assumes run: "SHORun EIG_M rho HOs SHOs"
  shows "decide (rho r p) = 
         (if r < Suc f then None
          else Some (newvals (rho (Suc f) p) root_node))"
     (is "?P r")
proof (induct r)
  from run show "?P 0"
    by (auto simp: EIG_SHOMachine_def SHORun_eq HOinitConfig_eq
                   initState_def EIG_initState_def)
next
  fix r
  assume ih: "?P r"
  from run obtain \<mu>p
    where "EIG_nextState r p (rho r p) \<mu>p (rho (Suc r) p)"
    by (auto simp: EIG_SHOMachine_def SHORun_eq SHOnextConfig_eq 
                   nextState_def)
  thus "?P (Suc r)"
  proof (auto simp: EIG_nextState_def next_main_def next_end_def)
    assume "\<not>(r < f)" "r \<noteq> f"
    with ih
    show "decide (rho r p) = Some (newvals (rho (Suc f) p) root_node)"
      by simp
  qed
qed


subsection \<open>Proof of Agreement, Validity, and Termination\<close>

text \<open>
  The Agreement property is an immediate consequence of lemma \<open>lynch_6_20\<close>.
\<close>

theorem Agreement:
  assumes run: "SHORun EIG_M rho HOs SHOs"
      and commG: "EIG_commGlobal HOs SHOs"
      and commR:  "\<forall>r. EIG_commPerRd (HOs r) (SHOs r)"
      and p: "decide (rho m p) = Some v"
      and q: "decide (rho n q) = Some w"
  shows "v = w"
  using p q lynch_6_20[OF run commG commR]
  by (auto simp: decide[OF run] common_def)


text \<open>
  We now show the Validity property: if all processes initially
  propose the same value \<open>v\<close>, then no other value may be decided.

  By lemma \<open>sho_correct_vals\<close>, value \<open>v\<close> must propagate to
  all children of the root that are well heard at round \<open>0\<close>, and
  lemma \<open>lynch_6_16_d\<close> implies that \<open>v\<close> is the value assigned
  to all these children by \<open>newvals\<close>. Finally, lemma
  \<open>newvals_skr_uniform\<close> lets us conclude.
\<close>

theorem Validity:
  assumes run: "SHORun EIG_M rho HOs SHOs"
      and commR: "\<forall>r. EIG_commPerRd (HOs r) (SHOs r)"
      and initv: "\<forall>q. the (vals (rho 0 q) root_node) = v"
      and dp: "decide (rho r p) = Some w"
  shows "v = w"
proof -

  have v: "\<forall>q. vals (rho 0 q) root_node = Some v"
  proof
    fix q
    from run have "vals (rho 0 q) root_node \<noteq> None"
      by (auto simp: EIG_SHOMachine_def SHORun_eq HOinitConfig_eq
                     initState_def EIG_initState_def)
    then obtain w where w: "vals (rho 0 q) root_node = Some w"
      by auto
    from initv have "the (vals (rho 0 q) root_node) = v" ..
    with w show "vals (rho 0 q) root_node = Some v" by simp
  qed

  let ?len = length_lbl
  let ?r = "Suc f"

  {
    fix l'
    assume l': "l' \<in> children root_node"
       and skr: "last_lbl l' \<in> SKr (HOs 0) (SHOs 0)"
    with run v have "vals (rho (?len l') p) l' = Some v"
      by (auto dest: sho_correct_vals simp: SKr_def)

    moreover
    from run commR l' skr
    have "newvals (rho ?r p) l' = fixupval (vals (rho (?len l') p) l')"
      by (auto intro: lynch_6_16_d)

    ultimately
    have "newvals (rho ?r p) l' = v" by simp
  }
  with run commR root_node_not_leaf
  have "newvals (rho ?r p) root_node = v"
    by (auto intro: newvals_skr_uniform)
  with dp show ?thesis by (simp add: decide[OF run])
qed

text \<open>Termination is trivial for \eigbyz{}.\<close>

theorem Termination:
  assumes "SHORun EIG_M rho HOs SHOs"
  shows "\<exists>r v. decide (rho r p) = Some v"
  using assms by (auto simp: decide)


subsection \<open>\eigbyz{} Solves Weak Consensus\<close>

text \<open>
  Summing up, all (coarse-grained) runs of \eigbyz{} for
  HO and SHO collections that satisfy the communication predicate 
  satisfy the Weak Consensus property.
\<close>

theorem eig_weak_consensus:
  assumes run: "SHORun EIG_M rho HOs SHOs"
      and commR: "\<forall>r. EIG_commPerRd (HOs r) (SHOs r)"
      and commG: "EIG_commGlobal HOs SHOs"
  shows "weak_consensus (\<lambda>p. the (vals (rho 0 p) root_node)) decide rho"
  unfolding weak_consensus_def
  using Validity[OF run commR]
        Agreement[OF run commG commR]
        Termination[OF run]
  by auto

text \<open>
  By the reduction theorem, the correctness of the algorithm carries over
  to the fine-grained model of runs.
\<close>

theorem eig_weak_consensus_fg:
  assumes run: "fg_run EIG_M rho HOs SHOs (\<lambda>r q. undefined)"
      and commR: "\<forall>r. EIG_commPerRd (HOs r) (SHOs r)"
      and commG: "EIG_commGlobal HOs SHOs"
  shows "weak_consensus (\<lambda>p. the (vals (state (rho 0) p) root_node))
                        decide (state \<circ> rho)"
    (is "weak_consensus ?inits _ _")
proof (rule local_property_reduction[OF run weak_consensus_is_local])
  fix crun
  assume crun: "CSHORun EIG_M crun HOs SHOs (\<lambda>r q. undefined)"
     and init: "crun 0 = state (rho 0)"
  from crun have "SHORun EIG_M crun HOs SHOs" by (unfold SHORun_def)
  from this commR commG 
  have "weak_consensus (\<lambda>p. the (vals (crun 0 p) root_node)) decide crun"
    by (rule eig_weak_consensus)
  with init show "weak_consensus ?inits decide crun"
    by (simp add: o_def)
qed


end
