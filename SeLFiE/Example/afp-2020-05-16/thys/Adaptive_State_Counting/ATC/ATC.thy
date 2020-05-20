theory ATC
imports "../FSM/FSM"
begin

section \<open> Adaptive test cases \<close>

text \<open>
Adaptive test cases (ATCs) are tree-like structures that label nodes with inputs and edges with
outputs such that applying an ATC to some FSM is performed by applying the label of its root node
and then applying the ATC connected to the root node by an edge labeled with the observed output of
the FSM. The result of such an application is here called an ATC-reaction.

ATCs are here modelled to have edges for every possible output from each non-leaf node. This is not
a restriction on the definition of ATCs by Hierons @{cite "hierons"} as a missing edge can be 
expressed by an edge to a leaf.
\<close>


datatype ('in, 'out) ATC = Leaf | Node 'in "'out \<Rightarrow> ('in, 'out) ATC"

inductive atc_reaction :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC 
                            \<Rightarrow> ('in \<times> 'out) list \<Rightarrow> bool" 
  where
  leaf[intro!]: "atc_reaction M q1 Leaf []" |
  node[intro!]: "q2 \<in> succ M (x,y) q1 
                  \<Longrightarrow> atc_reaction M q2 (f y) io 
                  \<Longrightarrow> atc_reaction M q1 (Node x f) ((x,y)#io)"

inductive_cases leaf_elim[elim!] : "atc_reaction M q1 Leaf []"
inductive_cases node_elim[elim!] : "atc_reaction M q1 (Node x f) ((x,y)#io)"




subsection \<open> Properties of ATC-reactions \<close>

lemma atc_reaction_empty[simp] :
  assumes "atc_reaction M q t []"
  shows "t = Leaf"
using assms atc_reaction.simps by force 

lemma atc_reaction_nonempty_no_leaf :
  assumes "atc_reaction M q t (Cons a io)"
  shows "t \<noteq> Leaf"
using assms
proof -
  have "\<And>f c a ps. \<not> atc_reaction f (c::'c) (a::('a, 'b) ATC) ps \<or> a \<noteq> Leaf \<or> a \<noteq> Leaf \<or> ps = []"
    using atc_reaction.simps by fastforce
  then show ?thesis
    using assms by blast
qed  

lemma atc_reaction_nonempty[elim] :
  assumes "atc_reaction M q1 t (Cons (x,y) io)"
  obtains q2 f 
  where "t = Node x f" "q2 \<in> succ M (x,y) q1"  "atc_reaction M q2 (f y) io"
proof -
  obtain x2 f where "t = Node x2 f"  
    using assms by (metis ATC.exhaust atc_reaction_nonempty_no_leaf) 
  moreover have "x = x2" 
    using assms calculation atc_reaction.cases by fastforce 
  ultimately show ?thesis 
    using assms using that by blast 
qed

lemma atc_reaction_path_ex : 
  assumes "atc_reaction M q1 t io"
  shows "\<exists> tr . path M (io || tr) q1 \<and> length io = length tr"
using assms proof (induction io arbitrary: q1 t rule: list.induct)
  case Nil
  then show ?case by (simp add: FSM.nil) 
next
  case (Cons io_hd io_tl)
  then obtain x y where io_hd_def : "io_hd = (x,y)" 
    by (meson surj_pair)
  then obtain f where f_def : "t = (Node x f)" 
    using Cons atc_reaction_nonempty by metis
  then obtain q2 where q2_def : "q2 \<in> succ M (x,y) q1" "atc_reaction M q2 (f y) io_tl" 
    using Cons io_hd_def atc_reaction_nonempty by auto
  then obtain tr_tl where tr_tl_def :  "path M (io_tl || tr_tl) q2" "length io_tl = length tr_tl" 
    using Cons.IH[of q2 "f y"] by blast
  then have "path M (io_hd # io_tl || q2 # tr_tl) q1" 
    using Cons q2_def by (simp add: FSM.path.intros(2) io_hd_def)
  then show ?case using tr_tl_def by fastforce   
qed

lemma atc_reaction_path[elim] : 
  assumes "atc_reaction M q1 t io"
obtains tr
  where "path M (io || tr) q1" "length io = length tr"
by (meson assms atc_reaction_path_ex) 



subsection \<open> Applicability \<close>

text \<open> 
An ATC can be applied to an FSM if each node-label is contained in the input alphabet of the FSM.
\<close>

inductive subtest :: "('in, 'out) ATC \<Rightarrow> ('in, 'out) ATC \<Rightarrow> bool" where
  "t \<in> range f \<Longrightarrow> subtest t (Node x f)"

lemma accp_subtest : "Wellfounded.accp subtest t"
proof (induction t)
  case Leaf
  then show ?case by (meson ATC.distinct(1) accp.simps subtest.cases)
next
  case (Node x f)
  have IH: "Wellfounded.accp subtest t" if "t \<in> range f" for "t"
    using Node[of t] and that by (auto simp: eq_commute)
  show ?case by (rule accpI) (auto intro: IH elim!: subtest.cases)
qed

definition subtest_rel where "subtest_rel = {(t, Node x f) |f x t. t \<in> range f}"

lemma subtest_rel_altdef: "subtest_rel = {(s, t) |s t. subtest s t}"
  by (auto simp: subtest_rel_def subtest.simps)

lemma subtest_relI [intro]: "t \<in> range f \<Longrightarrow> (t, Node x f) \<in> subtest_rel"
  by (simp add: subtest_rel_def)

lemma subtest_relI' [intro]: "t = f y \<Longrightarrow> (t, Node x f) \<in> subtest_rel"
  by (auto simp: subtest_rel_def ran_def)

lemma wf_subtest_rel [simp, intro]: "wf subtest_rel" 
  using accp_subtest unfolding subtest_rel_altdef accp_eq_acc wf_acc_iff
  by auto



function inputs_atc :: "('a,'b) ATC \<Rightarrow> 'a set" where
  "inputs_atc Leaf = {}" |
  "inputs_atc (Node x f) = insert x (\<Union> (image inputs_atc (range f)))"
by pat_completeness auto
termination by (relation subtest_rel) auto

fun applicable :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC \<Rightarrow> bool" where
  "applicable M t = (inputs_atc t \<subseteq> inputs M)"

fun applicable_set :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
  "applicable_set M \<Omega> = (\<forall> t \<in> \<Omega> . applicable M t)"

lemma applicable_subtest :
  assumes "applicable M (Node x f)"
shows "applicable M (f y)"
using assms inputs_atc.simps
  by (simp add: Sup_le_iff)



subsection \<open> Application function IO \<close>

text \<open>
Function @{verbatim IO} collects all ATC-reactions of some FSM to some ATC.
\<close>

fun IO :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC \<Rightarrow> ('in \<times> 'out) list set" where
  "IO M q t = { tr . atc_reaction M q t tr }"

fun IO_set :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> ('in \<times> 'out) list set" 
  where
  "IO_set M q \<Omega> = \<Union> {IO M q t | t . t \<in> \<Omega>}"

lemma IO_language : "IO M q t \<subseteq> language_state M q"
  by (metis atc_reaction_path IO.elims language_state mem_Collect_eq subsetI) 

lemma IO_leaf[simp] : "IO M q Leaf = {[]}"
proof   
  show "IO M q Leaf \<subseteq> {[]}" 
  proof (rule ccontr)
    assume assm : "\<not> IO M q Leaf \<subseteq> {[]}"
    then obtain io_hd io_tl where elem_ex : "Cons io_hd io_tl \<in> IO M q Leaf" 
      by (metis (no_types, hide_lams) insertI1 neq_Nil_conv subset_eq) 
    then show "False" 
      using atc_reaction_nonempty_no_leaf assm by (metis IO.simps mem_Collect_eq)
  qed  
next
  show "{[]} \<subseteq> IO M q Leaf" by auto 
qed


lemma IO_applicable_nonempty :
  assumes "applicable M t"
  and     "completely_specified M"
  and     "q1 \<in> nodes M"
  shows "IO M q1 t \<noteq> {}"
using assms proof (induction t arbitrary: q1)
  case Leaf
  then show ?case by auto
next
  case (Node x f)
  then have "x \<in> inputs M" by auto
  then obtain y q2  where x_appl : "q2 \<in> succ M (x, y) q1" 
    using Node unfolding completely_specified.simps by blast
  then have "applicable M (f y)" 
    using applicable_subtest Node by metis
  moreover have "q2 \<in> nodes M" 
    using Node(4) \<open>q2 \<in> succ M (x, y) q1\<close> FSM.nodes.intros(2)[of q1 M "((x,y),q2)"] by auto
  ultimately have "IO M q2 (f y) \<noteq> {}" 
    using Node by auto
  then show ?case unfolding IO.simps 
    using x_appl by blast  
qed


lemma IO_in_language :
  "IO M q t \<subseteq> LS M q"
  unfolding IO.simps by blast

lemma IO_set_in_language :
  "IO_set M q \<Omega> \<subseteq> LS M q"
  using IO_in_language[of M q] unfolding IO_set.simps by blast


subsection \<open> R-distinguishability \<close>

text \<open>
A non-empty ATC r-distinguishes two states of some FSM if there exists no shared ATC-reaction.
\<close>

fun r_dist :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"r_dist M t s1 s2 = (t \<noteq> Leaf \<and> IO M s1 t \<inter> IO M s2 t = {})"

fun r_dist_set :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> 'state \<Rightarrow> 'state \<Rightarrow> bool" where
"r_dist_set M T s1 s2 = (\<exists> t \<in> T . r_dist M t s1 s2)"


lemma r_dist_dist :
  assumes "applicable M t"
  and     "completely_specified M"
  and     "r_dist M t q1 q2"
  and     "q1 \<in> nodes M"
shows   "q1 \<noteq> q2"
proof (rule ccontr)
  assume "\<not>(q1 \<noteq> q2)" 
  then have "q1 = q2" 
    by simp
  then have "IO M q1 t = {}" 
    using assms by simp
  moreover have "IO M q1 t \<noteq> {}" 
    using assms IO_applicable_nonempty by auto
  ultimately show "False" 
    by simp
qed

lemma r_dist_set_dist :
  assumes "applicable_set M \<Omega>"
  and     "completely_specified M"
  and     "r_dist_set M \<Omega> q1 q2"
  and     "q1 \<in> nodes M"
shows   "q1 \<noteq> q2"
using assms r_dist_dist by (metis applicable_set.elims(2) r_dist_set.elims(2))  

lemma r_dist_set_dist_disjoint :
  assumes "applicable_set M \<Omega>"
  and     "completely_specified M"
  and     "\<forall> t1 \<in> T1 . \<forall> t2 \<in> T2 . r_dist_set M \<Omega> t1 t2"
  and     "T1 \<subseteq> nodes M"
shows "T1 \<inter> T2 = {}"
  by (metis assms disjoint_iff_not_equal r_dist_set_dist subsetCE)
  




subsection \<open> Response sets \<close>

text \<open>
The following functions calculate the sets of all ATC-reactions observed by applying some set of 
ATCs on every state reached in some FSM using a given set of IO-sequences.
\<close>


fun B :: "('in, 'out, 'state) FSM \<Rightarrow> ('in * 'out) list \<Rightarrow> ('in, 'out) ATC set 
          \<Rightarrow> ('in * 'out) list set" where
  "B M io \<Omega> = \<Union> (image (\<lambda> s . IO_set M s \<Omega>) (io_targets M (initial M) io))"


fun D :: "('in, 'out, 'state) FSM \<Rightarrow> 'in list set \<Rightarrow> ('in, 'out) ATC set
          \<Rightarrow> ('in * 'out) list set set" where
  "D M ISeqs \<Omega> = image (\<lambda> io . B M io \<Omega>) (LS\<^sub>i\<^sub>n M (initial M) ISeqs)"

fun append_io_B :: "('in, 'out, 'state) FSM \<Rightarrow> ('in * 'out) list \<Rightarrow> ('in, 'out) ATC set 
                    \<Rightarrow> ('in * 'out) list set" where
  "append_io_B M io \<Omega> = { io@res | res . res \<in> B M io \<Omega> }"




lemma B_dist' :
  assumes df: "B M io1 \<Omega> \<noteq> B M io2 \<Omega>"
  shows   "(io_targets M (initial M) io1) \<noteq> (io_targets M (initial M) io2)"
  using assms by force 

lemma B_dist :
  assumes "io_targets M (initial M) io1 = {q1}"
  and     "io_targets M (initial M) io2 = {q2}"
  and     "B M io1 \<Omega> \<noteq> B M io2 \<Omega>"
shows   "q1 \<noteq> q2"
  using assms by force


lemma D_bound :
  assumes wf: "well_formed M"
  and     ob: "observable M"
  and     fi: "finite ISeqs"
  shows "finite (D M ISeqs \<Omega>)" "card (D M ISeqs \<Omega>) \<le> card (nodes M)" 
proof -
  have "D M ISeqs \<Omega> \<subseteq> image (\<lambda> s . IO_set M s \<Omega>) (nodes M)"
  proof 
    fix RS assume RS_def : "RS \<in> D M ISeqs \<Omega>"
    then obtain xs ys where RS_tr : "RS = B M (xs || ys) \<Omega>" 
                                    "(xs \<in> ISeqs \<and> length xs = length ys 
                                        \<and> (xs || ys) \<in> language_state M (initial M))" 
      by auto
    then obtain qx where qx_def : "io_targets M (initial M) (xs || ys) = { qx }" 
      by (meson io_targets_observable_singleton_ex ob)  
    then have "RS = IO_set M qx \<Omega>" 
      using RS_tr by auto
    moreover have "qx \<in> nodes M" 
      by (metis FSM.nodes.initial io_targets_nodes qx_def singletonI) 
    ultimately show "RS \<in> image (\<lambda> s . IO_set M s \<Omega>) (nodes M)" 
      by auto
  qed
  moreover have "finite (nodes M)" 
    using assms by auto
  ultimately show "finite (D M ISeqs \<Omega>)" "card (D M ISeqs \<Omega>) \<le> card (nodes M)" 
    by (meson  finite_imageI infinite_super surj_card_le)+
qed


lemma append_io_B_in_language :
  "append_io_B M io \<Omega> \<subseteq> L M"
proof
  fix x assume "x \<in> append_io_B M io \<Omega>"
  then obtain res where "x = io@res" "res \<in> B M io \<Omega>"
    unfolding append_io_B.simps by blast
  then obtain q where "q \<in> io_targets M (initial M) io"  "res \<in> IO_set M q \<Omega>"
    unfolding B.simps by blast
  then have "res \<in> LS M q" 
    using IO_set_in_language[of M q \<Omega>] by blast

  obtain pIO where "path M (io || pIO) (initial M)" 
                   "length pIO = length io" "target (io || pIO) (initial M) = q"
    using \<open>q \<in> io_targets M (initial M) io\<close> by auto
  moreover obtain pRes where "path M (res || pRes) q" "length pRes = length res" 
    using \<open>res \<in> LS M q\<close> by auto
  ultimately have "io@res \<in> L M" 
    using FSM.path_append[of M "io||pIO" "initial M" "res||pRes"]
    by (metis language_state length_append zip_append) 
  then show "x \<in> L M"
    using \<open>x = io@res\<close> by blast
qed


lemma append_io_B_nonempty :
  assumes "applicable_set M \<Omega>"
  and     "completely_specified M"
  and     "io \<in> language_state M (initial M)"
  and     "\<Omega> \<noteq> {}"
shows "append_io_B M io \<Omega> \<noteq> {}"
proof -
  obtain t where "t \<in> \<Omega>" 
    using assms(4) by blast
  then have "applicable M t" 
    using assms(1) by simp
  moreover obtain tr where "path M (io || tr) (initial M) \<and> length tr = length io" 
    using assms(3) by auto
  moreover have "target (io || tr) (initial M) \<in> nodes M"
    using calculation(2) by blast
  ultimately have "IO M (target (io || tr) (initial M)) t \<noteq> {}" 
    using assms(2) IO_applicable_nonempty by simp
  then obtain io' where "io' \<in> IO M (target (io || tr) (initial M)) t" 
    by blast
  then have "io' \<in> IO_set M (target (io || tr) (initial M)) \<Omega>" 
    using \<open>t \<in> \<Omega>\<close> unfolding IO_set.simps by blast
  moreover have "(target (io || tr) (initial M)) \<in> io_targets M (initial M) io" 
    using \<open>path M (io || tr) (initial M) \<and> length tr = length io\<close> by auto 
  ultimately have "io' \<in> B M io \<Omega>" 
    unfolding B.simps by blast
  then have "io@io' \<in> append_io_B M io \<Omega>" 
    unfolding append_io_B.simps by blast
  then show ?thesis by blast
qed
  

lemma append_io_B_prefix_in_language :
  assumes "append_io_B M io \<Omega> \<noteq> {}"
  shows "io \<in> L M"
proof -
  obtain res where "io @ res \<in> append_io_B M io \<Omega> \<and> res \<in> B M io \<Omega>" 
    using assms by auto 
  then have "io_targets M (initial M) io \<noteq> {}" 
    by auto
  then obtain q where "q \<in> io_targets M (initial M) io" 
    by blast
  then obtain tr where "target (io || tr) (initial M) = q \<and> path M (io || tr) (initial M) 
                          \<and> length tr = length io" by auto 
  then show ?thesis by auto
qed





subsection \<open> Characterizing sets \<close>

text \<open>
A set of ATCs is a characterizing set for some FSM if for every pair of r-distinguishable states it
contains an ATC that r-distinguishes them.
\<close>

fun characterizing_atc_set :: "('in, 'out, 'state) FSM \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
"characterizing_atc_set M \<Omega> = (applicable_set M \<Omega> \<and> (\<forall> s1 \<in> (nodes M) . \<forall> s2 \<in> (nodes M) . 
    (\<exists> td . r_dist M td s1 s2) \<longrightarrow> (\<exists> tt \<in> \<Omega> . r_dist M tt s1 s2)))"


subsection \<open> Reduction over ATCs \<close>

text \<open>
Some state is a an ATC-reduction of another over some set of ATCs if for every contained ATC every 
ATC-reaction to it of the former state is also an ATC-reaction of the latter state.
\<close>


fun atc_reduction :: "('in, 'out, 'state) FSM \<Rightarrow> 'state \<Rightarrow> ('in, 'out, 'state) FSM \<Rightarrow> 'state 
                      \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
  "atc_reduction M2 s2 M1 s1 \<Omega> = (\<forall> t \<in> \<Omega> . IO M2 s2 t \<subseteq> IO M1 s1 t)"



\<comment> \<open>r-distinguishability holds for atc-reductions\<close>
lemma atc_rdist_dist[intro] :
  assumes wf2   : "well_formed M2"
  and     cs2   : "completely_specified M2"
  and     ap2   : "applicable_set M2 \<Omega>"
  and     el_t1 : "t1 \<in> nodes M2"
  and     red1  : "atc_reduction M2 t1 M1 s1 \<Omega>"
  and     red2  : "atc_reduction M2 t2 M1 s2 \<Omega>"
  and     rdist : "r_dist_set M1 \<Omega> s1 s2"
  and             "t1 \<in> nodes M2"
shows "r_dist_set M2 \<Omega> t1 t2"
proof -
  obtain td where td_def : "td \<in> \<Omega> \<and> r_dist M1 td s1 s2" 
    using rdist by auto
  then have "IO M1 s1 td \<inter> IO M1 s2 td = {}" 
    using td_def by simp
  moreover have "IO M2 t1 td \<subseteq> IO M1 s1 td" 
    using red1 td_def by auto
  moreover have "IO M2 t2 td \<subseteq> IO M1 s2 td" 
    using red2 td_def by auto
  ultimately have no_inter : "IO M2 t1 td \<inter> IO M2 t2 td = {}" 
    by blast
  
  then have "td \<noteq> Leaf" 
    by auto
  then have "IO M2 t1 td \<noteq> {}" 
    by (meson ap2 IO_applicable_nonempty applicable_set.elims(2) cs2 td_def assms(8)) 
  then have "IO M2 t1 td \<noteq> IO M2 t2 td" 
    using no_inter by auto 
  then show ?thesis 
    using no_inter td_def by auto 
qed




subsection \<open> Reduction over ATCs applied after input sequences \<close>

text \<open>
The following functions check whether some FSM is a reduction of another over a given set of input
sequences while furthermore the response sets obtained by applying a set of ATCs after every input
sequence to the first FSM are subsets of the analogously constructed response sets of the second
FSM.
\<close>

fun atc_io_reduction_on :: "('in, 'out, 'state1) FSM \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> 'in list 
                            \<Rightarrow> ('in, 'out) ATC set \<Rightarrow> bool" where
  "atc_io_reduction_on M1 M2 iseq \<Omega> = (L\<^sub>i\<^sub>n M1 {iseq} \<subseteq> L\<^sub>i\<^sub>n M2 {iseq} 
    \<and> (\<forall> io \<in> L\<^sub>i\<^sub>n M1 {iseq} . B M1 io \<Omega> \<subseteq> B M2 io \<Omega>))"

fun atc_io_reduction_on_sets :: "('in, 'out, 'state1) FSM \<Rightarrow> 'in list set \<Rightarrow> ('in, 'out) ATC set 
                                  \<Rightarrow> ('in, 'out, 'state2) FSM \<Rightarrow> bool" where
  "atc_io_reduction_on_sets M1 TS \<Omega> M2 = (\<forall> iseq \<in> TS . atc_io_reduction_on M1 M2 iseq \<Omega>)"

notation 
  atc_io_reduction_on_sets ("(_ \<preceq>\<lbrakk>_._\<rbrakk> _)" [1000,1000,1000,1000])



lemma io_reduction_from_atc_io_reduction :
  assumes "atc_io_reduction_on_sets M1 T \<Omega> M2"
  and     "finite T"
  shows "io_reduction_on M1 T M2" 
using assms(2,1) proof (induction T)
  case empty
  then show ?case by auto
next
  case (insert t T)
  then have "atc_io_reduction_on M1 M2 t \<Omega>"
    by auto
  then have "L\<^sub>i\<^sub>n M1 {t} \<subseteq> L\<^sub>i\<^sub>n M2 {t}"
    using atc_io_reduction_on.simps by blast

  have "L\<^sub>i\<^sub>n M1 T \<subseteq> L\<^sub>i\<^sub>n M2 T" 
    using insert.IH
  proof -
    have "atc_io_reduction_on_sets M1 T \<Omega> M2"
      by (meson contra_subsetD insert.prems atc_io_reduction_on_sets.simps subset_insertI)
    then show ?thesis
      using insert.IH by blast
  qed
  then have "L\<^sub>i\<^sub>n M1 T \<subseteq> L\<^sub>i\<^sub>n M2 (insert t T)"
    by (meson insert_iff language_state_for_inputs_in_language_state 
        language_state_for_inputs_map_fst language_state_for_inputs_map_fst_contained 
        subsetCE subsetI) 
  moreover have "L\<^sub>i\<^sub>n M1 {t} \<subseteq> L\<^sub>i\<^sub>n M2 (insert t T)"
  proof -
    obtain pps :: "('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pps x0 x1 \<in> x1 \<and> pps x0 x1 \<notin> x0)"
      by moura
    then have "\<forall>P Pa. pps Pa P \<in> P \<and> pps Pa P \<notin> Pa \<or> P \<subseteq> Pa"
      by blast
    moreover
    { assume "map fst (pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 {t})) \<notin> insert t T"
      then have "pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 {t}) \<notin> L\<^sub>i\<^sub>n M1 {t} 
                      \<or> pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 {t}) \<in> L\<^sub>i\<^sub>n M2 (insert t T)"
        by (metis (no_types) insertI1 language_state_for_inputs_map_fst_contained singletonD) }
    ultimately show ?thesis
      by (meson \<open>L\<^sub>i\<^sub>n M1 {t} \<subseteq> L\<^sub>i\<^sub>n M2 {t}\<close> language_state_for_inputs_in_language_state 
          language_state_for_inputs_map_fst set_rev_mp)
  qed
        
     
  ultimately show ?case
  proof -
    have f1: "\<forall>ps P Pa. (ps::('a \<times> 'b) list) \<notin> P \<or> \<not> P \<subseteq> Pa \<or> ps \<in> Pa"
      by blast
    obtain pps :: "('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list set \<Rightarrow> ('a \<times> 'b) list" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> v2 \<notin> x0) = (pps x0 x1 \<in> x1 \<and> pps x0 x1 \<notin> x0)"
      by moura
    moreover
    { assume "pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 (insert t T)) 
              \<notin> L\<^sub>i\<^sub>n M1 {t}"
      moreover
      { assume "map fst (pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 (insert t T))) 
                \<notin> {t}"
        then have "map fst (pps (L\<^sub>i\<^sub>n M2 (insert t T)) 
                      (L\<^sub>i\<^sub>n M1 (insert t T))) \<noteq> t"
          by blast
        then have "pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 (insert t T)) 
                        \<notin> L\<^sub>i\<^sub>n M1 (insert t T) 
                    \<or> pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 (insert t T)) 
                          \<in> L\<^sub>i\<^sub>n M2 (insert t T)"
          using f1 by (meson \<open>L\<^sub>i\<^sub>n M1 T \<subseteq> L\<^sub>i\<^sub>n M2 (insert t T)\<close> 
                       insertE language_state_for_inputs_in_language_state 
                       language_state_for_inputs_map_fst 
                       language_state_for_inputs_map_fst_contained) }
      ultimately have "io_reduction_on M1 (insert t T) M2 
                        \<or> pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 (insert t T)) 
                            \<notin> L\<^sub>i\<^sub>n M1 (insert t T) 
                        \<or> pps (L\<^sub>i\<^sub>n M2 (insert t T)) (L\<^sub>i\<^sub>n M1 (insert t T)) 
                            \<in> L\<^sub>i\<^sub>n M2 (insert t T)"
        using f1 by (meson language_state_for_inputs_in_language_state 
                     language_state_for_inputs_map_fst) }
      ultimately show ?thesis
        using f1 by (meson \<open>L\<^sub>i\<^sub>n M1 {t} \<subseteq> L\<^sub>i\<^sub>n M2 (insert t T)\<close> subsetI)
  qed 
qed
    
lemma atc_io_reduction_on_subset :
  assumes "atc_io_reduction_on_sets M1 T \<Omega> M2"
  and     "T' \<subseteq> T"
shows "atc_io_reduction_on_sets M1 T' \<Omega> M2"
  using assms unfolding atc_io_reduction_on_sets.simps by blast


lemma atc_reaction_reduction[intro] :
  assumes ls : "language_state M1 q1 \<subseteq> language_state M2 q2"
  and     el1 : "q1 \<in> nodes M1"
  and     el2 : "q2 \<in> nodes M2"
  and     rct : "atc_reaction M1 q1 t io"
  and     ob2 : "observable M2"
  and     ob1 : "observable M1"
shows "atc_reaction M2 q2 t io"
using assms proof (induction t arbitrary: io q1 q2)
  case Leaf
  then have "io = []" 
    by (metis atc_reaction_nonempty_no_leaf list.exhaust) 
  then show ?case 
    by (simp add: leaf)  
next
  case (Node x f)
  then obtain io_hd io_tl where io_split : "io = io_hd # io_tl" 
    by (metis ATC.distinct(1) atc_reaction_empty list.exhaust) 
  moreover obtain y where y_def : "io_hd = (x,y)" 
    using Node calculation by (metis ATC.inject atc_reaction_nonempty surj_pair) 
  ultimately  obtain q1x where q1x_def : "q1x \<in> succ M1 (x,y) q1" "atc_reaction M1 q1x (f y) io_tl" 
    using Node.prems(4) by blast 

  then have pt1 : "path M1 ([(x,y)] || [q1x]) q1" 
    by auto
  then have ls1 : "[(x,y)] \<in> language_state M1 q1" 
    unfolding language_state_def path_def using list.simps(9) by force
  moreover have "q1x \<in> io_targets M1 q1 [(x,y)]" 
    unfolding io_targets.simps
  proof -
    have f1: "length [(x, y)] = length [q1x]"
      by simp
    have "q1x = target ([(x, y)] || [q1x]) q1"
      by simp
    then show "q1x \<in> {target ([(x, y)] || cs) q1 |cs. path M1 ([(x, y)] || cs) q1 
                                                      \<and> length [(x, y)] = length cs}"
      using f1 pt1 by blast
  qed 
  ultimately have tgt1 : "io_targets M1 q1 [(x,y)] = {q1x}" 
    using Node.prems io_targets_observable_singleton_ex q1x_def 
    by (metis (no_types, lifting) singletonD) 

  
  then have ls2 : "[(x,y)] \<in> language_state M2 q2" 
    using Node.prems(1) ls1 by auto
  then obtain q2x where q2x_def : "q2x \<in> succ M2 (x,y) q2" 
    unfolding language_state_def path_def 
    using transition_system.path.cases by fastforce 
  then have pt2 : "path M2 ([(x,y)] || [q2x]) q2" 
    by auto
  then have "q2x \<in> io_targets M2 q2 [(x,y)]" 
    using ls2 unfolding io_targets.simps 
  proof -
    have f1: "length [(x, y)] = length [q2x]"
      by simp
    have "q2x = target ([(x, y)] || [q2x]) q2"
      by simp
    then show "q2x \<in> {target ([(x, y)] || cs) q2 |cs. path M2 ([(x, y)] || cs) q2 
                                                        \<and> length [(x, y)] = length cs}"
      using f1 pt2 by blast
  qed

  then have tgt2 : "io_targets M2 q2 [(x,y)] = {q2x}" 
    using Node.prems io_targets_observable_singleton_ex ls2 q2x_def 
    by (metis (no_types, lifting) singletonD) 


  then have "language_state M1 q1x \<subseteq> language_state M2 q2x" 
    using language_state_inclusion_of_state_reached_by_same_sequence
          [of M1 q1 M2 q2 "[(x,y)]" q1x q2x] 
          tgt1 tgt2 Node.prems by auto
  moreover have "q1x \<in> nodes M1" 
    using q1x_def(1) Node.prems(2) by (metis insertI1 io_targets_nodes tgt1)
  moreover have "q2x \<in> nodes M2" 
    using q2x_def(1) Node.prems(3) by (metis insertI1 io_targets_nodes tgt2)
  ultimately have "q2x \<in> succ M2 (x,y) q2 \<and> atc_reaction M2 q2x (f y) io_tl" 
    using Node.IH[of "f y" q1x q2x io_tl] ob1 ob2 q1x_def(2) q2x_def by blast 
 

  then show "atc_reaction M2 q2 (Node x f) io" using io_split y_def by blast 
qed


lemma IO_reduction :
  assumes ls : "language_state M1 q1 \<subseteq> language_state M2 q2"
  and     el1 : "q1 \<in> nodes M1"
  and     el2 : "q2 \<in> nodes M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "IO M1 q1 t \<subseteq> IO M2 q2 t"
  using assms atc_reaction_reduction unfolding IO.simps by auto

lemma IO_set_reduction :
  assumes ls : "language_state M1 q1 \<subseteq> language_state M2 q2"
  and     el1 : "q1 \<in> nodes M1"
  and     el2 : "q2 \<in> nodes M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "IO_set M1 q1 \<Omega> \<subseteq> IO_set M2 q2 \<Omega>"
proof -
  have "\<forall> t \<in> \<Omega> . IO M1 q1 t \<subseteq> IO M2 q2 t" 
    using assms IO_reduction by metis 
  then show ?thesis 
    unfolding IO_set.simps by blast
qed

lemma B_reduction :
  assumes red : "M1 \<preceq> M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "B M1 io \<Omega> \<subseteq> B M2 io \<Omega>"
proof 
  fix xy assume xy_assm : "xy \<in> B M1 io \<Omega>"
  then obtain q1x where q1x_def : "q1x \<in> (io_targets M1 (initial M1) io) \<and> xy \<in> IO_set M1 q1x \<Omega>" 
    unfolding B.simps by auto
  then obtain tr1 where tr1_def : "path M1 (io || tr1) (initial M1) \<and> length io = length tr1" 
    by auto

  then have q1x_ob : "io_targets M1 (initial M1) io = {q1x}" 
    using assms
    by (metis io_targets_observable_singleton_ex language_state q1x_def singleton_iff) 
  
  then have ls1 : "io \<in> language_state M1 (initial M1)" 
    by auto 
  then have ls2 : "io \<in> language_state M2 (initial M2)" 
    using red by auto

  then obtain tr2 where tr2_def : "path M2 (io || tr2) (initial M2) \<and> length io = length tr2" 
    by auto
  then obtain q2x where q2x_def : "q2x \<in> (io_targets M2 (initial M2) io)" 
    by auto

  then have q2x_ob : "io_targets M2 (initial M2) io = {q2x}" 
    using tr2_def assms
    by (metis io_targets_observable_singleton_ex language_state singleton_iff) 

  then have "language_state M1 q1x \<subseteq> language_state M2 q2x" 
    using q1x_ob assms unfolding io_reduction.simps 
    by (simp add: language_state_inclusion_of_state_reached_by_same_sequence) 
  then have "IO_set M1 q1x \<Omega> \<subseteq> IO_set M2 q2x \<Omega>" 
    using assms IO_set_reduction by (metis FSM.nodes.initial io_targets_nodes q1x_def q2x_def) 
  moreover have "B M1 io \<Omega> = IO_set M1 q1x \<Omega>" 
    using q1x_ob by auto
  moreover have "B M2 io \<Omega> = IO_set M2 q2x \<Omega>" 
    using q2x_ob by auto
  ultimately have "B M1 io \<Omega> \<subseteq> B M2 io \<Omega>" 
    by simp
  then show "xy \<in> B M2 io \<Omega>" using xy_assm 
    by blast
qed


lemma append_io_B_reduction :
  assumes red : "M1 \<preceq> M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "append_io_B M1 io \<Omega> \<subseteq> append_io_B M2 io \<Omega>"
proof 
  fix ioR assume ioR_assm : "ioR \<in> append_io_B M1 io \<Omega>" 
  then obtain res where res_def : "ioR = io @ res" "res \<in> B M1 io \<Omega>" 
    by auto
  then have "res \<in> B M2 io \<Omega>" 
    using assms B_reduction by (metis (no_types, hide_lams) subset_iff)
  then show "ioR \<in> append_io_B M2 io \<Omega>" 
    using ioR_assm res_def by auto
qed 



lemma atc_io_reduction_on_reduction[intro] :
  assumes red : "M1 \<preceq> M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "atc_io_reduction_on M1 M2 iseq \<Omega>"
unfolding atc_io_reduction_on.simps proof 
  show "L\<^sub>i\<^sub>n M1 {iseq} \<subseteq> L\<^sub>i\<^sub>n M2 {iseq}" 
    using red by auto 
next
  show "\<forall>io\<in>L\<^sub>i\<^sub>n M1 {iseq}. B M1 io \<Omega> \<subseteq> B M2 io \<Omega>" 
    using  B_reduction assms by blast
qed
    

lemma atc_io_reduction_on_sets_reduction[intro] :
  assumes red : "M1 \<preceq> M2"
  and     ob1 : "observable M1"
  and     ob2 : "observable M2"
shows "atc_io_reduction_on_sets M1 TS \<Omega> M2"
  using assms atc_io_reduction_on_reduction by (metis atc_io_reduction_on_sets.elims(3)) 

lemma atc_io_reduction_on_sets_via_LS\<^sub>i\<^sub>n : 
  assumes "atc_io_reduction_on_sets M1 TS \<Omega> M2"
  shows "(L\<^sub>i\<^sub>n M1 TS \<union> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 TS. B M1 io \<Omega>)) 
          \<subseteq> (L\<^sub>i\<^sub>n M2 TS \<union> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 TS. B M2 io \<Omega>))"
proof -
  have "\<forall> iseq \<in> TS . (L\<^sub>i\<^sub>n M1 {iseq} \<subseteq> L\<^sub>i\<^sub>n M2 {iseq} 
                        \<and> (\<forall> io \<in> L\<^sub>i\<^sub>n M1 {iseq} . B M1 io \<Omega> \<subseteq> B M2 io \<Omega>))" 
    using assms by auto
  then have "\<forall> iseq \<in> TS . (\<Union>io\<in>L\<^sub>i\<^sub>n M1 {iseq}. B M1 io \<Omega>) 
                            \<subseteq> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 {iseq}. B M2 io \<Omega>)"
    by blast
  moreover have "\<forall> iseq \<in> TS . (\<Union>io\<in>L\<^sub>i\<^sub>n M2 {iseq}. B M2 io \<Omega>) 
                                \<subseteq> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 TS. B M2 io \<Omega>)"
    unfolding language_state_for_inputs.simps by blast
  ultimately have elem_subset : "\<forall> iseq \<in> TS . 
                                  (\<Union>io\<in>L\<^sub>i\<^sub>n M1 {iseq}. B M1 io \<Omega>) 
                                    \<subseteq> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 TS. B M2 io \<Omega>)" 
    by blast
  
  show ?thesis
  proof 
    fix x assume "x \<in> L\<^sub>i\<^sub>n M1 TS \<union> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 TS. B M1 io \<Omega>)"
    then show "x \<in> L\<^sub>i\<^sub>n M2 TS \<union> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 TS. B M2 io \<Omega>)"
    proof (cases "x \<in> L\<^sub>i\<^sub>n M1 TS")
      case True
      then obtain iseq where "iseq \<in> TS" "x\<in> L\<^sub>i\<^sub>n M1 {iseq}"
        unfolding language_state_for_inputs.simps by blast 
      then have "atc_io_reduction_on M1 M2 iseq \<Omega>" 
        using assms by auto
      then have "L\<^sub>i\<^sub>n M1 {iseq} \<subseteq> L\<^sub>i\<^sub>n M2 {iseq}" 
        by auto
      then have "x \<in> L\<^sub>i\<^sub>n M2 TS"
        by (metis (no_types, lifting) UN_I 
            \<open>\<And>thesis. (\<And>iseq. \<lbrakk>iseq \<in> TS; x \<in> L\<^sub>i\<^sub>n M1 {iseq}\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> 
            \<open>\<forall>iseq\<in>TS. L\<^sub>i\<^sub>n M1 {iseq} \<subseteq> L\<^sub>i\<^sub>n M2 {iseq} \<and> (\<forall>io\<in>L\<^sub>i\<^sub>n M1 {iseq}. B M1 io \<Omega> \<subseteq> B M2 io \<Omega>)\<close> 
            language_state_for_input_alt_def language_state_for_inputs_alt_def set_rev_mp) 
      then show ?thesis 
        by blast
    next
      case False
      then have "x \<in> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 TS. B M1 io \<Omega>)"
        using \<open>x \<in> L\<^sub>i\<^sub>n M1 TS \<union> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 TS. B M1 io \<Omega>)\<close> by blast
      then obtain io where "io \<in> L\<^sub>i\<^sub>n M1 TS" "x \<in> B M1 io \<Omega>"
        by blast
      then obtain iseq where "iseq \<in> TS" "io\<in>L\<^sub>i\<^sub>n M1 {iseq}"
        unfolding language_state_for_inputs.simps by blast
      have "x \<in> (\<Union>io\<in>L\<^sub>i\<^sub>n M1 {iseq}. B M1 io \<Omega>)"
        using \<open>io \<in> L\<^sub>i\<^sub>n M1 {iseq}\<close> \<open>x \<in> B M1 io \<Omega>\<close> by blast
      then have "x \<in> (\<Union>io\<in>L\<^sub>i\<^sub>n M2 TS. B M2 io \<Omega>)"
        using \<open>iseq \<in> TS\<close> elem_subset by blast
      then show ?thesis 
        by blast
    qed
  qed
qed




end
