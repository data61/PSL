(*  Title:      Topology.thy
    Author:     Stefan Friedrich
    Maintainer: Stefan Friedrich
    License:    LGPL
*)

section \<open>A bit of general topology\<close>

theory Topology
imports "HOL-Library.FuncSet"
begin

text\<open>
  This theory gives a formal account of basic notions of general
  topology as they can be found in various textbooks, e.g. in
  \cite{mccarty67:_topol} or in \cite{querenburg01:_mengen_topol}.
  The development includes open and closed sets, neighbourhoods, as
  well as closure, open core, frontier, and adherent points of a set,
  dense sets, continuous functions, filters, ultra filters,
  convergence, and various separation axioms.
\<close>

text\<open>We use the theory on ``Pi and Function Sets'' by Florian
Kammueller and Lawrence C Paulson.\<close>

subsection\<open>Preliminaries\<close>

lemma seteqI:
  "\<lbrakk> \<And>x. x\<in>A \<Longrightarrow> x\<in>B; \<And>x. x\<in>B \<Longrightarrow> x\<in>A \<rbrakk> \<Longrightarrow> A = B"
  by auto

lemma subset_mono: "A \<subseteq> B \<Longrightarrow> M \<subseteq> A \<longrightarrow> M \<subseteq> B"
  by auto

lemma diff_diff:
  "C - (A - B) = (C - A) \<union> (C \<inter> B)"
  by blast

lemma diff_diff_inter: "\<lbrakk>B \<subseteq> A; B \<subseteq> X\<rbrakk> \<Longrightarrow> (X - (A - B)) \<inter> A = B"
  by auto

lemmas diffsimps = double_diff Diff_Un vimage_Diff
  Diff_Int_distrib Diff_Int

lemma vimage_comp:
"f: A \<rightarrow> B \<Longrightarrow> A \<inter> (f -` B \<inter> f -` g -` m)= A \<inter> (g \<circ> f) -` m "
  by (auto dest: funcset_mem)

lemma funcset_comp:
  "\<lbrakk> f : A \<rightarrow> B; g : B \<rightarrow> C \<rbrakk> \<Longrightarrow> g \<circ> f : A \<rightarrow> C"
  by (auto intro!: funcsetI dest!: funcset_mem)

subsection\<open>Definition\<close>

text\<open>A topology is defined by a set of sets (the open sets)
that is closed under finite intersections and infinite unions.\<close>


type_synonym 'a top = "'a set set"

definition
  carr :: "'a top \<Rightarrow> 'a set" ("carrier\<index>") where
  "carr T = \<Union>T"

definition
  is_open :: "'a top \<Rightarrow> 'a set \<Rightarrow> bool" ("_ open\<index>" [50] 50) where
  "is_open T s \<longleftrightarrow> s \<in> T"


locale carrier =
  fixes T :: "'a top" (structure)


lemma (in carrier) openI:
  "m \<in> T \<Longrightarrow> m open"
  by (simp add: is_open_def)

lemma (in carrier) openE:
  "\<lbrakk> m open; m \<in> T \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R" 
by (auto simp: is_open_def)

lemma (in carrier) carrierI [intro]:
  "\<lbrakk> t open; x \<in> t \<rbrakk> \<Longrightarrow> x \<in> carrier"
  by (auto simp: is_open_def carr_def)

lemma (in carrier) carrierE [elim]:
 "\<lbrakk> x \<in> carrier;
   \<And>t. \<lbrakk> t open; x \<in> t \<rbrakk> \<Longrightarrow> R
  \<rbrakk> \<Longrightarrow> R"
  by (auto simp: is_open_def carr_def)

lemma (in carrier) subM:
  "\<lbrakk> t \<in> M; M \<subseteq> T \<rbrakk> \<Longrightarrow> t open"
  by (auto simp: is_open_def)

lemma (in carrier) topeqI [intro!]:
  fixes S (structure)
  shows "\<lbrakk> \<And>m. m open\<^bsub>T\<^esub> \<Longrightarrow> m open\<^bsub>S\<^esub>;
           \<And>m. m open\<^bsub>S\<^esub> \<Longrightarrow> m open\<^bsub>T\<^esub> \<rbrakk>
         \<Longrightarrow> T = S"
by (auto simp: is_open_def)

locale topology = carrier T for T (structure) +
  assumes Int_open [intro!]:   "\<lbrakk> x open; y open\<rbrakk> \<Longrightarrow> x \<inter> y open"
  and     union_open [intro]: "\<forall>m \<in> M. m open \<Longrightarrow> \<Union> M open"

lemma topologyI:
  "\<lbrakk> \<And> x y. \<lbrakk> is_open T x; is_open T y\<rbrakk> \<Longrightarrow> is_open T (x \<inter> y);
     \<And> M. \<forall> m \<in> M. is_open T m \<Longrightarrow> is_open T (\<Union> M)
   \<rbrakk> \<Longrightarrow> topology T"
  by (auto simp: topology_def)

lemma (in topology) Un_open [intro!]:
  assumes abopen: "A open" "B open"
  shows "A \<union> B open"
proof-
  have "\<Union>{A, B} open" using abopen
    by fast
  thus ?thesis by simp
qed

text\<open>Common definitions of topological spaces require that the empty
set and the carrier set of the space be open. With our definition,
however, the carrier is implicitly given as the union of all open
sets; therefore it is trivially open. The empty set is open by the
laws of HOLs typed set theory.\<close>

lemma (in topology) empty_open [iff]: "{} open"
proof-
  have "\<Union>{} open" by fast
  thus ?thesis by simp
qed

lemma (in topology) carrier_open [iff]: "carrier open"
  by (auto simp: carr_def intro: openI)

lemma (in topology) open_kriterion:
  assumes t_contains_open: "\<And> x. x\<in>t \<Longrightarrow> \<exists>t'. t' open \<and> x\<in>t' \<and> t'\<subseteq>t"
  shows "t open"
proof-
  let ?M = "\<Union>x\<in>t. {t'. t' open \<and> x\<in>t' \<and> t'\<subseteq>t}"
  have "\<forall> m \<in> ?M. m open" by simp
  hence  "\<Union>?M open" by auto
  moreover have "t = \<Union>?M"
    by (auto dest!: t_contains_open)
  ultimately show ?thesis
    by simp
qed

text\<open>We can obtain a topology from a set of basic open sets by
closing the set under finite intersections and arbitrary unions.\<close>


inductive_set
  topo :: "'a set set \<Rightarrow> 'a top"
  for B :: "'a set set"
where
  basic [intro]: "x \<in> B \<Longrightarrow> x \<in> topo B"
| inter [intro]: "\<lbrakk> x \<in> topo B; y \<in> topo B \<rbrakk> \<Longrightarrow> x \<inter> y \<in> topo B"
| union [intro]: "(\<And>x. x \<in> M \<Longrightarrow> x \<in> topo B) \<Longrightarrow> \<Union>M \<in> topo B"

locale topobase = carrier T for B and T (structure) +
  defines "T \<equiv> topo B"

lemma (in topobase) topo_open:
  "t open = (t \<in> topo B)"
  by (auto simp: T_def is_open_def)

lemma (in topobase)
  basic [intro]: "t \<in> B \<Longrightarrow> t open" and
  inter [intro]: "\<lbrakk>x open; y open \<rbrakk> \<Longrightarrow> (x \<inter> y) open" and
  union [intro]: "(\<And>t. t\<in>M \<Longrightarrow> t open) \<Longrightarrow> \<Union>M open"
  by (auto simp: topo_open)

lemma (in topobase) topo_induct
  [case_names basic inter union, induct set: topo, consumes 1]:
    assumes opn: "x open"
    and bas: "\<And>x. x \<in> B \<Longrightarrow> P x"
    and int: "\<And>x y. \<lbrakk>x open; P x; y open; P y\<rbrakk> \<Longrightarrow> P (x \<inter> y)"
    and uni: "\<And>M. (\<forall>t\<in>M. t open \<and> P t) \<Longrightarrow> P (\<Union>M)"
    shows "P x"
proof-
  from opn have "x \<in> topo B" by (simp add: topo_open)
  thus ?thesis
    by induct (auto intro: bas int intro!:uni simp: topo_open)
qed


lemma topo_topology [iff]:
  "topology (topo B)"
  by (auto intro!: union topologyI simp: is_open_def)

lemma topo_mono:
  assumes asubb: "A \<subseteq> B"
  shows  "topo A \<subseteq> topo B"
proof
  fix m assume mintopoa: "m \<in> topo A"
  hence "A \<subseteq> B \<longrightarrow> m \<in> topo B"
    by (rule topo.induct) auto
  with asubb show "m \<in> topo B"
    by auto
qed

lemma topo_open_imp:
  fixes A and S (structure) defines "S \<equiv> topo A"
  fixes B and T (structure) defines "T \<equiv> topo B"
  shows "\<lbrakk> A \<subseteq> B; x open\<^bsub>S\<^esub> \<rbrakk> \<Longrightarrow> x open\<^bsub>T\<^esub>" (is "PROP ?P")
proof -
  interpret A_S: topobase A S by fact
  interpret topobase B T by fact
  show "PROP ?P" by (auto dest: topo_mono iff: A_S.topo_open topo_open)
qed

lemma (in topobase) carrier_topo: "carrier = \<Union>B"
proof
  show "carrier \<subseteq> \<Union>B"
  proof
    fix x assume "x \<in> carrier"
    then obtain t where "t open" and "x \<in> t" ..
    thus "x \<in> \<Union>B" by (induct, auto)
  qed
qed (auto iff: topo_open)


text\<open>Topological subspace\<close>


locale subtopology = carrier S + carrier T for S (structure) and T (structure) +
  assumes subtop[iff]: "s open = (\<exists>t. t open\<^bsub>T\<^esub> \<and> s = t \<inter> carrier)"

lemma subtopologyI:
  fixes S (structure)
  fixes T (structure)
  assumes H1: "\<And>s. s open \<Longrightarrow> \<exists>t. t open\<^bsub>T\<^esub> \<and> s = t \<inter> carrier"
  and     H2: "\<And>t. t open\<^bsub>T\<^esub> \<Longrightarrow> t \<inter> carrier open"
  shows "subtopology S T"
by (auto simp: subtopology_def intro: assms)

lemma (in subtopology) subtopologyE [elim]:
  assumes major: "s open"
  and     minor: "\<And>t. \<lbrakk> t open\<^bsub>T\<^esub>; s = t \<inter> carrier \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using assms by auto
  
lemma (in subtopology) subtopI [intro]:
  "t open\<^bsub>T\<^esub> \<Longrightarrow> t \<inter> carrier open"
  by auto

lemma (in subtopology) carrier_subset:
  "carrier\<^bsub>S\<^esub> \<subseteq> carrier\<^bsub>T\<^esub>"
  by auto

lemma (in subtopology) subtop_sub:
  assumes "topology T"
  assumes carrSopen: "carrier\<^bsub>S\<^esub> open\<^bsub>T\<^esub>"
  and s_open: "s open\<^bsub>S\<^esub>"
  shows "s open\<^bsub>T\<^esub>"
proof -
  interpret topology T by fact
  show ?thesis using assms by auto
qed

lemma (in subtopology) subtop_topology [iff]:
  assumes "topology T"
  shows "topology S"
proof -
  interpret topology T by fact
  show ?thesis proof (rule topologyI)
    fix u v assume uopen: "u open" and vopen: "v open"
    thus "u \<inter> v open"  by (auto simp add: Int_ac)
  next
    fix M assume msub: "\<forall>m\<in>M. m open"
    let ?N = "{x. x open\<^bsub>T\<^esub> \<and> x \<inter> carrier \<in> M}"
    have "\<Union>?N open\<^bsub>T\<^esub>" by auto
    hence "\<Union>?N \<inter> carrier open" ..
    moreover have "\<Union>?N  \<inter> carrier = \<Union>M"
    proof
      show "\<Union>M \<subseteq> \<Union>?N \<inter> carrier"
      proof
        fix x assume "x \<in> \<Union>M"
        then obtain s where sinM: "s \<in> M" and xins: "x \<in> s"
          by auto
        from msub sinM have s_open: "s open" ..
        then obtain t
          where t_open: "t open\<^bsub>T\<^esub>" and s_inter: "s = t \<inter> carrier" by auto
        with xins have xint: "x\<in>t" and xpoint: "x \<in> carrier" by auto
        moreover
        from t_open s_inter sinM have "t \<in> ?N" by auto
        ultimately show "x \<in> \<Union>?N \<inter> carrier"
          by auto
      qed
    qed auto
    finally show "\<Union>M open" .
  qed
qed

lemma  subtop_lemma:
  fixes A and S (structure) defines "S \<equiv> topo A"
  fixes B and T (structure) defines "T \<equiv> topo B"
  assumes  Asub: "A = (\<Union>t\<in>B. { t \<inter> \<Union>A })"
  shows   "subtopology S T"
proof -
  interpret A_S: topobase A S by fact
  interpret topobase B T by fact
  show ?thesis proof (rule subtopologyI)
    fix s assume "s open\<^bsub>S\<^esub>"
    thus "\<exists>t. t open\<^bsub>T\<^esub> \<and> s = t \<inter> carrier"
    proof induct
      case (basic s) with Asub
      obtain t where tB: "t \<in> B" and stA: "s = t \<inter> \<Union>A" by blast
      thus ?case by (auto simp: A_S.carrier_topo)
    next case (inter s t) thus ?case by auto
    next case (union M)
      let ?N = "\<Union>{u. u open\<^bsub>T\<^esub> \<and> (\<exists>m\<in>M. m = u \<inter> carrier)}"
      have "?N open\<^bsub>T\<^esub>" and "\<Union>M = ?N \<inter> carrier" using union by auto
      thus ?case by auto
    qed
  next
    fix t assume "t open\<^bsub>T\<^esub>"
    thus "t \<inter> carrier open"
    proof induct
      case (basic u) with Asub show ?case
        by (auto simp: A_S.carrier_topo)
    next case (inter u v)
      hence "(u \<inter> carrier) \<inter> (v \<inter> carrier) open" by auto
      thus ?case  by (simp add: Int_ac)
    next case (union M)
      let ?N = "\<Union>{s. \<exists>m\<in>M. s = m \<inter> carrier}"
      from union have "?N open" and "?N = \<Union>M \<inter> carrier" by auto
      thus ?case by auto
    qed
  qed
qed

text\<open>Sample topologies\<close>

definition
  trivial_top :: "'a top" where
  "trivial_top = {{}}"

definition
  discrete_top :: "'a set \<Rightarrow> 'a set set" where
  "discrete_top X = Pow X"

definition
  indiscrete_top :: "'a set \<Rightarrow> 'a set set" where
  "indiscrete_top X = {{}, X}"

definition
  order_base :: "('a::order) set \<Rightarrow> 'a set set" where
  "order_base A = (\<Union>x\<in>A. {{y. y \<in> A \<and> x \<le> y}})"

definition
  order_top :: "('a::order) set \<Rightarrow> 'a set set" where
  "order_top X = topo(order_base X)"

locale trivial = carrier +
  defines "T \<equiv> {{}}"

lemma (in trivial) open_iff [iff]:
  "m open = (m = {})"
  by (auto simp: T_def is_open_def)

lemma trivial_topology:
  fixes T (structure) defines "T \<equiv> {{}}"
  shows "topology T"
proof -
  interpret trivial T by fact
  show ?thesis by (auto intro: topologyI)
qed

lemma empty_carrier_implies_trivial:
  fixes S (structure) assumes "topology S"
  fixes T (structure) defines "T \<equiv> {{}}"
  shows "carrier = {} \<Longrightarrow> S = T" (is "PROP ?P")
proof -
  interpret topology S by fact
  interpret trivial T by fact
  show "PROP ?P" by auto
qed

locale discrete = carrier T for X and T (structure) +
  defines "T \<equiv> discrete_top X"

lemma (in discrete) carrier:
  "carrier = X"
  by (auto intro!:carrierI elim!:carrierE)
     (auto simp: discrete_top_def T_def is_open_def)

lemma (in discrete) open_iff [iff]:
  "t open = (t \<in> Pow carrier)"
proof-
  have "t open = (t \<in> Pow X)"
    by (auto simp: T_def discrete_top_def is_open_def)
  thus ?thesis by (simp add: carrier)
qed

lemma discrete_topology: "topology (discrete_top X)"
  by (auto intro!: topologyI simp: is_open_def discrete_top_def)
   blast

locale indiscrete = carrier T for X and T (structure) +
  defines "T \<equiv> indiscrete_top X"

lemma (in indiscrete) carrier:
  "X = carrier"
  by (auto intro!: carrierI elim!: carrierE)
     (auto simp: T_def indiscrete_top_def is_open_def)

lemma (in indiscrete) open_iff [iff]:
  "t open = (t = {} \<or> t = carrier)"
proof-
  have "t open = (t = {} \<or> t = X)"
    by (auto simp: T_def indiscrete_top_def is_open_def)
  thus ?thesis by (simp add: carrier)
qed
    
lemma indiscrete_topology: "topology (indiscrete_top X)"
  by (rule topologyI) (auto simp: is_open_def indiscrete_top_def)

locale orderbase =
  fixes X and B
  defines "B \<equiv> order_base X"

locale ordertop1 =  orderbase X B + topobase B T for X and B and T (structure)

locale ordertop = carrier T for X and T (structure) +
  defines "T \<equiv> order_top X"

lemma (in ordertop) ordertop_open:
  "t open = (t \<in> order_top X)"
  by (auto simp: T_def is_open_def)

lemma ordertop_topology [iff]:
  "topology (order_top X)"
  by (auto simp: order_top_def)

subsection\<open>Neighbourhoods\<close>

definition
  nhd :: "'a top \<Rightarrow> 'a \<Rightarrow> 'a set set"  ( "nhds\<index>") where
  "nhd T x = {U. U \<subseteq> carr T \<and> (\<exists> m. is_open T m \<and> x\<in>m \<and> m \<subseteq> U)}"

lemma (in carrier) nhdI [intro]:
  "\<lbrakk> U \<subseteq> carrier; m open; x \<in> m; m \<subseteq> U \<rbrakk> \<Longrightarrow>  U \<in> nhds x"
  by (auto simp: nhd_def)

lemma (in carrier) nhdE [elim]:
  "\<lbrakk> U \<in> nhds x; \<And>m. \<lbrakk> U \<subseteq> carrier; m open; x \<in> m; m \<subseteq> U \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: nhd_def)

lemma (in carrier) elem_in_nhd:
  "U \<in> nhds x \<Longrightarrow> x \<in> U"
  by auto

lemma (in carrier) carrier_nhd [intro]: "x \<in> carrier \<Longrightarrow> carrier \<in> nhds x"
  by auto

lemma (in carrier) empty_not_nhd [iff]:
  "{} \<notin> nhds x "
  by auto

lemma (in carrier) nhds_greater:
  "\<lbrakk>V \<subseteq> carrier; U \<subseteq> V;  U \<in> nhds x\<rbrakk> \<Longrightarrow> V \<in> nhds x"
  by (erule nhdE) blast

lemma (in topology) nhds_inter:
  assumes nhdU: "U \<in> nhds x"
  and     nhdV: "V \<in> nhds x"
  shows "(U \<inter> V) \<in> nhds x"
proof-
  from nhdU obtain u where
    Usub: "U \<subseteq> carrier" and
    uT:   "u open" and
    xu:   "x \<in> u" and
    usub: "u \<subseteq> U"
    by auto 
 from nhdV obtain v where
    Vsub: "V \<subseteq> carrier" and
    vT: "v open" and
    xv: "x \<in> v" and
    vsub: "v \<subseteq> V"
    by auto
  from Usub Vsub have "U \<inter> V \<subseteq> carrier" by auto
  moreover from uT vT have "u \<inter> v open" ..
  moreover from xu xv have "x \<in> u \<inter> v" ..
  moreover from usub vsub have "u \<inter> v \<subseteq> U \<inter> V" by auto
  ultimately show  ?thesis by auto
qed

lemma (in carrier) sub_nhd:
  "U \<in> nhds x \<Longrightarrow> \<exists>V \<in> nhds x. V \<subseteq> U \<and> (\<forall> z \<in> V. U \<in> nhds z)"
  by (auto elim!: nhdE)

lemma (in ordertop1) l1:
  assumes mopen: "m open"
  and xpoint: "x \<in> X"
  and ypoint: "y \<in> X"
  and xley: "x \<le> y"
  and xinm: "x \<in> m"
  shows "y \<in> m"
  using mopen xinm
proof induct
  case (basic U) thus ?case
    by (auto simp: B_def order_base_def ypoint
        intro: xley dest: order_trans)
qed auto

lemma (in ordertop1)
  assumes xpoint: "x \<in> X" and ypoint: "y \<in> X" and xley: "x \<le> y"
  shows "nhds x \<subseteq> nhds y"
proof
  fix u assume "u \<in> nhds x"
  then obtain m where "m open"
    and "m \<subseteq> u" and "u \<subseteq> carrier" and "x \<in> m"
    by auto
  with xpoint ypoint xley
  show "u \<in> nhds y"
    by (auto dest: l1)
qed


subsection\<open>Closed sets\<close>

text\<open>A set is closed if its complement is open.\<close>

definition
  is_closed :: "'a top \<Rightarrow> 'a set \<Rightarrow> bool" ("_ closed\<index>" [50] 50) where
  "is_closed T s \<longleftrightarrow> is_open T (carr T - s)"

lemma (in carrier) closedI:
  "(carrier - s) open \<Longrightarrow> s closed"
  by (auto simp: is_closed_def)

lemma (in carrier) closedE:
  "\<lbrakk> s closed; (carrier - s) open \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: is_closed_def)

lemma (in topology) empty_closed [iff]:
  "{} closed"
  by (auto intro!: closedI)

lemma (in topology) carrier_closed [iff]:
  "carrier closed"
  by (auto intro!: closedI)

lemma (in carrier) compl_open_closed:
  assumes mopen: "m open"
  shows "(carrier - m) closed"
proof (rule closedI)
  from mopen have "m \<subseteq> carrier"
    by auto
  hence "carrier - (carrier - m) = m"
    by (simp add: double_diff)
  thus "carrier - (carrier - m) open"
    using mopen by simp
qed

lemma (in carrier) compl_open_closed1:
  "\<lbrakk> m \<subseteq> carrier; (carrier - m) closed \<rbrakk> \<Longrightarrow> m open"
  by (auto elim: closedE simp: diffsimps)

lemma (in carrier) compl_closed_iff [iff]:
  " m \<subseteq> carrier \<Longrightarrow> (carrier - m) closed = (m open)"
  by (auto dest: compl_open_closed1 intro: compl_open_closed)

lemma (in topology) Un_closed [intro!]:
  "\<lbrakk> x closed; y closed \<rbrakk> \<Longrightarrow> x \<union> y closed"
  by (auto simp:Diff_Un elim!: closedE intro!: closedI)

lemma (in topology) inter_closed:
  assumes xsclosed: "\<And>x. x\<in>S \<Longrightarrow> x closed"
  shows "\<Inter>S closed"
proof (rule closedI)
  let ?M = "{m. \<exists>x\<in>S. m = carrier - x}"
  have "\<forall> m \<in> ?M. m open"
    by (auto dest: xsclosed elim: closedE)
  hence "\<Union> ?M open" ..
  moreover have "\<Union> ?M = carrier - \<Inter>S" by auto
  ultimately show "carrier - \<Inter>S open" by auto
qed

corollary (in topology) Int_closed [intro!]:
 assumes abclosed: "A closed" "B closed"
  shows  "A \<inter> B closed"
proof-
  from assms have "\<Inter>{A, B} closed"
    by (blast intro!: inter_closed)
  thus ?thesis by simp
qed

lemma (in topology) closed_diff_open:
assumes aclosed: "A closed"
  and   bopen: "B open"
  shows "A - B closed"
proof (rule closedI)
  from aclosed have "carrier - A open"
    by (rule closedE)
  moreover from bopen have "carrier \<inter> B open" by auto
  ultimately have "(carrier - A) \<union> (carrier \<inter> B) open" ..
  thus "carrier - (A - B) open" by (simp add: diff_diff)
qed

lemma (in topology) open_diff_closed:
assumes aclosed: "A closed"
  and   bopen: "B open"
  shows "B - A open"
proof-
  from aclosed have "carrier - A open"
    by (rule closedE)
  hence "(carrier - A) \<inter> B open" using bopen ..
  moreover from bopen have "B \<subseteq> carrier"
    by auto
  hence "(carrier - A) \<inter> B = B - A" by auto
  ultimately show "B - A open" by simp
qed
  

subsection\<open>Core, closure, and frontier of a set\<close>

definition
  cor :: "'a top \<Rightarrow> 'a set \<Rightarrow> 'a set"          ("core\<index>") where
  "cor T s = (\<Union>{m. is_open T m \<and> m \<subseteq> s})"

definition
  clsr :: "'a top \<Rightarrow> 'a set \<Rightarrow> 'a set"          ("closure\<index>") where
  "clsr T a = (\<Inter>{c. is_closed T c \<and> a \<subseteq> c})"

definition
  frt :: "'a top \<Rightarrow> 'a set \<Rightarrow> 'a set"          ("frontier\<index>") where
  "frt T s = clsr T s - cor T s"


subsubsection\<open>Core\<close>

lemma (in carrier) coreI:
  "\<lbrakk>m open; m \<subseteq> s; x \<in> m \<rbrakk> \<Longrightarrow> x \<in> core s"
  by (auto simp: cor_def)

lemma (in carrier) coreE:
  "\<lbrakk> x \<in> core s; \<And>m. \<lbrakk>m open; m \<subseteq> s; x \<in> m \<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: cor_def)

lemma (in topology) core_open [iff]:
  "core a open"
  by (auto simp: cor_def)

lemma (in carrier) core_subset:
  "core a \<subseteq> a"
  by (auto simp: cor_def)

lemmas (in carrier) core_subsetD = subsetD [OF core_subset]

lemma (in carrier) core_greatest:
  "\<lbrakk> m open; m \<subseteq> a \<rbrakk> \<Longrightarrow> m \<subseteq> core a"
  by (auto simp: cor_def)

lemma (in carrier) core_idem [simp]:
  "core (core a) = core a"
  by  (auto simp: cor_def)

lemma (in carrier) open_core_eq [simp]:
  "a open \<Longrightarrow> core a = a"
  by (auto simp: cor_def)

lemma (in topology) core_eq_open:
  "core a = a \<Longrightarrow> a open"
  by (auto elim: subst)

lemma (in topology) core_iff:
  "a open = (core a = a)"
  by (auto intro: core_eq_open)

lemma (in carrier) core_mono:
  "a \<subseteq> b \<Longrightarrow> core a \<subseteq> core b"
  by (auto simp: cor_def)

lemma (in topology) core_Int [simp]: 
  "core (a \<inter> b) = core a \<inter> core b"
  by (auto simp: cor_def)

lemma (in carrier) core_nhds:
  "\<lbrakk> U \<subseteq> carrier; x \<in> core U \<rbrakk> \<Longrightarrow> U \<in> nhds x"
  by (auto elim!: coreE)

lemma (in carrier) nhds_core:
  "U \<in> nhds x \<Longrightarrow> x \<in> core U"
  by (auto intro: coreI)

lemma (in carrier) core_nhds_iff:
  "U \<subseteq> carrier \<Longrightarrow> (x \<in> core U) = (U \<in> nhds x)"
  by (auto intro: core_nhds nhds_core)  

subsubsection\<open>Closure\<close>

lemma (in carrier) closureI [intro]:
"(\<And>c. \<lbrakk>c closed; a \<subseteq> c\<rbrakk> \<Longrightarrow> x \<in> c) \<Longrightarrow> x \<in> closure a"
  by (auto simp: clsr_def)

lemma (in carrier) closureE [elim]:
  "\<lbrakk> x \<in> closure a; \<not> c closed \<Longrightarrow> R;  \<not> a \<subseteq> c \<Longrightarrow> R;  x \<in> c \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: clsr_def)

lemma (in carrier) closure_least:
  "s closed \<Longrightarrow> closure s \<subseteq> s"
  by auto

lemma (in carrier) subset_closure:
  "s \<subseteq> closure s"
  by auto

lemma (in topology) closure_carrier [simp]:
  "closure carrier = carrier"
  by auto

lemma (in topology) closure_subset:
  "A \<subseteq> carrier \<Longrightarrow> closure A \<subseteq> carrier"
  by auto

lemma (in topology) closure_closed [iff]:
  "closure a closed"
  by (auto simp: clsr_def intro: inter_closed)

lemma (in carrier) closure_idem [simp]:
  "closure (closure s) = closure s"
  by (auto simp: clsr_def)

lemma (in carrier) closed_closure_eq [simp]:
  "a closed \<Longrightarrow> closure a = a"
  by (auto simp: clsr_def)

lemma (in topology) closure_eq_closed:
  "closure a = a \<Longrightarrow> a closed"
  by (erule subst) simp

lemma (in topology) closure_iff:
  "a closed = (closure a = a)"
  by (auto intro: closure_eq_closed)

lemma (in carrier) closure_mono1:
  "mono (closure)"
  by (rule, auto simp: clsr_def)

lemma (in carrier) closure_mono:
  "a \<subseteq> b \<Longrightarrow> closure a \<subseteq> closure b"
  by (auto simp: clsr_def)


lemma (in topology) closure_Un [simp]: 
  "closure (a \<union> b) = closure a \<union> closure b"
  by (rule, blast) (auto simp: clsr_def)


subsubsection\<open>Frontier\<close>

lemma (in carrier) frontierI:
  "\<lbrakk>x \<in> closure s; x \<in> core s \<Longrightarrow> False\<rbrakk> \<Longrightarrow> x \<in> frontier s"
  by (auto simp: frt_def)

lemma (in carrier) frontierE:
  "\<lbrakk> x \<in> frontier s; \<lbrakk>x \<in> closure s; x \<in> core s \<Longrightarrow> False\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: frt_def)

lemma (in topology) frontier_closed [iff]:
  "frontier s closed"
by (unfold frt_def)
(intro closure_closed core_open closed_diff_open)

lemma (in carrier) frontier_Un_core:
  "frontier s \<union> core s = closure s"
  by (auto dest: subsetD [OF core_subset] simp: frt_def)

lemma (in carrier) frontier_Int_core:
  "frontier s \<inter> core s = {}"
  by (auto simp: frt_def)

lemma (in topology) closure_frontier [simp]:
  "closure (frontier a) = frontier a"
  by simp

lemma (in topology) frontier_carrier [simp]:
  "frontier carrier = {}"
  by (auto simp: frt_def)

text\<open>Hence frontier is not monotone. Also @{prop "cor T (frt T A) =
{}"} is not a theorem as illustrated by the following counter
example. By the way: could the counter example be prooved using an
instantiation?\<close>

lemma counter_example_core_frontier:
  fixes X defines [simp]: "X \<equiv> (UNIV::nat set)"
  fixes T (structure) defines "T \<equiv> indiscrete_top X"
  shows "core (frontier {0}) = X"
proof -
  interpret indiscrete X T by fact
  have "core {0} = {}"
    by (auto simp add: carrier [symmetric] cor_def)
  moreover have "closure {0} = UNIV"
    by (auto simp: clsr_def carrier [symmetric] is_closed_def)
  ultimately have "frontier {0} = UNIV"
    by (auto simp: frt_def)
  thus ?thesis
    by (auto simp add: cor_def carrier [symmetric])
qed


subsubsection\<open>Adherent points\<close>

definition
  adhs :: "'a top \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool"     (infix "adh\<index>" 50) where
  "adhs T x A \<longleftrightarrow> (\<forall> U \<in> nhd T x. U \<inter> A \<noteq> {})"

lemma (in carrier) adhCE [elim?]:
"\<lbrakk>x adh A;  U \<notin> nhds x \<Longrightarrow> R; U \<inter> A \<noteq> {}  \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (unfold adhs_def) auto

lemma (in carrier) adhI [intro]:
  "(\<And>U. U \<in> nhds x \<Longrightarrow> U \<inter> A \<noteq> {}) \<Longrightarrow> x adh A"
  by (unfold adhs_def) simp

lemma (in carrier) closure_imp_adh:
  assumes asub: "A \<subseteq> carrier"
  and closure: "x \<in> closure A"
  shows "x adh A"
proof
  fix U assume unhd: "U \<in> nhds x"
  show "U \<inter> A \<noteq> {}"
  proof
    assume UA: "U \<inter> A = {}"
    from unhd obtain V where "V open" "x \<in> V" and VU: "V \<subseteq> U" ..
    moreover from UA VU have "V \<inter> A = {}" by auto
    ultimately show "False" using asub closure
      by (auto  dest!: compl_open_closed simp: clsr_def)
  qed
qed

lemma (in carrier) adh_imp_closure:
  assumes xpoint: "x \<in> carrier"
  and   adh: "x adh A"  
  shows "x \<in> closure A"
proof (rule ccontr)
  assume notclosure: "x \<notin> closure A"
  then obtain C
    where closed: "C closed"
    and   asubc:  "A \<subseteq> C"
    and   xnotinc: "x \<notin> C"
    by (auto simp: clsr_def)
  from closed have "carrier - C open" by (rule closedE)
  moreover from xpoint xnotinc have "x \<in> carrier - C" by simp
  ultimately have "carrier - C \<in> nhds x" by auto
  with adh have "(carrier - C) \<inter> A \<noteq> {}"
    by (auto elim: adhCE)
  with asubc show "False" by auto
qed

lemma (in topology) closed_adh:
  assumes Asub: "A \<subseteq> carrier"
  shows "A closed = (\<forall> x \<in> carrier. x adh A \<longrightarrow> x \<in> A)"
proof
  assume "A closed"
  hence AA: "closure A = A"
    by auto 
  thus "(\<forall> x \<in> carrier. x adh A \<longrightarrow> x \<in> A)"
    by (fast dest!: adh_imp_closure)
next assume adhA: "\<forall> x \<in> carrier. x adh A \<longrightarrow> x \<in> A"
  have "closure A \<subseteq> A"
  proof
    fix x assume xclosure: "x \<in> closure A"
    hence "x \<in> carrier" using Asub by (auto dest: closure_subset)
    with xclosure show "x \<in> A" using Asub adhA
      by (auto dest!: closure_imp_adh)
  qed
  thus "A closed" by (auto intro: closure_eq_closed)
qed

lemma (in carrier) adh_closure_iff:
  "\<lbrakk> A \<subseteq> carrier; x \<in> carrier \<rbrakk> \<Longrightarrow> (x adh A) = (x \<in> closure A)"
  by (auto dest: adh_imp_closure closure_imp_adh)


subsection\<open>More about closure and core\<close>

lemma (in topology) closure_complement [simp]:
  shows  "closure (carrier - A) = carrier - core A"
proof
  have  "closure (carrier - A) \<subseteq> carrier"
    by (auto intro: closure_subset)
  moreover have "closure (carrier - A) \<inter> core A = {}"
  proof (rule seteqI, clarsimp)
    fix x assume xclosure: "x \<in> closure (carrier - A)"
    hence xadh: "x adh carrier - A"
      by (auto intro: closure_imp_adh)
    moreover assume xcore: "x \<in> core A"
    hence "core A \<in> nhds x"
      by auto
    ultimately have "core A \<inter> (carrier - A) \<noteq> {}"
      by (auto elim: adhCE)
    thus "False" by (auto dest: core_subsetD)
  qed auto
  ultimately show "closure (carrier - A) \<subseteq> carrier - core A"
    by auto
next
  show "carrier - core A \<subseteq> closure (carrier - A)"
    by (auto simp: cor_def clsr_def is_closed_def)
qed


lemma (in carrier) core_complement [simp]:
  assumes asub: "A \<subseteq> carrier"
  shows  "core (carrier - A) = carrier - closure A"
proof
  show "carrier - closure A \<subseteq> core (carrier - A)"
    by (auto simp: cor_def clsr_def is_closed_def)
next
  have "core (carrier - A) \<subseteq> carrier"
    by (auto elim!: coreE)
  moreover have  "core (carrier - A) \<inter> closure A = {}"
  proof auto
    fix x assume "x \<in> core (carrier - A)"
    hence "(carrier - A) \<in> nhds x"
      by (auto iff: core_nhds_iff)
    moreover assume "x \<in> closure A"
    ultimately have "A \<inter> (carrier - A) \<noteq> {}" using asub
      by (auto dest!: closure_imp_adh elim!: adhCE)
    thus "False" by auto
  qed
  ultimately show "core (carrier - A) \<subseteq> carrier - closure A"
    by auto
qed


lemma (in carrier) core_closure_diff_empty [simp]:
  assumes asub: "A \<subseteq> carrier"
  shows "core (closure A - A) = {}"
proof auto
  fix x assume "x \<in> core (closure A - A)"
  then obtain m where
    mopen: "m open" and
    xinm: "x \<in> m" and
    msub: "m \<subseteq> closure A" and
    minter: "m \<inter> A = {}"
    by (auto elim!: coreE)
  from xinm msub have "x adh A" using asub
    by (auto dest: closure_imp_adh)
  moreover from xinm mopen have "m \<in> nhds x"
    by auto
  ultimately have "m \<inter> A \<noteq> {}" by (auto elim: adhCE)
  with minter show "False" by auto
qed

subsection\<open>Dense sets\<close>

definition
  is_densein :: "'a top \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "densein\<index>" 50) where
  "is_densein T A B \<longleftrightarrow> B \<subseteq> clsr T A"

definition
  is_dense :: "'a top \<Rightarrow> 'a set \<Rightarrow> bool"             ("_ dense\<index>" [50] 50) where
  "is_dense T A = is_densein T A (carr T)"


lemma (in carrier) densinI [intro!]: "B \<subseteq> closure A \<Longrightarrow> A densein B"
  by (auto simp: is_densein_def)

lemma (in carrier) denseinE [elim!]: "\<lbrakk> A densein B; B \<subseteq> closure A \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: is_densein_def)

lemma (in carrier) denseI [intro!]: "carrier \<subseteq> closure A \<Longrightarrow> A dense"
  by (auto simp: is_dense_def)

lemma (in carrier) denseE [elim]: "\<lbrakk> A dense; carrier \<subseteq> closure A \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: is_dense_def)

lemma (in topology) dense_closure_eq [dest]:
  "\<lbrakk> A dense; A \<subseteq> carrier \<rbrakk> \<Longrightarrow> closure A = carrier"
  by (auto dest: closure_subset)

lemma (in topology) dense_lemma: 
  "A \<subseteq> carrier \<Longrightarrow> carrier - (closure A - A) dense" 
  by auto

lemma (in topology) ex_dense_closure_inter:
  assumes ssub: "S \<subseteq> carrier"
  shows "\<exists> D C. D dense \<and> C closed \<and> S = D \<inter> C"
proof-
  let ?D = "carrier - (closure S - S)" and
      ?C = "closure S"
  from ssub have "?D dense" by auto
  moreover have "?C closed" ..
  moreover from ssub
  have "(carrier - (closure S - S)) \<inter> closure S = S"
    by (simp add: diff_diff_inter subset_closure)
  ultimately show ?thesis
    by auto
qed

lemma (in topology) ex_dense_closure_interE:
  assumes ssub: "S \<subseteq> carrier"
  and H: "\<And>D C. \<lbrakk> D \<subseteq> carrier; C \<subseteq> carrier; D dense; C closed; S = D \<inter> C \<rbrakk> \<Longrightarrow> R"
  shows "R"
proof-
  let ?D = "(carrier - (closure S - S))"
  and ?C = "closure S"
  have "?D \<subseteq> carrier" by auto
  moreover from assms have "?C \<subseteq> carrier"
    by (auto dest!: closure_subset)
  moreover from assms have "?D dense" by auto
  moreover have "?C closed" ..
  moreover from ssub have "S = ?D \<inter> ?C"
    by (simp add: diff_diff_inter subset_closure)
  ultimately show ?thesis
    by (rule H)
qed


subsection\<open>Continuous functions\<close>


definition
  INJ :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "INJ A B = {f. f : A \<rightarrow> B \<and> inj_on f A}"

definition
  SUR :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "SUR A B = {f. f : A \<rightarrow> B \<and> (\<forall> y\<in>B. \<exists> x\<in>A. y = f x)}"

definition
  BIJ :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "BIJ A B = INJ A B \<inter> SUR A B"

definition
  cnt :: "'a top \<Rightarrow> 'b top \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "cnt S T = {f. f : carr S \<rightarrow> carr T \<and>
                (\<forall> m. is_open T m \<longrightarrow> is_open S (carr S \<inter> (f -` m)))}"

definition
  HOM :: " 'a top \<Rightarrow> 'b top \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "HOM S T = {f. f \<in> cnt S T \<and> inv f \<in> cnt T S \<and> f \<in> BIJ (carr S) (carr T)}"

definition
  homeo :: "'a top \<Rightarrow> 'b top \<Rightarrow> bool" where
  "homeo S T \<longleftrightarrow> (\<exists>h \<in> BIJ (carr S) (carr T). h \<in> cnt S T \<and> inv h \<in> cnt T S)"

definition
  fimg :: "'b top \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set set \<Rightarrow> 'b set set" where
  "fimg T f F = {v. v \<subseteq> carr T \<and> (\<exists> u \<in> F. f`u \<subseteq> v)}"


lemma domain_subset_vimage:
  "f : A \<rightarrow> B \<Longrightarrow> A \<subseteq> f-`B"
  by (auto intro: funcset_mem)

lemma domain_inter_vimage:
  "f : A \<rightarrow> B \<Longrightarrow> A \<inter> f-`B = A"
  by (auto intro: funcset_mem)

lemma funcset_vimage_diff:
  "f : A \<rightarrow> B \<Longrightarrow> A - f-`(B - C) = A \<inter> f-`C"
  by (auto intro: funcset_mem)

locale func = S?: carrier S + T?: carrier T
  for f and S (structure) and T (structure) and fimage +
  assumes func [iff]: "f : carrier\<^bsub>S\<^esub> \<rightarrow> carrier\<^bsub>T\<^esub>"
  defines "fimage \<equiv> fimg T f"
  notes func_mem [simp, intro] = funcset_mem [OF func]
  and   domain_subset_vimage [iff] = domain_subset_vimage [OF func]
  and   domain_inter_vimage  [simp] = domain_inter_vimage [OF func]
  and   vimage_diff          [simp] = funcset_vimage_diff [OF func]

lemma (in func) fimageI [intro!]:
  shows "\<lbrakk> v \<subseteq> carrier\<^bsub>T\<^esub>; u \<in> F; f`u \<subseteq> v\<rbrakk> \<Longrightarrow> v \<in> fimage F"
  by (auto simp: fimg_def fimage_def)

lemma (in func) fimageE [elim!]:
  "\<lbrakk> v \<in> fimage F; \<And>u. \<lbrakk> v \<subseteq> carrier\<^bsub>T\<^esub> ; u\<in>F; f`u \<subseteq> v\<rbrakk> \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: fimage_def fimg_def)

lemma cntI:
  "\<lbrakk> f : carr S \<rightarrow> carr T; 
    (\<And>m. is_open T m \<Longrightarrow> is_open S (carr S \<inter> (f -` m))) \<rbrakk>
  \<Longrightarrow> f \<in> cnt S T"
  by (auto simp: cnt_def)

lemma cntE:
  "\<lbrakk> f \<in> cnt S T;
     \<lbrakk> f : carr S \<rightarrow> carr T;
      \<forall>m. is_open T m \<longrightarrow> is_open S (carr S \<inter> (f -` m)) \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (auto simp: cnt_def)

lemma cntCE:
  "\<lbrakk> f \<in> cnt S T;
     \<lbrakk> \<not> is_open T m; f : carr S \<rightarrow> carr T \<rbrakk> \<Longrightarrow> P;
     \<lbrakk> is_open S (carr S \<inter> (f -` m)); f : carr S \<rightarrow> carr T \<rbrakk>  \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (auto simp: cnt_def)

lemma cnt_fun:
  "f \<in> cnt S T \<Longrightarrow> f : carr S \<rightarrow> carr T"
  by (auto simp add: cnt_def)

lemma cntD1:
  "\<lbrakk> f \<in> cnt S T; x \<in> carr S \<rbrakk> \<Longrightarrow> f x \<in> carr T"
  by (auto simp add: cnt_def intro: funcset_mem)

lemma cntD2:
  "\<lbrakk> f \<in> cnt S T; is_open T m \<rbrakk> \<Longrightarrow> is_open S (carr S \<inter> (f -` m))"
  by (auto simp: cnt_def)


locale continuous = func +
  assumes continuous [dest, simp]:
  "m open\<^bsub>T\<^esub> \<Longrightarrow> carrier \<inter> (f -` m) open"

lemma continuousI:
  fixes S (structure)
  fixes T (structure)
  assumes  "f : carrier\<^bsub>S\<^esub> \<rightarrow> carrier\<^bsub>T\<^esub>"
           "\<And>m. m open\<^bsub>T\<^esub> \<Longrightarrow> carrier \<inter> (f -` m) open"
  shows "continuous f S T"
using assms by (auto simp: continuous_def func_def continuous_axioms_def)

lemma continuousE:
  fixes S (structure)
  fixes T (structure)
  shows
  "\<lbrakk> continuous f S T;
     \<lbrakk> f : carrier\<^bsub>S\<^esub> \<rightarrow> carrier\<^bsub>T\<^esub>;
      \<forall>m. m open\<^bsub>T\<^esub> \<longrightarrow> carrier\<^bsub>S\<^esub> \<inter> (f -` m) open \<rbrakk> \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (auto simp: continuous_def func_def continuous_axioms_def)

lemma continuousCE:
  fixes S (structure)
  fixes T (structure)
  shows
  "\<lbrakk> continuous f S T;
     \<lbrakk> \<not> m open\<^bsub>T\<^esub>; f : carrier\<^bsub>S\<^esub> \<rightarrow> carrier\<^bsub>T\<^esub> \<rbrakk> \<Longrightarrow> P;
     \<lbrakk> carrier\<^bsub>S\<^esub> \<inter> (f -` m) open\<^bsub>S\<^esub>; f : carrier\<^bsub>S\<^esub> \<rightarrow> carrier\<^bsub>T\<^esub> \<rbrakk>  \<Longrightarrow> P
   \<rbrakk> \<Longrightarrow> P"
  by (auto simp: continuous_def func_def continuous_axioms_def)

lemma (in continuous) closed_vimage [intro, simp]:
  assumes csubset: "c \<subseteq> carrier\<^bsub>T\<^esub>"
  and cclosed: "c closed\<^bsub>T\<^esub>"
  shows "f -` c closed"
proof-
  from cclosed have  "carrier\<^bsub>T\<^esub> - c open\<^bsub>T\<^esub>"  by (rule closedE)
  hence "carrier \<inter> f -` (carrier\<^bsub>T\<^esub> - c) open" by auto
  hence "carrier - f -` c open" by (auto simp: diffsimps)
  thus "f -` c closed" by (rule S.closedI)
qed

lemma continuousI2:
  fixes S (structure)
  fixes T (structure)
  assumes func: "f : carrier\<^bsub>S\<^esub> \<rightarrow> carrier\<^bsub>T\<^esub>"
  assumes R: "\<And>c. \<lbrakk> c \<subseteq> carrier\<^bsub>T\<^esub>; c closed\<^bsub>T\<^esub> \<rbrakk> \<Longrightarrow> f -` c closed"
  shows "continuous f S T"
proof (rule continuous.intro)
  from func show "func f S T" by (auto simp: func_def)
next
  interpret S: carrier S .
  interpret T: carrier T .
  show "continuous_axioms f S T"
  proof (rule continuous_axioms.intro)
    fix m let ?c = "carrier\<^bsub>T\<^esub> - m" assume "m open\<^bsub>T\<^esub>"
    hence csubset: "?c \<subseteq> carrier\<^bsub>T\<^esub>" and cclosed: "?c closed\<^bsub>T\<^esub>"
      by auto
    hence "f -` ?c closed" by (rule R)
    hence  "carrier - f -` ?c open"
      by (rule S.closedE)
    thus "carrier \<inter> f -` m open" by (simp add: funcset_vimage_diff [OF func])
  qed
qed


lemma cnt_compose:
  "\<lbrakk> f \<in> cnt S T; g \<in> cnt T U \<rbrakk> \<Longrightarrow> (g \<circ> f) \<in> cnt S U "
  by (auto intro!: cntI funcset_comp elim!: cntE simp add: vimage_comp)

lemma continuous_compose:
  "\<lbrakk> continuous f S T; continuous g T U \<rbrakk> \<Longrightarrow> continuous (g \<circ> f) S U"
  by (auto intro!: continuousI funcset_comp
       elim!: continuousE simp add: vimage_comp)


lemma id_continuous:
  fixes T (structure)
  shows "continuous id T T"
proof(rule continuousI)
  show "id \<in> carrier \<rightarrow> carrier"
    by (auto intro: funcsetI)
next
  interpret T: carrier T .
  fix m assume mopen: "m open"
  hence "m \<subseteq> carrier" by auto
  hence "carrier \<inter> m = m" by auto
  thus "carr T \<inter> id -` m open" using mopen
    by auto
qed

lemma (in discrete) continuous:
  fixes f and S (structure) and fimage
  assumes "func f T S" defines "fimage \<equiv> fimg S f"
  shows "continuous f T S"
proof -
  interpret func f T S fimage by fact fact
  show ?thesis by (auto intro!: continuousI)
qed

lemma (in indiscrete) continuous:
  fixes S (structure)
  assumes "topology S"
  fixes f and fimage
  assumes "func f S T" defines "fimage \<equiv> fimg T f"
  shows "continuous f S T"
proof -
  interpret S: topology S by fact
  interpret func f S T fimage by fact fact
  show ?thesis by (auto del: S.Int_open intro!: continuousI)
qed

subsection\<open>Filters\<close>

definition
  fbas :: "'a top \<Rightarrow> 'a set set \<Rightarrow> bool" ("fbase\<index>") where
  "fbas T B \<longleftrightarrow> {} \<notin> B \<and> B \<noteq> {} \<and>
              (\<forall> a\<in>B. \<forall> b\<in>B. \<exists> c\<in>B. c \<subseteq> a \<inter> b)"

definition
  filters :: "'a top \<Rightarrow> 'a set set set"      ("Filters\<index>") where
  "filters T = { F. {} \<notin> F \<and> \<Union>F \<subseteq> carr T \<and>
                (\<forall> A B. A\<in>F \<and> B\<in>F \<longrightarrow> A\<inter>B \<in> F) \<and>
                (\<forall> A B. A\<in>F \<and> A\<subseteq>B \<and> B \<subseteq> carr T \<longrightarrow> B \<in> F) }"

definition
  ultr :: "'a top \<Rightarrow> 'a set set \<Rightarrow> bool"      ("ultra\<index>") where
  "ultr T F \<longleftrightarrow> (\<forall> A. A \<subseteq> carr T \<longrightarrow> A \<in> F \<or> (carr T - A) \<in> F)"

lemma filtersI [intro]:
  fixes T (structure)
  assumes a1: "{} \<notin> F"
  and a2: "\<Union>F \<subseteq> carrier"
  and a3: "\<And> A B. \<lbrakk> A \<in> F; B \<in> F \<rbrakk> \<Longrightarrow> A \<inter> B \<in> F"
  and a4: "\<And> A B. \<lbrakk> A \<in> F; A \<subseteq> B; B \<subseteq> carrier \<rbrakk> \<Longrightarrow> B \<in> F"
  shows "F \<in> Filters"
  using a1 a2
  by (auto simp add: filters_def intro: a3 a4)


lemma filtersE:
  assumes a1: "F \<in> filters T"
  and R: "\<lbrakk> {} \<notin> F;
            \<Union>F \<subseteq> carr T;
            \<forall> A B. A\<in>F \<and>  B\<in>F \<longrightarrow> A\<inter>B \<in> F;
            \<forall> A B. A\<in>F \<and> A\<subseteq>B \<and> B\<subseteq> carr T \<longrightarrow> B \<in> F
          \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using a1
  apply (simp add: filters_def)
  apply (rule R)
  apply ((erule conjE)+, assumption)+
  done


lemma filtersD1:
  "F \<in> filters T \<Longrightarrow> {} \<notin> F"
  by (erule filtersE)


lemma filtersD2:
  "F \<in> filters T \<Longrightarrow> \<Union>F \<subseteq> carr T"
  by (erule filtersE)


lemma filtersD3:
  "\<lbrakk> F \<in> filters T; A\<in>F;  B\<in>F \<rbrakk> \<Longrightarrow> A \<inter> B \<in> F"
  by (blast elim: filtersE)


lemma filtersD4:
  "\<lbrakk> F \<in> filters T; A \<subseteq> B; B \<subseteq> carr T; A\<in>F \<rbrakk> \<Longrightarrow> B \<in> F"
  by (blast elim: filtersE)

locale filter = carrier T for F and T (structure) +
  assumes F_filter: "F \<in> Filters"
  notes not_empty [iff]       = filtersD1 [OF F_filter]
  and   union_carr [iff]      = filtersD2 [OF F_filter]
  and   filter_inter [intro!, simp] = filtersD3 [OF F_filter]
  and   filter_greater [dest] = filtersD4 [OF F_filter]

lemma (in filter) elem_carrier [elim]:
  assumes A: "A \<in> F"
  assumes R: "\<lbrakk> A \<subseteq> carrier; A \<noteq> {} \<rbrakk> \<Longrightarrow> R"
  shows "R"
proof-
  have "\<Union>F \<subseteq> carrier" ..
  thus ?thesis using A by (blast intro: R)
qed


lemma empty_filter [iff]: "{} \<in> filters T"
  by auto

lemma (in filter) contains_carrier [intro, simp]:
  assumes F_not_empty: "F\<noteq>{}"
  shows "carrier \<in> F"
proof-
  from F_not_empty obtain A where  "A \<subseteq> carrier" "A \<in> F"
    by auto
  thus ?thesis by auto
qed

lemma nonempty_filter_implies_nonempty_carrier:
  fixes T (structure)
  assumes F_filter: "F \<in> Filters"
  and F_not_empty: "F \<noteq> {}"
  shows "carrier \<noteq> {}"
proof-
  from assms have "carrier \<in> F"
    by (auto dest!: filter.contains_carrier [OF filter.intro])
  thus ?thesis using F_filter
    by(auto dest: filtersD1)
qed

lemma carrier_singleton_filter:
  fixes T (structure)
  shows "carrier \<noteq> {} \<Longrightarrow> {carrier} \<in> Filters"
  by auto


lemma (in topology) nhds_filter:
  "nhds x \<in> Filters"
  by (auto dest: nhds_greater intro!: filtersI nhds_inter)

lemma fimage_filter:
  fixes f and S (structure) and T (structure) and fimage
  assumes "func f S T" defines "fimage \<equiv> fimg T f"
  fixes F assumes "filter F S"
  shows "fimage F \<in> Filters\<^bsub>T\<^esub>"
proof -
  interpret func f S T fimage by fact fact
  interpret filter F S by fact
  show ?thesis proof
    fix A B assume "A \<in> fimage F" "B \<in> fimage F"
    then obtain a b where
      AY: "A\<subseteq>carrier\<^bsub>T\<^esub>" and aF: "a\<in>F" and fa: "f ` a \<subseteq> A" and
      BY: "B\<subseteq>carrier\<^bsub>T\<^esub>" and bF: "b\<in>F" and fb: "f ` b \<subseteq> B"
      by (auto)
    from AY BY have "A\<inter>B \<subseteq> carrier\<^bsub>T\<^esub>" by auto
    moreover from aF bF have "a \<inter> b \<in> F" by auto
    moreover from aF bF fa fb have "f`(a \<inter> b) \<subseteq> A \<inter> B" by auto
    ultimately show "A\<inter>B \<in> fimage F" by auto
  qed auto
qed

lemma Int_filters:
  fixes F and T (structure) assumes "filter F T"
  fixes E assumes "filter E T"
  shows "F \<inter> E \<in> Filters"
proof -
  interpret filter F T by fact
  interpret filter E T by fact
  show ?thesis by auto
qed

lemma ultraCI [intro!]:
  fixes T (structure)
  shows "(\<And>A. \<lbrakk> A \<subseteq> carrier; carrier - A \<notin> F \<rbrakk> \<Longrightarrow> A \<in> F) \<Longrightarrow> ultra F"
  by (auto simp: ultr_def)


lemma ultraE:
  fixes T (structure)
  shows "\<lbrakk> ultra F; A \<subseteq> carrier;
     A \<in> F \<Longrightarrow> R;
     carrier - A \<in> F \<Longrightarrow> R
  \<rbrakk> \<Longrightarrow> R"
by (auto simp: ultr_def)

lemma ultraD:
  fixes T (structure)
  shows "\<lbrakk> ultra F; A \<subseteq> carrier; A \<notin> F \<rbrakk> \<Longrightarrow> (carrier - A) \<in> F"
  by (erule ultraE) auto

locale ultra_filter = filter +
  assumes ultra: "ultra F"
  notes ultraD = ultraD [OF ultra]
  notes ultraE [elim] = ultraE [OF ultra]


lemma (in ultra_filter) max:
  fixes E assumes "filter E T"
  assumes fsube: "F \<subseteq> E"
  shows "E \<subseteq> F"
proof -
  interpret filter E T by fact
  show ?thesis proof
    fix x assume xinE: "x \<in> E"
    hence "x \<subseteq> carrier" ..
    hence "x \<in> F \<or> carrier - x \<in> F" by auto
    thus "x \<in> F"
    proof clarify
      assume "carrier - x \<in> F"
      hence "carrier - x \<in> E" using fsube ..
      with xinE have "x \<inter> (carrier - x) \<in> E" ..
      hence False by auto
      thus "x \<in> F" ..
    qed
  qed
qed

lemma (in filter) max_ultra:
  assumes carrier_not_empty: "carrier \<noteq> {}"
  and fmax: "\<forall> E \<in> Filters. F \<subseteq> E \<longrightarrow> F = E"
  shows "ultra F"
proof

  fix A let ?CA = "carrier - A"
  assume A_subset_carrier: "A \<subseteq> carrier"
     and CA_notin_F: "?CA \<notin> F"

  let ?E  = "{V. \<exists> U\<in>F. V \<subseteq> carrier \<and> A \<inter> U \<subseteq> V}"
  have "?E \<in> Filters"
  proof
    show "{} \<notin> ?E"
    proof clarify
      fix U assume U_in_F: "U \<in> F" and "A \<inter> U \<subseteq> {}"
      hence "U \<subseteq> ?CA" by auto
      with U_in_F have "?CA \<in> F" by auto
      with CA_notin_F show False ..
    qed
  next show "\<Union>?E \<subseteq> carrier" by auto
  next fix a b assume "a \<in> ?E" and "b \<in> ?E"
    then obtain u v where props: "u \<in> F" "a \<subseteq> carrier" "A \<inter> u \<subseteq> a"
      "v \<in> F" "b \<subseteq> carrier" "A \<inter> v \<subseteq> b" by auto
    hence "(u \<inter> v) \<in> F" "a \<inter> b \<subseteq> carrier" "A \<inter> (u \<inter> v) \<subseteq> a \<inter> b"
      by auto
    thus "a \<inter> b \<in> ?E" by auto
  next fix a b assume "a \<in> ?E" and asub: "a \<subseteq> b" and bsub: "b \<subseteq> carrier"
    thus "b \<in> ?E" by blast
  qed

  moreover have "F \<subseteq> ?E" by auto

  moreover from carrier_not_empty
  have "{carrier} \<in> Filters" by auto
  hence "F \<noteq> {}" using fmax by blast
  hence "A \<in> ?E" using A_subset_carrier by auto

  ultimately show "A \<in> F" using fmax by auto

qed

lemma filter_chain_lemma:
  fixes T (structure) and F
  assumes "filter F T"
  assumes C_chain: "C \<in> chains {V. V \<in> Filters \<and> F \<subseteq> V}" (is "C \<in> chains ?FF")
  shows "\<Union>(C \<union> {F}) \<in> Filters" (is "?E \<in> Filters")
proof-
  interpret filter F T by fact
  from C_chain have C_subset_FF[dest]: "\<And> x. x\<in>C \<Longrightarrow> x \<in> ?FF" and
    C_ordered: "\<forall> A \<in> C. \<forall> B \<in> C. A \<subseteq> B \<or> B \<subseteq> A"
    by (auto simp: chains_def chain_subset_def)

  show ?thesis
  proof    
    show "{} \<notin> ?E" by (auto dest: filtersD1)
  next
    show "\<Union>?E \<subseteq> carrier" by (blast dest: filtersD2)
  next
    fix a b assume a_in_E: "a \<in> ?E" and a_subset_b: "a \<subseteq> b"
  and b_subset_carrier: "b \<subseteq> carrier"
    thus "b \<in> ?E" by (blast dest: filtersD4)
  next
    fix a b assume a_in_E: "a \<in> ?E" and b_in_E: "b \<in> ?E"
    then obtain A B where A_in_chain: "A \<in> C \<union> {F}" and B_in_chain: "B \<in> C \<union> {F}"
      and a_in_A: "a \<in> A" and b_in_B: "b \<in> B" and A_filter: "A \<in> Filters"
      and B_filter: "B \<in> Filters"
      by auto
    with C_ordered have "A \<subseteq> B \<or> B \<subseteq> A" by auto
    thus "a\<inter>b \<in> ?E"
    proof
      assume "A \<subseteq> B"
      with a_in_A have "a \<in> B" ..
      with B_filter b_in_B have "a\<inter>b \<in> B" by (intro filtersD3)
      with B_in_chain show ?thesis ..
    next
      assume "B \<subseteq> A" \<comment> \<open>Symmetric case\<close>
      with  b_in_B A_filter a_in_A A_in_chain
      show ?thesis by (blast intro: filtersD3)
    qed
  qed
qed

lemma expand_filter_ultra:
  fixes T (structure)
  assumes carrier_not_empty: "carrier \<noteq> {}"
  and     F_filter: "F \<in> Filters"
  and     R: "\<And>U.  \<lbrakk> U \<in> Filters;  F \<subseteq> U; ultra U \<rbrakk> \<Longrightarrow> R"
  shows "R"
proof-
  let ?FF = "{V. V \<in> Filters \<and> F \<subseteq> V}"
  have "\<forall> C \<in> chains ?FF. \<exists>y \<in> ?FF. \<forall>x \<in> C. x \<subseteq> y"
  proof clarify
    fix C let ?M = "\<Union>(C \<union> {F})"
    assume C_in_chain: "C \<in> chains ?FF"
    hence "?M \<in> ?FF" using F_filter
      by (auto dest: filter_chain_lemma [OF filter.intro])
    moreover have "\<forall> x \<in> C. x \<subseteq> ?M" using C_in_chain
      by (auto simp: chain_def)
    ultimately show "\<exists>y\<in>?FF. \<forall>x\<in>C. x \<subseteq> y"
      by auto
  qed then obtain U where
    U_FFilter: "U \<in> ?FF" and U_max: "\<forall> V \<in> ?FF. U \<subseteq> V \<longrightarrow> V = U"
    by (blast dest!: Zorn_Lemma2)
  hence U_filter: "U \<in> Filters" and F_subset_U: "F \<subseteq> U"
    by auto
  moreover from U_filter carrier_not_empty have "ultra U"
  proof (rule filter.max_ultra [OF filter.intro], clarify)
    fix E x assume "E \<in> Filters" and  U_subset_E: "U \<subseteq> E" and x_in_E: "x \<in> E"
    with F_subset_U have "E \<in> ?FF" by auto 
    with U_subset_E x_in_E U_max show "x \<in> U" by blast
  qed
  ultimately show ?thesis
    by (rule R)
qed


subsection \<open>Convergence\<close>

definition
  converges :: "'a top \<Rightarrow> 'a set set \<Rightarrow> 'a \<Rightarrow> bool" ("(_ \<longlongrightarrow>\<index> _)" [55, 55] 55) where
  "converges T F x \<longleftrightarrow> nhd T x \<subseteq> F"

notation
  converges  ("(_ \<turnstile> _ \<longrightarrow> _)" [55, 55, 55] 55)

definition
  cnvgnt :: "'a top \<Rightarrow> 'a set set \<Rightarrow> bool" ("_ convergent\<index>" [50] 50) where
  "cnvgnt T F \<longleftrightarrow> (\<exists> x \<in> carr T. converges T F x)"

definition
  limites :: "'a top \<Rightarrow> 'a set set \<Rightarrow> 'a set" ("lims\<index>") where
  "limites T F = {x. x \<in> carr T \<and> T \<turnstile> F \<longrightarrow> x}"

definition
  limes :: "'a top \<Rightarrow> 'a set set \<Rightarrow> 'a" ("lim\<index>") where
  "limes T F = (THE x. x \<in> carr T \<and> T \<turnstile> F \<longrightarrow> x)"


lemma (in carrier) convergesI [intro]:
  "nhds x \<subseteq> F \<Longrightarrow> F \<longlongrightarrow> x"
  by (auto simp: converges_def)

lemma (in carrier) convergesE [elim]:
  "\<lbrakk> F \<longlongrightarrow> x; nhds x \<subseteq> F \<Longrightarrow> R \<rbrakk> \<Longrightarrow> R"
  by (auto simp: converges_def)

lemma (in carrier) convergentI [intro?]:
  "\<lbrakk> F \<longlongrightarrow> x; x \<in> carrier \<rbrakk> \<Longrightarrow> F convergent"
  by (auto simp: cnvgnt_def)

lemma (in carrier) convergentE [elim]:
   "\<lbrakk> F convergent;
     \<And> x. \<lbrakk> F \<longlongrightarrow> x; x \<in> carrier \<rbrakk> \<Longrightarrow> R
    \<rbrakk> \<Longrightarrow> R"
  by (auto simp: cnvgnt_def)

lemma (in continuous) fimage_converges:
  assumes   xpoint: "x \<in> carrier"
  and       conv:   "F \<longlongrightarrow>\<^bsub>S\<^esub> x"
  shows    "fimage F \<longlongrightarrow>\<^bsub>T\<^esub> (f x)"
proof (rule, rule)
  fix v assume vnhd: "v \<in> nhds\<^bsub>T\<^esub> (f x)"
  then obtain m where v_subset_carrier: "v \<subseteq> carrier\<^bsub>T\<^esub>"
    and m_open: "m open\<^bsub>T\<^esub>"
    and m_subset_v: "m \<subseteq> v"
    and fx_in_m: "f x \<in> m" ..
  let ?m' = "carrier \<inter> f-`m"
  from fx_in_m xpoint have "x \<in> ?m'" by auto
  with m_open have "?m' \<in> nhds x" by auto
  with conv have "?m' \<in> F" by auto
  moreover from m_subset_v have "f`?m' \<subseteq> v" by auto
  ultimately show "v \<in> fimage F" using v_subset_carrier by auto
qed

corollary (in continuous) fimage_convergent [intro!]:
  "F convergent\<^bsub>S\<^esub> \<Longrightarrow> fimage F convergent\<^bsub>T\<^esub>"
  by (blast intro: convergentI fimage_converges)

lemma (in topology) closure_convergent_filter:
assumes xclosure: "x \<in> closure A"
  and xpoint: "x \<in> carrier"
  and asub: "A \<subseteq> carrier"
  and H: "\<And>F. \<lbrakk> F \<in> Filters; F \<longlongrightarrow> x; A \<in> F\<rbrakk> \<Longrightarrow> R"
  shows "R"
proof-
  let ?F = "{v. v \<subseteq> carrier \<and> (\<exists> u \<in> nhds x. u \<inter> A \<subseteq> v)}"
  have "?F \<in> Filters"
  proof
    from asub xclosure have adhx: "x adh A" by (rule closure_imp_adh)
    thus "{} \<notin> ?F" by (auto elim: adhCE)
  next show "\<Union>?F \<subseteq> carrier" by auto
  next fix a b assume aF: "a \<in> ?F" and bF: "b \<in> ?F"
    then obtain u v where
      aT: "a \<subseteq> carrier" and bT: "b \<subseteq> carrier" and
      ux: "u \<in> nhds x" and vx: "v \<in> nhds x" and
      uA: "u \<inter> A \<subseteq> a" and vA: "v \<inter> A \<subseteq> b"
      by auto
    moreover from ux vx have "u \<inter> v \<in> nhds x"
      by (auto intro: nhds_inter)
    moreover from uA vA have "(u \<inter> v) \<inter> A \<subseteq> a \<inter> b" by auto
    ultimately show  "a \<inter> b \<in> ?F" by auto
  next fix a b assume aF: "a \<in> ?F" and ab: "a \<subseteq> b" and bT: "b \<subseteq> carrier"
    then obtain u
      where at: "a \<subseteq> carrier" and ux: "u \<in> nhds x" and  uA: "u \<inter> A \<subseteq> a"
      by auto
    moreover from ux bT have "u \<union> b \<in> nhds x"
      by (auto intro: nhds_greater)
    moreover from uA ab have "(u \<union> b) \<inter> A \<subseteq> b" by auto
    ultimately show "b \<in> ?F" by auto
  qed
  moreover have "?F \<longlongrightarrow> x"
    by auto
  moreover from asub xpoint have "A \<in> ?F"
    by blast
  ultimately show ?thesis
    by (rule H)
qed


lemma convergent_filter_closure:
  fixes F and T (structure)
  assumes "filter F T"
  assumes converge: "F \<longlongrightarrow> x"
  and   xpoint: "x \<in> carrier"
  and   AF: "A \<in> F"
  shows "x \<in> closure A"
proof-
  interpret filter F T by fact
  have "x adh A"
  proof
    fix u assume unhd: "u \<in> nhds x"
    with converge have "u \<in> F" by auto
    with AF have "u \<inter> A \<in> F" by auto
    thus "u \<inter> A \<noteq> {}"  by blast
  qed
  with xpoint show ?thesis
    by (rule adh_imp_closure)
qed


subsection\<open>Separation\<close>

subsubsection\<open>T0 spaces\<close>

locale T0 = topology +
  assumes T0: "\<forall> x \<in> carrier. \<forall> y \<in> carrier. x \<noteq> y \<longrightarrow>
               (\<exists> u \<in> nhds x. y \<notin> u) \<or> (\<exists> v \<in> nhds y. x \<notin> v)"


lemma (in T0) T0_eqI:
  assumes points: "x \<in> carrier" "y \<in> carrier"
  and R1: "\<And>u. u \<in> nhds x \<Longrightarrow> y \<in> u"
  and R2: "\<And>v. v \<in> nhds y \<Longrightarrow> x \<in> v"
  shows "x = y"
  using T0 points
  by (auto intro: R1 R2)


lemma (in T0) T0_neqE [elim]:
  assumes x_neq_y: "x \<noteq> y"
  and points: "x \<in> carrier" "y \<in> carrier"
  and R1: "\<And>u. \<lbrakk> u \<in> nhds x; y \<notin> u \<rbrakk> \<Longrightarrow> R"
  and R2: "\<And>v. \<lbrakk> v \<in> nhds y; x \<notin> v \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using T0 points x_neq_y
  by (auto intro: R1 R2)

subsubsection\<open>T1 spaces\<close>

locale T1 = T0 +
  assumes DT01: "\<forall> x \<in> carrier. \<forall> y \<in> carrier. x \<noteq> y \<longrightarrow>
               (\<exists> u \<in> nhds x. y \<notin> u) = (\<exists> v \<in> nhds y. x \<notin> v)"


lemma (in T1) T1_neqE [elim]:
  assumes x_neq_y: "x \<noteq> y"
  and points: "x \<in> carrier" "y \<in> carrier"
  and R [intro] : "\<And>u v. \<lbrakk> u \<in> nhds x; v \<in> nhds y; y \<notin> u; x \<notin> v\<rbrakk> \<Longrightarrow> R"
  shows "R"
proof-
  from DT01 x_neq_y points
  have nhd_iff: "(\<exists> v \<in> nhds y. x \<notin> v) = (\<exists> u \<in> nhds x. y \<notin> u)"
    by force
  from x_neq_y points show ?thesis
  proof
    fix u assume u_nhd: "u \<in> nhds x" and y_notin_u: "y \<notin> u"
    with nhd_iff obtain v where  "v \<in> nhds y" and "x \<notin> v" by blast
    with u_nhd y_notin_u show "R" by auto
  next
    fix v assume v_nhd: "v \<in> nhds y" and x_notin_v: "x \<notin> v"
    with nhd_iff obtain u where  "u \<in> nhds x" and "y \<notin> u" by blast
    with v_nhd x_notin_v show "R" by auto
  qed
qed

declare (in T1) T0_neqE [rule del]

lemma (in T1) T1_eqI:
  assumes points: "x \<in> carrier" "y \<in> carrier"
  and R1: "\<And>u v. \<lbrakk> u \<in> nhds x; v \<in> nhds y; y \<notin> u \<rbrakk> \<Longrightarrow>  x \<in> v"
  shows "x = y"
proof (rule ccontr)
  assume "x \<noteq> y" thus False using points
    by (auto intro: R1)
qed

lemma (in T1) singleton_closed [iff]: "{x} closed"
proof (cases "x \<in> carrier")
  case False hence "carrier - {x} = carrier"
    by auto
  thus ?thesis by (clarsimp intro!: closedI)
next  
  case True show ?thesis
  proof (rule closedI, rule open_kriterion)
    fix y assume "y \<in> carrier - {x}"
    hence "y \<in> carrier" "x \<noteq> y" by auto
    with True obtain v where "v \<in> nhds y" "x \<notin> v"
      by (elim T1_neqE)
    then obtain m where "m open" "y\<in>m" "m \<subseteq> carrier - {x}"
      by (auto elim!: nhdE)
    thus "\<exists>m. m open \<and> y \<in> m \<and> m \<subseteq> carrier - {x}"
      by blast
  qed
qed

lemma (in T1) finite_closed:
  assumes finite: "finite A"
  shows "A closed"
  using finite
proof induct
  case empty show ?case ..
next
  case (insert x F)
  hence "{x} \<union> F closed" by blast
  thus ?case by simp
qed

subsubsection\<open>T2 spaces (Hausdorff spaces)\<close>

locale T2 = T1 +
  assumes T2: "\<forall> x \<in> carrier. \<forall> y \<in> carrier. x \<noteq> y
  \<longrightarrow> (\<exists> u \<in> nhds x. \<exists> v \<in> nhds y. u \<inter> v = {})"

lemma T2_axiomsI:
  fixes T (structure)
  shows
  "(\<And>x y. \<lbrakk> x \<in> carrier; y \<in> carrier; x \<noteq> y \<rbrakk> \<Longrightarrow> 
           \<exists> u \<in> nhds x. \<exists> v \<in> nhds y. u \<inter> v = {})
   \<Longrightarrow> T2_axioms T"
  by (auto simp: T2_axioms_def)

declare (in T2) T1_neqE [rule del]

lemma (in T2) neqE [elim]:
  assumes neq: "x \<noteq> y"
  and points: "x \<in> carrier" "y \<in> carrier"
  and R: "\<And> u v. \<lbrakk> u \<in> nhds x; v \<in> nhds y; u \<inter> v = {} \<rbrakk> \<Longrightarrow> R"
  shows R
proof-
  from T2 points neq obtain u v where
    "u \<in> nhds x" "v \<in> nhds y" "u \<inter> v = {}" by force
  thus R by (rule R)
qed

lemma (in T2) neqE2 [elim]:
  assumes neq: "x \<noteq> y"
  and points: "x \<in> carrier" "y \<in> carrier"
  and R: "\<And> u v. \<lbrakk> u \<in> nhds x; v \<in> nhds y; z \<notin> u \<or> z \<notin> v\<rbrakk> \<Longrightarrow> R"
  shows R
proof-
  from T2 points neq obtain u v where
    "u \<in> nhds x" "v \<in> nhds y" "u \<inter> v = {}" by force
  thus R by (auto intro: R)
qed

lemma T2_axiom_implies_T1_axiom:
  fixes T (structure)
  assumes T2: "\<forall> x \<in> carrier. \<forall> y \<in> carrier. x \<noteq> y
  \<longrightarrow> (\<exists> u \<in> nhds x. \<exists> v \<in> nhds y. u \<inter> v = {})"
  shows "T1_axioms T"
proof (rule T1_axioms.intro, clarify)
  interpret carrier T .
  fix x y assume neq: "x \<noteq> y" and
    points: "x \<in> carrier" "y \<in> carrier"
  with T2 obtain u v
    where unhd: "u \<in> nhds x" and
    vnhd: "v \<in> nhds y" and Int_empty: "u \<inter> v = {}"
    by force
  show "(\<exists>u\<in>nhds x. y \<notin> u) = (\<exists>v\<in>nhds y. x \<notin> v)"
  proof safe
    show "\<exists>v\<in>nhds y. x \<notin> v"
    proof
      from unhd have "x \<in> u" by auto
      with Int_empty show "x \<notin> v" by auto
    qed (rule vnhd)
  next
    show "\<exists>u\<in>nhds x. y \<notin> u"
    proof
      from vnhd have "y \<in> v" by auto
      with Int_empty show "y \<notin> u" by auto
    qed (rule unhd)
  qed
qed

lemma T2_axiom_implies_T0_axiom:
  fixes T (structure)
  assumes T2: "\<forall> x \<in> carrier. \<forall> y \<in> carrier. x \<noteq> y
  \<longrightarrow> (\<exists> u \<in> nhds x. \<exists> v \<in> nhds y. u \<inter> v = {})"
  shows "T0_axioms T"
proof (rule T0_axioms.intro, clarify)
  interpret carrier T .
  fix x y assume neq: "x \<noteq> y" and
    points: "x \<in> carrier" "y \<in> carrier"
  with T2 obtain u v
    where unhd: "u \<in> nhds x" and
    vnhd: "v \<in> nhds y" and Int_empty: "u \<inter> v = {}"
    by force
  show "\<exists>u\<in>nhds x. y \<notin> u"
  proof
    from vnhd have "y \<in> v" by auto
    with Int_empty show "y \<notin> u" by auto
  qed (rule unhd)
qed


lemma T2I:
  fixes T (structure) assumes "topology T"
  assumes I: "\<And>x y. \<lbrakk> x \<in> carrier; y \<in> carrier; x \<noteq> y \<rbrakk> \<Longrightarrow> 
           \<exists> u \<in> nhds x. \<exists> v \<in> nhds y. u \<inter> v = {}"
  shows "T2 T"
proof -
  interpret topology T by fact
  show ?thesis apply intro_locales
    apply (rule T2_axiom_implies_T0_axiom)
    using I apply simp
    apply (rule T2_axiom_implies_T1_axiom)
    using I apply simp
    apply unfold_locales
    using I apply simp
    done
qed

lemmas T2E = T2.neqE
lemmas T2E2 = T2.neqE2

lemma (in T2) unique_convergence:
fixes F assumes "filter F T"
assumes points: "x \<in> carrier" "y \<in> carrier"
  and   Fx:    "F \<longlongrightarrow> x"
  and   Fy:    "F \<longlongrightarrow> y"
  shows "x = y"
proof -
  interpret filter F T by fact
  show ?thesis proof (rule ccontr)
    assume "x \<noteq> y" then obtain u v
      where unhdx: "u \<in> nhds x"
      and   vnhdy: "v \<in> nhds y"
      and   inter: "u \<inter> v = {}"
      using points ..
    hence "u \<in> F" and "v \<in> F" using Fx Fy by auto
    hence "u \<inter> v \<in> F" ..
    with inter show "False" by auto
  qed
qed

lemma (in topology) unique_convergence_implies_T2 [rule_format]:
  assumes unique_convergence: 
  "\<And>x y F.\<lbrakk> x \<in> carrier; y \<in> carrier; F\<in>Filters; 
    F \<longlongrightarrow> x; F \<longlongrightarrow> y \<rbrakk> \<Longrightarrow> x = y"
  shows "T2 T"

proof (rule T2I)
  show "topology T" ..
next
  fix x y assume points: "x \<in> carrier" "y \<in> carrier"
    and neq: "x \<noteq> y"
  show "\<exists>u\<in>nhds x. \<exists>v\<in>nhds y. u \<inter> v = {}"
  proof (rule ccontr, simp)
    assume non_empty_Int: "\<forall>u\<in>nhds x. \<forall>v\<in>nhds y. u \<inter> v \<noteq> {}"
    let ?E = "{w. w\<subseteq>carrier \<and> (\<exists> u \<in> nhds x. \<exists> v \<in> nhds y. u\<inter>v \<subseteq> w)}"

    have "?E \<in> Filters"
    proof rule
      show "{} \<notin> ?E" using non_empty_Int by auto
    next show "\<Union>?E \<subseteq> carrier" by auto
    next fix a b assume "a \<in> ?E" "b \<in> ?E"
      then obtain ua va ub vb
        where "a \<subseteq> carrier" "ua \<in> nhds x" "va \<in> nhds y" "ua \<inter> va \<subseteq> a"
              "b \<subseteq> carrier" "ub \<in> nhds x" "vb \<in> nhds y" "ub \<inter> vb \<subseteq> b"
        by auto
      hence "a\<inter>b \<subseteq> carrier" "ua \<inter> ub \<in> nhds x" "va \<inter> vb \<in> nhds y" "(ua \<inter> ub) \<inter> (va \<inter> vb) \<subseteq> a \<inter> b"
        by (auto intro!: nhds_inter simp: Int_ac)
      thus "a \<inter> b \<in> ?E" by blast
    next fix a b assume "a \<in> ?E" and a_sub_b:
        "a \<subseteq> b" and b_sub_carrier: "b \<subseteq> carrier"
      then obtain u v
        where u_int_v: "u \<inter> v \<subseteq> a" and nhds: "u \<in> nhds x" "v \<in> nhds y"
        by auto
      from u_int_v a_sub_b have "u \<inter> v \<subseteq> b" by auto
      with b_sub_carrier nhds show "b \<in> ?E" by blast
    qed

    moreover have "?E \<longlongrightarrow> x"
    proof (rule, rule)
      fix w assume "w \<in> nhds x"
      moreover have "carrier \<in> nhds y" using \<open>y \<in> carrier\<close> ..
      moreover have "w \<inter> carrier \<subseteq> w" by auto
      ultimately show "w \<in> ?E" by auto
    qed

    moreover have "?E \<longlongrightarrow> y"
    proof (rule, rule)
      fix w assume "w \<in> nhds y"
      moreover have "carrier \<in> nhds x" using \<open>x \<in> carrier\<close> ..
      moreover have "w \<inter> carrier \<subseteq> w" by auto
      ultimately show "w \<in> ?E" by auto
    qed

    ultimately have "x = y" using points
      by (auto intro:  unique_convergence)
    thus False using neq by contradiction
  qed
qed

lemma (in T2) limI [simp]:
  assumes filter: "F \<in> Filters"
  and      point: "x \<in> carrier"
  and  converges: "F \<longlongrightarrow> x"
  shows "lim F = x"
  using filter converges point
  by (auto simp: limes_def dest: unique_convergence [OF filter.intro])

lemma (in T2) convergent_limE:
  assumes convergent: "F convergent"
  and filter: "F \<in> Filters"
  and R: "\<lbrakk>  lim F \<in> carrier; F \<longlongrightarrow> lim F \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using convergent filter
  by (force intro!: R)

lemma image_lim_subset_lim_fimage:
  fixes f and S (structure) and T (structure) and fimage
  defines "fimage \<equiv> fimg T f"
  assumes "continuous f S T"
  shows "F \<in> Filters\<^bsub>S\<^esub> \<Longrightarrow> f`(lims F) \<subseteq> lims\<^bsub>T\<^esub> (fimage F)"
proof -
  interpret continuous f S T fimage by fact fact
  show ?thesis by (auto simp: limites_def intro: fimage_converges)
qed

subsubsection\<open>T3 axiom and regular spaces\<close>


locale T3 = topology +
  assumes T3: "\<forall> A. \<forall> x \<in> carrier - A. A \<subseteq> carrier \<and> A closed \<longrightarrow> 
               (\<exists> B. \<exists> U \<in> nhds x. B open \<and> A \<subseteq> B \<and> B \<inter> U = {})"

lemma (in T3) T3E:
  assumes H: "A \<subseteq> carrier" "A closed" "x \<in> carrier" "x\<notin> A"
  and     R: "\<And> B U. \<lbrakk> A \<subseteq> B; B open; U \<in> nhds x; B \<inter> U = {} \<rbrakk> \<Longrightarrow> R"
  shows "R"
  using T3 H
  by (blast dest: R)

locale regular = T1 + T3

lemma regular_implies_T2:
  fixes T (structure)
  assumes "regular T"
  shows "T2 T"
proof (rule T2I)
  interpret regular T by fact
  show "topology T" ..
next
  interpret regular T by fact
  fix x y assume "x \<in> carrier" "y \<in> carrier" "x \<noteq> y"
  hence "{y} \<subseteq> carrier" "{y} closed" "x \<in> carrier" "x \<notin> {y}" by auto
  then obtain B U where B: "{y} \<subseteq> B" "B open" and U: "U \<in> nhds x" "B \<inter> U = {}"
    by (elim T3E)
  from B have "B \<in> nhds y" by auto
  thus "\<exists>u\<in>nhds x. \<exists>v\<in>nhds y. u \<inter> v = {}"  using U
    by blast
qed


subsubsection\<open>T4 axiom and normal spaces\<close> 

locale T4 = topology +
  assumes T4: "\<forall> A B. A closed \<and> A \<subseteq> carrier \<and> B closed \<and> B \<subseteq> carrier \<and>
  A \<inter> B = {} \<longrightarrow> (\<exists> U V. U open \<and> A \<subseteq> U \<and> V open \<and> B \<subseteq> V \<and> U \<inter> V = {})"

lemma (in T4) T4E:
  assumes H: "A closed" "A \<subseteq> carrier" "B closed" "B \<subseteq> carrier" "A\<inter>B = {}"
  and R: "\<And> U V. \<lbrakk> U open; A \<subseteq> U; V open; B \<subseteq> V; U \<inter> V = {} \<rbrakk> \<Longrightarrow> R"
  shows "R"
proof-
  from H T4 have "(\<exists> U V. U open \<and> A \<subseteq> U \<and> V open \<and> B \<subseteq> V \<and> U \<inter> V = {})"
    by auto
  then obtain U V where "U open" "A \<subseteq> U" "V open" "B \<subseteq> V" "U \<inter> V = {}"
    by auto
  thus ?thesis by (rule R)
qed
     

locale normal = T1 + T4

lemma normal_implies_regular:
  fixes T (structure)
  assumes "normal T"
  shows  "regular T"
proof -
  interpret normal T by fact
  show ?thesis
  proof intro_locales
    show "T3_axioms T"
    proof (rule T3_axioms.intro, clarify)
      fix A x assume x: "x \<in> carrier" "x \<notin> A" and A: "A closed" "A \<subseteq> carrier"
      from x have "{x} closed" "{x} \<subseteq> carrier" "A \<inter> {x} = {}" by auto
      with A obtain U V
        where "U open" "A \<subseteq> U" "V open" "{x} \<subseteq> V" "U \<inter> V = {}" by (rule T4E)
      thus "\<exists>B. \<exists>U\<in>nhds x. B open \<and> A \<subseteq> B \<and> B \<inter> U = {}" by auto
    qed
  qed
qed

(*

subsection{*Compactness*}

definition
  covers :: "'a top \<Rightarrow> 'a set set \<Rightarrow> bool" ("_ covering\<index>" [50] 50) where
  "covers T D = (\<Union>D = carr T)"

definition
  card_le :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infix "cardle" 50) where
  "A cardle B \<longleftrightarrow> (\<exists>f. f \<in> SUR B A)"

definition
  countable :: "'a set \<Rightarrow> bool" where
  "countable A = A cardle Nat"

lemma cardle_refl: "A cardle A"
proof-
  have "id : A \<rightarrow> A" by (auto intro: funcsetI)
  moreover have "\<forall> y\<in>A. \<exists>x\<in>A. y = id x" by auto
  ultimately show ?thesis
    by (auto simp add: card_le_def SUR_def)
qed

locale quasicompact = topology +
  assumes quasi: "\<forall> C. C covering \<and> (\<forall> m\<in>C. m open) \<longrightarrow>
  (\<exists> D. D covering \<and> finite D \<and> D \<subseteq> C)"
*)

end
