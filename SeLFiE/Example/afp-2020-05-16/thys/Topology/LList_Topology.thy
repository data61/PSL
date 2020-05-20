(*  Title:      LList_Topology.thy
    Author:     Stefan Friedrich
    Maintainer: Stefan Friedrich
    License:    LGPL
*)

section \<open>The topology of llists\<close>

theory LList_Topology
imports Topology "Lazy-Lists-II.LList2"
begin

subsection\<open>The topology of all llists\<close>

text\<open>
  This theory introduces the topologies of all llists, of infinite
  llists, and of the non-empty llists. For all three cases it is
  proved that safety properties are closed sets and that liveness
  properties are dense sets. Finally, we prove in each of the the
  three different topologies the respective theorem of Alpern and
  Schneider \cite{alpern85:_defin_liven}, which states that every
  property can be represented as an intersection of a safety property
  and a liveness property.\<close>

definition
  ttop :: "'a set \<Rightarrow> 'a llist top" where
  "ttop A = topo (\<Union> s\<in>A\<^sup>\<star>. {suff A s})"

lemma ttop_topology [iff]: "topology (ttop A)"
  by (auto simp: ttop_def)


locale suffixes =
  fixes A and B
  defines [simp]: "B \<equiv> (\<Union> s\<in>A\<^sup>\<star>. {suff A s})"

locale trace_top = suffixes + topobase


lemma (in trace_top) open_iff [iff]:
  "m open = (m \<in> topo (\<Union> s\<in>A\<^sup>\<star>. {suff A s}))"
  by (simp add: T_def is_open_def)

lemma (in trace_top) suff_open [intro!]:
  "r \<in> A\<^sup>\<star> \<Longrightarrow> suff A r open"
  by auto

lemma (in trace_top) ttop_carrier: "A\<^sup>\<infinity> = carrier"
  by (auto simp: carrier_topo suff_def)

lemma (in trace_top) suff_nhd_base:
  assumes unhd: "u \<in> nhds t"
  and H: "\<And>r. \<lbrakk> r \<in> finpref A t; suff A r \<subseteq> u \<rbrakk> \<Longrightarrow> R"
  shows "R"
proof-
  from unhd obtain m where
    uA: "u \<subseteq> A\<^sup>\<infinity>" and
    mopen: "m open" and
    tm: "t \<in> m" and
    mu: "m \<subseteq> u"
    by (auto simp: ttop_carrier [THEN sym])
  from mopen tm have
    "\<exists>r \<in> finpref A t. suff A r \<subseteq> m"
  proof (induct "m")
    case (basic a)
    then obtain s where sA: "s \<in> A\<^sup>\<star>" and as: "a = suff A s" and ta: "t \<in> a"
      by auto
    from sA as ta have "s \<in> finpref A t" by (auto dest: suff_finpref)
    thus ?case using as by auto
  next case (inter a b)
    then obtain r r' where
      rt: "r \<in> finpref A t" and ra: "suff A r \<subseteq> a" and
      r't: "r' \<in> finpref A t" and r'b: "suff A r' \<subseteq> b"
      by auto
    from rt r't have "r \<le> r' \<or> r' \<le> r"
      by (auto simp: finpref_def dest: pref_locally_linear)
    thus ?case
    proof
      assume "r \<le> r'"
      hence "suff A r' \<subseteq> suff A r" by (rule suff_mono2)
      thus ?case using r't ra r'b by auto
    next assume "r' \<le> r"
      hence "suff A r \<subseteq> suff A r'" by (rule suff_mono2)
      thus ?case using rt r'b ra by auto
    qed
  next case (union M)
    then obtain v where
      "t \<in> v" and vM: "v \<in> M"
      by blast
    then obtain r where "r\<in>finpref A t" "suff A r \<subseteq> v" using union
      by auto
    thus ?case using vM by auto
  qed
  with mu show ?thesis by (auto intro: H)
qed

lemma (in trace_top) nhds_LNil [simp]: "nhds LNil = {A\<^sup>\<infinity>}"
proof
  show "nhds LNil \<subseteq> {A\<^sup>\<infinity>}"
  proof clarify
    fix x assume xnhd: "x \<in> nhds LNil"
    then obtain r
      where rfinpref: "r \<in> finpref A LNil" and suffsub: "suff A r \<subseteq> x"
      by (rule suff_nhd_base)
    from rfinpref have "r = LNil" by auto
    hence "suff A r = A\<^sup>\<infinity>" by auto
    with suffsub have "A\<^sup>\<infinity> \<subseteq> x" by auto
    moreover from xnhd have "x \<subseteq> A\<^sup>\<infinity>" by(auto simp: ttop_carrier elim!: nhdE)
    ultimately show "x = A\<^sup>\<infinity>" by auto
  qed
next
  show "{A\<^sup>\<infinity>} \<subseteq> nhds LNil" by (auto simp: ttop_carrier)
qed

lemma (in trace_top) adh_lemma:
assumes xpoint: "x \<in> A\<^sup>\<infinity>"
  and  PA: "P \<subseteq> A\<^sup>\<infinity>"
shows "(x adh P) = (\<forall> r \<in> finpref A x. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P)"
proof-
  from PA have "\<And>r. r \<in> A\<^sup>\<star> \<Longrightarrow> (\<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P) =
        (\<exists> s \<in> P. r \<le> s)"
    by (auto simp: llist_le_def iff: lapp_allT_iff)
  hence  "(\<forall> r \<in> finpref A x. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P) =
        (\<forall> r \<in> finpref A x. \<exists> s \<in> P. r \<le> s)"
    by (auto simp: finpref_def)
  also have "\<dots> = (\<forall> r \<in> finpref A x. suff A r \<inter> P \<noteq> {})"
  proof-
    have "\<And>r. (\<exists>s\<in>P. r \<le> s) = ({ra. ra \<in> A\<^sup>\<infinity> \<and> r \<le> ra} \<inter> P \<noteq> {})" using PA
      by blast
    thus ?thesis by (simp add: suff_def)
  qed
  also have "\<dots> = (\<forall> u \<in> nhds x. u \<inter> P \<noteq> {})"
  proof safe
    fix r assume uP: "\<forall>u\<in>nhds x. u \<inter> P \<noteq> {}" and
      rfinpref: "r \<in> finpref A x" and rP: "suff A r \<inter> P = {}"
    from rfinpref have "suff A r open" by (auto dest!: finpref_fin)
    hence "suff A r \<in> nhds x" using xpoint rfinpref
      by auto
    with uP rP show "False" by auto
  next
    fix u assume
      inter:     "\<forall>r\<in>finpref A x. suff A r \<inter> P \<noteq> {}" and
      unhd:   "u \<in> nhds x" and
      uinter: "u \<inter> P = {}"
    from unhd obtain r where
      "r \<in> finpref A x" and "suff A r \<subseteq> u"
      by (rule suff_nhd_base)
    with inter uinter show "False" by auto
  qed
  finally show ?thesis by (simp add: adhs_def)
qed

lemma (in trace_top) topology [iff]:
  "topology T"
by (simp add: T_def)

lemma (in trace_top) safety_closed_iff:
  "P \<subseteq> A\<^sup>\<infinity> \<Longrightarrow>  safety A P = (P closed)"
by (auto simp: safety_def topology.closed_adh adh_lemma ttop_carrier)

lemma (in trace_top) liveness_dense_iff:
  assumes P: "P \<subseteq> A\<^sup>\<infinity>"
  shows "liveness A P = (P dense)"
proof-
  have "liveness A P = (\<forall>r\<in>A\<^sup>\<star>. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P)"
    by (simp add: liveness_def)
  also have "\<dots> = (\<forall>x\<in>A\<^sup>\<infinity>. \<forall> r \<in> finpref A x. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P)"
      by (auto simp: finpref_def dest: finsubsetall)
  also have "\<dots> = (\<forall>x\<in>A\<^sup>\<infinity>. x adh P)" using P
    by (simp add: adh_lemma)
  also have "\<dots> = (A\<^sup>\<infinity> \<subseteq> closure P)" using P
    by (auto simp: adh_closure_iff ttop_carrier)
  also have "\<dots> = (P dense)"
    by (simp add: liveness_def is_dense_def is_densein_def ttop_carrier)
  finally show ?thesis .
qed

lemma (in trace_top) LNil_safety: "safety A {LNil}"
proof (unfold safety_def, clarify)
  fix t
  assume adh: "t \<in> A\<^sup>\<infinity>" "\<forall>r\<in>finpref A t. \<exists>s\<in>A\<^sup>\<infinity>. r @@ s \<in> {LNil}"
  thus "t = LNil" by (cases t)(auto simp: finpref_def)
qed

lemma (in trace_top) LNil_closed: "{LNil} closed"
by (auto intro: iffD1 [OF safety_closed_iff] LNil_safety)

theorem (in trace_top) alpern_schneider:
assumes Psub:     "P \<subseteq> A\<^sup>\<infinity>"
  shows "\<exists> S L. safety A S \<and> liveness A L \<and> P = S \<inter> L"
proof-
  from Psub have "P \<subseteq> carrier" by (simp add: ttop_carrier)
  then obtain L S where
    Lsub: "L \<subseteq> carrier" and
    Ssub: "S \<subseteq> carrier" and
    Sclosed: "S closed" and
    Ldense: "L dense" and
    Pinter: "P = S \<inter> L"
    by (blast elim: topology.ex_dense_closure_interE [OF topology])
  from Ssub Sclosed have "safety A S"
    by (simp add: safety_closed_iff ttop_carrier)
  moreover from Lsub Ldense have "liveness A L"
    by (simp add: liveness_dense_iff ttop_carrier)
  ultimately show ?thesis using Pinter
    by auto
qed

subsection\<open>The topology of infinite llists\<close>

definition
  itop :: "'a set \<Rightarrow> 'a llist top" where
  "itop A = topo (\<Union> s\<in>A\<^sup>\<star>. {infsuff A s})"


locale infsuffixes =
  fixes A and B
  defines [simp]: "B \<equiv> (\<Union> s\<in>A\<^sup>\<star>. {infsuff A s})"

locale itrace_top = infsuffixes + topobase


lemma (in itrace_top) open_iff [iff]:
  "m open = (m \<in> topo (\<Union> s\<in>A\<^sup>\<star>. {infsuff A s}))"
  by (simp add: T_def is_open_def)

lemma (in itrace_top) topology [iff]: "topology T"
  by (auto simp: T_def)

lemma (in itrace_top) infsuff_open [intro!]:
  "r \<in> A\<^sup>\<star> \<Longrightarrow> infsuff A r open"
  by auto

lemma (in itrace_top) itop_carrier: "carrier = A\<^sup>\<omega>"
  by (auto simp: carrier_topo infsuff_def)

lemma itop_sub_ttop_base:
  fixes A :: "'a set" 
    and B :: "'a llist set set" 
    and C :: "'a llist set set"
  defines [simp]: "B \<equiv> \<Union>s\<in>A\<^sup>\<star>. {suff A s}" and [simp]: "C \<equiv> \<Union>s\<in>A\<^sup>\<star>. {infsuff A s}"
  shows "C = (\<Union> t\<in>B. {t \<inter> \<Union>C})"
  by (auto simp: infsuff_def suff_def)

lemma itop_sub_ttop [folded ttop_def itop_def]:
  fixes A and C and S (structure)
  defines "C \<equiv> \<Union>s\<in>A\<^sup>\<star>. {infsuff A s}" and "S \<equiv> topo C"
  fixes B and T (structure)
  defines "B \<equiv> \<Union>s\<in>A\<^sup>\<star>. {suff A s}" and "T \<equiv> topo B"
  shows "subtopology S T"
proof -
  interpret itrace_top A C S by fact+
  interpret trace_top A B T by fact+
  show ?thesis
    by (auto intro: itop_sub_ttop_base [THEN subtop_lemma] simp: S_def T_def)
qed

lemma (in itrace_top) infsuff_nhd_base:
  assumes unhd: "u \<in> nhds t"
  and H: "\<And>r. \<lbrakk> r \<in> finpref A t; infsuff A r \<subseteq> u \<rbrakk> \<Longrightarrow> R"
  shows "R"
proof-
  from unhd obtain m where
    uA: "u \<subseteq> A\<^sup>\<omega>" and
    mopen: "m open" and
    tm: "t \<in> m" and
    mu: "m \<subseteq> u"
    by (auto simp: itop_carrier)
  from mopen tm have
    "\<exists>r \<in> finpref A t. infsuff A r \<subseteq> m"
  proof (induct "m")
    case (basic a)
    then obtain s where sA: "s \<in> A\<^sup>\<star>" and as: "a = infsuff A s" and ta: "t \<in> a"
      by auto
    from sA as ta have "s \<in> finpref A t" by (auto dest: infsuff_finpref)
    thus ?case using as by auto
  next case (inter a b)
    then obtain r r' where
      rt: "r \<in> finpref A t" and ra: "infsuff A r \<subseteq> a" and
      r't: "r' \<in> finpref A t" and r'b: "infsuff A r' \<subseteq> b"
      by auto
    from rt r't have "r \<le> r' \<or> r' \<le> r"
      by (auto simp: finpref_def dest: pref_locally_linear)
    thus ?case
    proof
      assume "r \<le> r'"
      hence "infsuff A r' \<subseteq> infsuff A r" by (rule infsuff_mono2)
      thus ?case using r't ra r'b by auto
    next assume "r' \<le> r"
      hence "infsuff A r \<subseteq> infsuff A r'" by (rule infsuff_mono2)
      thus ?case using rt r'b ra by auto
    qed
  next case (union M)
    then obtain v where
      "t \<in> v" and vM: "v \<in> M"
      by blast
    then obtain r where "r\<in>finpref A t" "infsuff A r \<subseteq> v" using union
      by auto
    thus ?case using vM by auto
  qed
  with mu show ?thesis by (auto intro: H)
qed

lemma (in itrace_top) hausdorff [iff]: "T2 T"
proof(rule T2I, clarify)
  fix x y assume xpoint: "x \<in> carrier"
    and ypoint: "y \<in> carrier"
    and neq: "x \<noteq> y"
  from xpoint ypoint have xA: "x \<in> A\<^sup>\<omega>" and yA: "y \<in> A\<^sup>\<omega>"
    by (auto simp: itop_carrier)
  then obtain s where
    sA: "s \<in> A\<^sup>\<star>" and sx: "s \<le> x" and sy: "\<not> s \<le> y" using neq
    by (rule inf_neqE) auto
  from neq have "y \<noteq> x" ..
  with yA xA obtain t where
    tA: "t \<in> A\<^sup>\<star>" and ty: "t \<le> y" and tx: "\<not> t \<le> x" 
    by (rule inf_neqE) auto
  let ?u = "infsuff A s" and ?v = "infsuff A t"
  have inter: "?u \<inter> ?v = {}"
  proof (rule ccontr, auto)
    fix z assume "z \<in> ?u" and "z \<in> ?v"
    hence "s \<le> z" and  "t \<le> z" by (unfold infsuff_def) auto
    hence "s \<le> t \<or> t \<le> s" by (rule pref_locally_linear)
    thus False using sx sy tx ty by (auto dest: llist_le_trans)
  qed
  moreover {
    from sA tA have "?u open" and "?v open"
      by auto
    moreover from xA yA sx ty have "x \<in> ?u" and "y \<in> ?v"
      by (auto simp: infsuff_def)
    ultimately have "infsuff A s \<in> nhds x" and
      "infsuff A t \<in> nhds y"
      by auto }
  ultimately show "\<exists> u \<in> nhds x. \<exists> v \<in> nhds y. u \<inter> v = {}"
    by auto
qed

corollary (in itrace_top) unique_convergence:
  "\<lbrakk> x \<in> carrier;
     y \<in> carrier;
     F \<in> Filters ;
     F \<longlongrightarrow> x;
     F \<longlongrightarrow> y \<rbrakk> \<Longrightarrow> x = y"
  apply (rule T2.unique_convergence)
  prefer 2
  apply (rule filter.intro)
  apply auto
  done

(*
lemma safty_closed:
  fixes   A :: "'a set"
  defines "T \<equiv> itop A"
  assumes P: "P \<subseteq> A\<^sup>\<omega>"
  and safety: "safety A P"
  shows "P iscl T"
proof-
  have istopT [iff]: "istop T" by (simp add: T_def)
  have carrT [simp]: "carr T = A\<^sup>\<omega>" by (simp add: T_def itop_carr)
  show ?thesis
  proof (rule closure_eq_closed, auto)
    fix x assume xclos: "x \<in> clos T P"
    with P have "x \<in> carr T"
      by (intro subsetD [OF closure_subset]) auto
    hence xA: "x \<in> A\<^sup>\<omega>" by simp
    moreover 
    from P xclos have adhx: "adh T P x" by (auto intro!: closure_imp_adh)
    have "\<forall> r \<in> finpref A x. \<exists> s \<in> A\<^sup>\<omega>. r @@ s \<in> P"
    proof
      fix r assume "r \<in> finpref A x"
      hence "x \<in> infsuff A r" and rA: "r \<in> A\<^sup>\<star>" using xA
        by (auto simp: finpref_def infsuff_def)
      hence "infsuff A r \<in> nhds T x" by (auto simp: T_def)
      with adhx have  "infsuff A r \<inter> P \<noteq> {}" by (elim adhCE) auto
      then obtain t where "t \<in> infsuff A r" and tP: "t \<in> P" by auto
      then obtain s where "s \<in> A\<^sup>\<omega>" and "t = r @@ s" using rA
        by (auto elim!: infsuff_appE)
      thus "\<exists> s \<in> A\<^sup>\<omega>. r @@ s \<in> P" using tP by auto
    qed
    ultimately show "x \<in> P" using safety
      by (auto elim: safetyE)
  qed
qed
*)
lemma (in itrace_top) adh_lemma:
assumes xpoint: "x \<in> A\<^sup>\<omega>"
  and  PA: "P \<subseteq> A\<^sup>\<omega>"
shows "x adh P = (\<forall> r \<in> finpref A x. \<exists> s \<in> A\<^sup>\<omega>. r @@ s \<in> P)"
proof-
  from PA have "\<And>r. r \<in> A\<^sup>\<star> \<Longrightarrow> (\<exists> s \<in> A\<^sup>\<omega>. r @@ s \<in> P) =
        (\<exists> s \<in> P. r \<le> s)"
    by (auto simp: llist_le_def iff: lapp_infT)
  hence  "(\<forall> r \<in> finpref A x. \<exists> s \<in> A\<^sup>\<omega>. r @@ s \<in> P) =
        (\<forall> r \<in> finpref A x. \<exists> s \<in> P. r \<le> s)"
    by (auto simp: finpref_def)
  also have "\<dots> = (\<forall> r \<in> finpref A x. infsuff A r \<inter> P \<noteq> {})"
  proof-
    have "\<And>r. (\<exists>s\<in>P. r \<le> s) = ({ra. ra \<in> A\<^sup>\<omega> \<and> r \<le> ra} \<inter> P \<noteq> {})" using PA
      by blast
    thus ?thesis by (simp add: infsuff_def)
  qed
  also have "\<dots> = (\<forall> u \<in> nhds x. u \<inter> P \<noteq> {})"
  proof safe
    fix r assume uP: "\<forall> u \<in> nhds x. u \<inter> P \<noteq> {}" and
      rfinpref: "r \<in> finpref A x" and rP: "infsuff A r \<inter> P = {}"
    from rfinpref have "infsuff A r open" by (auto dest!: finpref_fin)
    hence "infsuff A r \<in> nhds x" using xpoint rfinpref
      by auto
    with uP rP show "False" by auto
  next
    fix u assume
      inter:     "\<forall>r\<in>finpref A x. infsuff A r \<inter> P \<noteq> {}" and
      unhd:   "u \<in> nhds x" and
      uinter: "u \<inter> P = {}"
    from unhd obtain r where
      "r \<in> finpref A x" and "infsuff A r \<subseteq> u"
      by (rule infsuff_nhd_base)
    with inter uinter show "False" by auto
  qed
  finally show ?thesis by (simp add: adhs_def)
qed

lemma (in itrace_top) infsafety_closed_iff:
  "P \<subseteq> A\<^sup>\<omega> \<Longrightarrow>  infsafety A P = (P closed)"
  by (auto simp: infsafety_def topology.closed_adh adh_lemma itop_carrier)

lemma (in itrace_top) empty:
  "A = {} \<Longrightarrow> T = {{}}"
proof (auto simp: T_def)
  fix m x assume "m \<in> topo {{}}" and  xm: "x \<in> m"
  thus False
    by (induct m) auto
qed

lemma itop_empty: "itop {} = {{}}"
proof (auto simp: itop_def)
  fix m x assume "m \<in> topo {{}}" and  xm: "x \<in> m"
  thus False
    by (induct m) auto
qed

lemma infliveness_empty:
  "infliveness {} P \<Longrightarrow> False"
  by (auto simp: infliveness_def)

lemma (in trivial) dense:
  "P dense"
  by auto

lemma (in itrace_top) infliveness_dense_iff:
  assumes notempty: "A \<noteq> {}"
  and P: "P \<subseteq> A\<^sup>\<omega>"
  shows "infliveness A P = (P dense)"
proof-
  have "infliveness A P = (\<forall>r\<in>A\<^sup>\<star>. \<exists> s \<in> A\<^sup>\<omega>. r @@ s \<in> P)"
    by (simp add: infliveness_def)
  also have "\<dots> = (\<forall>x\<in>A\<^sup>\<omega>. \<forall> r \<in> finpref A x. \<exists> s \<in> A\<^sup>\<omega>. r @@ s \<in> P)"
  proof-
    from notempty obtain a where "a \<in> A"
      by auto
    hence lc: "lconst a \<in> A\<^sup>\<omega>"
      by (rule lconstT)
    hence "\<And>P. (\<forall>x\<in>A\<^sup>\<omega>. \<forall>r\<in>finpref A x. P r) = (\<forall> r\<in>A\<^sup>\<star>. P r)"
    proof (auto dest: finpref_fin)
      fix P r  assume lc: "lconst a \<in> A\<^sup>\<omega>"
        and Pr: "\<forall>x\<in>A\<^sup>\<omega>. \<forall>r\<in>finpref A x. P r"
        and rA: "r \<in> A\<^sup>\<star>"
      from rA lc have rlc: "r @@ lconst a \<in> A\<^sup>\<omega>" by (rule lapp_fin_infT)
      moreover from rA rlc have "r \<in> finpref A (r @@ lconst a)" 
        by (auto simp: finpref_def llist_le_def)
      ultimately show "P r" using Pr by auto
    qed
    thus ?thesis by simp
  qed
  also have "\<dots> = (\<forall>x\<in>A\<^sup>\<omega>. x adh P)" using P
    by (simp add: adh_lemma)
  also have "\<dots> = (A\<^sup>\<omega> \<subseteq> closure P)" using P
    by (auto simp: adh_closure_iff itop_carrier)
  also have "\<dots> = (P dense)"
    by (simp add: infliveness_def is_dense_def is_densein_def itop_carrier)
  finally show ?thesis .
qed

theorem (in itrace_top) alpern_schneider:
assumes notempty: "A \<noteq> {}"
  and   Psub:     "P \<subseteq> A\<^sup>\<omega>"
  shows "\<exists> S L. infsafety A S \<and> infliveness A L \<and> P = S \<inter> L"
proof-
  from Psub have "P \<subseteq> carrier"
    by (simp add: itop_carrier [THEN sym])
  then obtain L S where
    Lsub: "L \<subseteq> carrier" and
    Ssub: "S \<subseteq> carrier" and
    Sclosed: "S closed" and
    Ldense: "L dense" and
    Pinter: "P = S \<inter> L"
    by (rule topology.ex_dense_closure_interE [OF topology]) auto
  from Ssub Sclosed have "infsafety A S"
    by (simp add: infsafety_closed_iff itop_carrier)
  moreover from notempty Lsub Ldense have "infliveness A L"
    by (simp add: infliveness_dense_iff itop_carrier)
  ultimately show ?thesis using Pinter
    by auto
qed

subsection\<open>The topology of non-empty llists\<close>

definition
  ptop :: "'a set \<Rightarrow> 'a llist top" where
  "ptop A \<equiv> topo (\<Union> s\<in>A\<^sup>\<clubsuit>. {suff A s})"


locale possuffixes =
  fixes A and B
  defines [simp]: "B \<equiv> (\<Union> s\<in>A\<^sup>\<clubsuit>. {suff A s})"

locale ptrace_top = possuffixes + topobase


lemma (in ptrace_top) open_iff [iff]:
  "m open = (m \<in> topo (\<Union> s\<in>A\<^sup>\<clubsuit>. {suff A s}))"
  by (simp add: T_def is_open_def)

lemma (in ptrace_top) topology [iff]: "topology T"
  by (simp add: T_def)

lemma (in ptrace_top) ptop_carrier: "carrier = A\<^sup>\<spadesuit>"
by (auto simp add: carrier_topo suff_def)
   (auto elim: alllsts.cases)

lemma pptop_subtop_ttop:
  fixes S (structure)
  fixes A and B and T (structure)
  defines "B \<equiv> \<Union>s\<in>A\<^sup>\<star>. {suff A s}" and "T \<equiv> topo B"
  defines "S \<equiv> \<Union> t \<in> T. {t - {LNil}}"
  shows "subtopology S T"
by (rule subtopology.intro, auto simp add: is_open_def S_def carr_def)
  
lemma pptop_top:
  fixes S (structure)
  fixes A and B and T (structure)
  defines "B \<equiv> \<Union>s\<in>A\<^sup>\<star>. {suff A s}" and "T \<equiv> topo B"
  defines "S \<equiv> \<Union> t \<in> T. {t - {LNil}}"
  shows  "topology (\<Union> t \<in> T. {t - {LNil}})"
proof -
  interpret trace_top A B T by fact+
  show ?thesis
    by (auto intro!: subtopology.subtop_topology [OF pptop_subtop_ttop]
      trace_top.topology simp: T_def)
qed

(*
lemma
  includes ptrace_top A B S
  includes trace_top  A C T
  fixes S' (structure)
  defines  "S' \<equiv> (\<Union> t \<in> T. {t - {LNil}})" 
  shows "S = S'"
proof-
  have [iff]: "\<And> m. m open\<^sub>3 = (\<exists>t. t open\<^sub>2 \<and> m = t - {LNil})"
    by (auto simp add: S'_def is_open_def)
  show ?thesis
  proof
    fix m assume "m open"
    thus "m open\<^sub>3"
    proof (induct m)
      case (basic m) thus ?case by auto
    next case (inter u v) thus ?case
        by (blast intro: topology.Int_open [OF pptop_top])
    next case (union M) thus ?case
        by (auto intro!: topology.union_open [OF pptop_top] simp: S'_def T_def)
    qed
  next
    fix m assume "m open\<^sub>3"
    then obtain t where "t open\<^sub>2" and mt: "m = t - {LNil}" by auto
    hence "t - {LNil} open\<^sub>1"
    proof (induct t)
      case (basic x)
      then obtain s where sfin: "s \<in> A\<^sup>\<star>" and
        ms: "x = suff A s"
        by auto
      thus ?case
      proof (cases s)
        case LNil_fin with ms
        have "x - {LNil} = carrier" by (auto simp: ptop_carrier)
        thus ?thesis by (auto intro!: topology.carrier_open [OF pptop_top])
      next
        case (LCons_fin a l) with ms show ?thesis
          by (auto simp: ptop_def)
      qed
    next case (inter u v)
      hence "(u - {LNil}) \<inter> (v - {LNil}) \<in> ptop A" by auto
      moreover have "(u - {LNil}) \<inter> (v - {LNil}) = (u \<inter> v) - {LNil}"
        by auto
      ultimately show ?case by auto
    next case (union M)
      hence "\<Union>{u. \<exists>x\<in>M. u = x - {LNil}} \<in> ptop A" by auto
      moreover have "\<Union>{u. \<exists>x\<in>M. u = x - {LNil}} = \<Union>M - {LNil}" by auto
      ultimately show ?case by auto
    qed
    thus "x \<in> ptop A" using xt by auto
  qed
qed
*)
lemma (in ptrace_top) suff_open [intro!]:
  "r \<in> A\<^sup>\<clubsuit> \<Longrightarrow> suff A r open"
  by auto

lemma (in ptrace_top) suff_ptop_nhd_base:
  assumes unhd: "u \<in> nhds t"
  and H: "\<And>r. \<lbrakk> r \<in> pfinpref A t; suff A r \<subseteq> u \<rbrakk> \<Longrightarrow> R"
  shows "R"
proof-
  from unhd obtain m where
    uA: "u \<subseteq> A\<^sup>\<spadesuit>" and
    mopen: "m open" and
    tm: "t \<in> m" and
    mu: "m \<subseteq> u"
    by (auto simp: ptop_carrier)
  from mopen tm have
    "\<exists>r \<in> pfinpref A t. suff A r \<subseteq> m"
  proof (induct "m")
    case (basic a)
    then obtain s where sA: "s \<in> A\<^sup>\<clubsuit>" and as: "a = suff A s" and ta: "t \<in> a"
      by auto
    from sA as ta have "s \<in> pfinpref A t"
      by (auto simp: pfinpref_def dest: suff_finpref)
    thus ?case using as by auto
  next case (inter a b)
    then obtain r r' where
      rt: "r \<in> pfinpref A t" and ra: "suff A r \<subseteq> a" and
      r't: "r' \<in> pfinpref A t" and r'b: "suff A r' \<subseteq> b"
      by auto
    from rt r't have "r \<le> r' \<or> r' \<le> r"
      by (auto simp: pfinpref_def finpref_def dest: pref_locally_linear)
    thus ?case
    proof
      assume "r \<le> r'"
      hence "suff A r' \<subseteq> suff A r" by (rule suff_mono2)
      thus ?case using r't ra r'b by auto
    next assume "r' \<le> r"
      hence "suff A r \<subseteq> suff A r'" by (rule suff_mono2)
      thus ?case using rt r'b ra by auto
    qed
  next case (union M)
    then obtain v where
      "t \<in> v" and vM: "v \<in> M"
      by blast
    then obtain r where "r\<in>pfinpref A t" "suff A r \<subseteq> v" using union
      by auto
    thus ?case using vM by auto
  qed
  with mu show ?thesis by (auto intro: H)
qed

lemma pfinpref_LNil [simp]: "pfinpref A LNil = {}"
  by (auto simp: pfinpref_def)

lemma (in ptrace_top) adh_lemma:
  assumes xpoint: "x \<in> A\<^sup>\<spadesuit>"
  and  P_subset_A: "P \<subseteq> A\<^sup>\<spadesuit>"
  shows "x adh P = (\<forall> r \<in> pfinpref A x. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P)"
proof
  assume adh_x: "x adh P"
  show "\<forall>r\<in>pfinpref A x. \<exists>s\<in>A\<^sup>\<infinity>. r @@ s \<in> P"
  proof
    fix r let ?u = "suff A r"
    assume r_pfinpref_x: "r \<in> pfinpref A x"
    hence r_pos: "r \<in> A\<^sup>\<clubsuit>" by (auto dest: finpref_fin)
    hence "?u open" by auto
    hence "?u \<in> nhds x" using xpoint r_pfinpref_x
      by auto
    with adh_x have  "?u \<inter> P \<noteq> {}" by (auto elim!:adhCE)
    then obtain t where tu: "t \<in> ?u" and tP: "t \<in> P"
      by auto
    from tu obtain s where "t = r @@ s" using r_pos
      by (auto elim!: suff_appE)
    with tP show "\<exists>s\<in>A\<^sup>\<infinity>. r @@ s \<in> P" using P_subset_A r_pos
      by (auto iff: lapp_allT_iff)
  qed
next
  assume H: "\<forall>r\<in>pfinpref A x. \<exists>s\<in>A\<^sup>\<infinity>. r @@ s \<in> P"
  show "x adh P"
  proof
    fix U assume unhd: "U \<in> nhds x"
    then obtain r where r_pfinpref_x: "r \<in> pfinpref A x" and
      suff_subset_U: "suff A r \<subseteq> U" by (elim suff_ptop_nhd_base)
    from r_pfinpref_x have rpos: "r \<in> A\<^sup>\<clubsuit>" by (auto intro: finpref_fin)
    show "U \<inter> P \<noteq> {}" using rpos
    proof (cases r)
      case (LCons a l)
      hence r_pfinpref_x: "r \<in> pfinpref A x" using r_pfinpref_x
        by auto
      with H obtain s where sA: "s \<in> A\<^sup>\<infinity>" and asP: "r@@s \<in> P"
        by  auto
      moreover have "r @@ s \<in> suff A r" using sA rpos
        by (auto simp: suff_def iff: lapp_allT_iff)
      ultimately show ?thesis using suff_subset_U by auto
    qed
  qed
qed

lemma (in ptrace_top) possafety_closed_iff:
  "P \<subseteq> A\<^sup>\<spadesuit> \<Longrightarrow>  possafety A P = (P closed)"
  by (auto simp: possafety_def topology.closed_adh ptop_carrier adh_lemma)
(*
lemma ptop_empty: "ptop {} = {{}}"
proof (auto simp: ptop_def intro!: topobase.basic)
  fix m x assume "m \<in> topo {}" and  xm: "x \<in> m"
  thus False
    by (induct m) auto
qed

lemma posliveness_empty:
  "posliveness {} P"
  by (auto simp: posliveness_def)
*)

lemma (in ptrace_top) posliveness_dense_iff:
  assumes P: "P \<subseteq> A\<^sup>\<spadesuit>"
  shows "posliveness A P = (P dense)"
proof-
  have "posliveness A P = (\<forall>r\<in>A\<^sup>\<clubsuit>. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P)"
    by (simp add: posliveness_def)
  also have "\<dots> = (\<forall>x\<in>A\<^sup>\<spadesuit>. \<forall> r \<in> pfinpref A x. \<exists> s \<in> A\<^sup>\<infinity>. r @@ s \<in> P)"
      by (auto simp: pfinpref_def finpref_def dest: finsubsetall)
  also have "\<dots> = (\<forall>x\<in>A\<^sup>\<spadesuit>. x adh P)" using P
    by (auto simp: adh_lemma simp del: poslsts_iff)
  also have "\<dots> = (A\<^sup>\<spadesuit> \<subseteq> closure P)" using P
    by (auto simp: adh_closure_iff ptop_carrier simp del: poslsts_iff)
  also have "\<dots> = (P dense)"
    by (simp add: posliveness_def is_dense_def is_densein_def ptop_carrier)
  finally show ?thesis .
qed

theorem (in ptrace_top) alpern_schneider:
assumes Psub: "P \<subseteq> A\<^sup>\<spadesuit>"
  shows "\<exists> S L. possafety A S \<and> posliveness A L \<and> P = S \<inter> L"
proof-
  from Psub have "P \<subseteq> carrier" by (simp add: ptop_carrier)
  then obtain L S where
    Lsub: "L \<subseteq> carrier" and
    Ssub: "S \<subseteq> carrier" and
    Sclosed: "S closed" and
    Ldense: "L dense" and
    Pinter: "P = S \<inter> L"
    by (blast elim: topology.ex_dense_closure_interE [OF topology])
  from Ssub Sclosed have "possafety A S"
    by (simp add: possafety_closed_iff ptop_carrier)
  moreover from Lsub Ldense have "posliveness A L"
    by (simp add: posliveness_dense_iff ptop_carrier)
  ultimately show ?thesis using Pinter
    by auto
qed

end
