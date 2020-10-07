section \<open> Simple UTP real-time theory \<close>

theory utp_simple_time imports "../utp" begin

text \<open> In this section we give a small example UTP theory, and show how Isabelle/UTP can be
  used to automate production of programming laws. \<close>

subsection \<open> Observation Space and Signature \<close>

text \<open> We first declare the observation space for our theory of timed relations. It consists
  of two variables, to denote time and the program state, respectively. \<close>

alphabet 's st_time = 
  clock :: nat  st :: 's

text \<open> A timed relation is a homogeneous relation over the declared observation space. \<close>

type_synonym 's time_rel = "'s st_time hrel"

text \<open> We introduce the following operator for adding an $n$-unit delay to a timed relation. \<close>

definition Wait :: "nat \<Rightarrow> 's time_rel" where
[upred_defs]: "Wait(n) = ($clock\<acute> =\<^sub>u $clock + \<guillemotleft>n\<guillemotright> \<and> $st\<acute> =\<^sub>u $st)"

subsection \<open> UTP Theory \<close>

text \<open> We define a single healthiness condition which ensures that the clock monotonically
  advances, and so forbids reverse time travel. \<close>

definition HT :: "'s time_rel \<Rightarrow> 's time_rel" where
[upred_defs]: "HT(P) = (P \<and> $clock \<le>\<^sub>u $clock\<acute>)"

text \<open> This healthiness condition is idempotent, monotonic, and also continuous, meaning it
  distributes through arbitary non-empty infima. \<close>

theorem HT_idem: "HT(HT(P)) = HT(P)" by rel_auto

theorem HT_mono: "P \<sqsubseteq> Q \<Longrightarrow> HT(P) \<sqsubseteq> HT(Q)" by rel_auto

theorem HT_continuous: "Continuous HT" by rel_auto

text \<open> We now create the UTP theory object for timed relations. This is done using a local 
  interpretation @{term "utp_theory_continuous HT"}. This raises the proof obligations
  that @{term HT} is both idempotent and continuous, which we have proved already. 
  The result of this command is a collection of theorems that can be derived from these 
  facts. Notably, we obtain a complete lattice of timed relations via the Knaster-Tarski theorem. 
  We also apply some locale rewrites so that the theorems that are exports have a more intuitive 
  form. \<close>

interpretation time_theory: utp_theory_continuous HT
  rewrites "P \<in> carrier time_theory.thy_order \<longleftrightarrow> P is HT"
  and "carrier time_theory.thy_order \<rightarrow> carrier time_theory.thy_order \<equiv> \<lbrakk>HT\<rbrakk>\<^sub>H \<rightarrow> \<lbrakk>HT\<rbrakk>\<^sub>H"
  and "le time_theory.thy_order = (\<sqsubseteq>)"
  and "eq time_theory.thy_order = (=)"  
proof -
  show "utp_theory_continuous HT"
  proof
    show "\<And>P. HT (HT P) = HT P"
      by (simp add: HT_idem)
    show "Continuous HT"
      by (simp add: HT_continuous)
  qed
qed (simp_all)

text \<open> The object \textit{time-theory} is a new namespace that contains both definitions and theorems.
  Since the theory forms a complete lattice, we obtain a top element, bottom element, and a
  least fixed-point constructor. We give all of these some intuitive syntax. \<close>

notation time_theory.utp_top ("\<top>\<^sub>t")
notation time_theory.utp_bottom ("\<bottom>\<^sub>t")
notation time_theory.utp_lfp ("\<mu>\<^sub>t")

text \<open> Below is a selection of theorems that have been exported by the locale interpretation. \<close>

thm time_theory.bottom_healthy
thm time_theory.top_higher
thm time_theory.meet_bottom
thm time_theory.LFP_unfold

subsection \<open> Closure Laws \<close>

text \<open> @{term HT} applied to @{term Wait} has no affect, since the latter always advances time. \<close>

lemma HT_Wait: "HT(Wait(n)) = Wait(n)" by (rel_auto)

lemma HT_Wait_closed [closure]: "Wait(n) is HT"
  by (simp add: HT_Wait Healthy_def)

text \<open> Relational identity, @{term II}, is likewise @{term HT}-healthy. \<close>

lemma HT_skip_closed [closure]: "II is HT"
  by (rel_auto)

text \<open> @{term HT} is closed under sequential composition, which can be shown 
  by transitivity of @{term "(\<le>)"}. \<close>

lemma HT_seqr_closed [closure]:
  "\<lbrakk> P is HT; Q is HT \<rbrakk> \<Longrightarrow> P ;; Q is HT"
  by (rel_auto, meson dual_order.trans) \<comment> \<open> Sledgehammer required \<close>

text \<open> Assignment is also healthy, provided that the clock variable is not assigned. \<close>

lemma HT_assign_closed [closure]: "\<lbrakk> vwb_lens x; clock \<bowtie> x \<rbrakk> \<Longrightarrow> x := v is HT"
  by (rel_auto, metis (mono_tags, lifting) eq_iff lens.select_convs(1) lens_indep_get st_time.select_convs(1))

text \<open> An alternative characterisation of the above is that @{term x} is within the state space lens. \<close>

lemma HT_assign_closed' [closure]: "\<lbrakk> vwb_lens x; x \<subseteq>\<^sub>L st \<rbrakk> \<Longrightarrow> x := v is HT"
  by (rel_auto)

subsection \<open> Algebraic Laws \<close>

text \<open> Finally, we prove some useful algebraic laws. \<close>

theorem Wait_skip: "Wait(0) = II" by (rel_auto)
    
theorem Wait_Wait: "Wait(m) ;; Wait(n) = Wait (m + n)" by (rel_auto)

theorem Wait_cond: "Wait(m) ;; (P \<triangleleft> b \<triangleright>\<^sub>r Q) = (Wait m ;; P) \<triangleleft> b\<lbrakk>&clock+\<guillemotleft>m\<guillemotright>/&clock\<rbrakk> \<triangleright>\<^sub>r (Wait m ;; Q)"
  by (rel_auto)

end