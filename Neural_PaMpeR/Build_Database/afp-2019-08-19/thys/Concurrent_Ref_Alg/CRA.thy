section \<open>Concurrent Refinement Algebra \label{S:CRA}\<close>

text \<open>
  This theory brings together the three main operators:
  sequential composition,
  parallel composition and
  conjunction,
  as well as the iteration operators. 
\<close>

theory CRA
imports 
  Sequential
  Conjunction
  Parallel
begin

text \<open>
  Locale sequential-parallel brings together the sequential and parallel
  operators and relates their identities.
\<close>
locale sequential_parallel = seq_distrib + par_distrib +
  assumes nil_par_nil: "nil \<parallel> nil \<sqsubseteq> nil" 
  and skip_nil: "skip \<sqsubseteq> nil"           (* 41 *)
  and skip_skip: "skip \<sqsubseteq> skip;skip"    (* 40 *)
begin

lemma nil_absorb: "nil \<parallel> nil = nil" using nil_par_nil skip_nil par_skip
by (metis inf.absorb_iff2 inf.orderE inf_par_distrib2)

lemma skip_absorb [simp]: "skip;skip = skip"
by (metis antisym seq_mono_right seq_nil_right skip_skip skip_nil)

end

text \<open>
  Locale conjunction-parallel brings together the weak conjunction and
  parallel operators and relates their identities.
  It also introduces the interchange axiom for conjunction and parallel.
\<close>

locale conjunction_parallel = conj_distrib + par_distrib + 
  assumes chaos_par_top: "\<top> \<sqsubseteq> chaos \<parallel> \<top>"
  assumes chaos_par_chaos: "chaos \<sqsubseteq> chaos \<parallel> chaos"     (* 47 *)
  assumes parallel_interchange: "(c\<^sub>0 \<parallel> c\<^sub>1) \<iinter> (d\<^sub>0 \<parallel> d\<^sub>1) \<sqsubseteq> (c\<^sub>0 \<iinter> d\<^sub>0) \<parallel> (c\<^sub>1 \<iinter> d\<^sub>1)" (* 50 *)
begin

lemma chaos_skip: "chaos \<sqsubseteq> skip"  (* 46 *)
proof -
  have "chaos = (chaos \<parallel> skip) \<iinter> (skip \<parallel> chaos)" by simp
  then have "\<dots> \<sqsubseteq> (chaos \<iinter> skip) \<parallel> (skip \<iinter> chaos)" using parallel_interchange by blast 
  thus ?thesis by auto
qed

lemma chaos_par_chaos_eq: "chaos = chaos \<parallel> chaos"
  by (metis antisym chaos_par_chaos chaos_skip order_refl par_mono par_skip)

lemma nonabort_par_top: "chaos \<sqsubseteq> c \<Longrightarrow> c \<parallel> \<top> = \<top>"
  by (metis chaos_par_top par_mono top.extremum_uniqueI)

lemma skip_conj_top: "skip \<iinter> \<top> = \<top>"
by (simp add: chaos_skip conjoin_top)

lemma conj_distrib2: "c \<sqsubseteq> c \<parallel> c \<Longrightarrow> c \<iinter> (d\<^sub>0 \<parallel> d\<^sub>1) \<sqsubseteq> (c \<iinter> d\<^sub>0) \<parallel> (c \<iinter> d\<^sub>1)"
proof -
  assume "c \<sqsubseteq> c \<parallel> c"
  then have "c \<iinter> (d\<^sub>0 \<parallel> d\<^sub>1) \<sqsubseteq> (c \<parallel> c) \<iinter> (d\<^sub>0 \<parallel> d\<^sub>1)" by (metis conj_mono order.refl) 
  thus ?thesis by (metis parallel_interchange refine_trans) 
qed

end

text \<open>
  Locale conjunction-sequential brings together the weak conjunction and
  sequential operators.
  It also introduces the interchange axiom for conjunction and sequential.
\<close>

locale conjunction_sequential = conj_distrib + seq_distrib + (* iteration + *)
  assumes chaos_seq_chaos: "chaos \<sqsubseteq> chaos;chaos"
  assumes sequential_interchange: "(c\<^sub>0;c\<^sub>1) \<iinter> (d\<^sub>0;d\<^sub>1) \<sqsubseteq> (c\<^sub>0 \<iinter> d\<^sub>0);(c\<^sub>1 \<iinter> d\<^sub>1)"  (* 51 *)
begin

lemma chaos_nil: "chaos \<sqsubseteq> nil"
  by (metis conj_chaos local.conj_commute seq_nil_left seq_nil_right
       sequential_interchange)

lemma chaos_seq_absorb: "chaos = chaos;chaos" 
proof (rule antisym)
  show "chaos \<sqsubseteq> chaos;chaos" by (simp add: chaos_seq_chaos) 
next
  show "chaos;chaos \<sqsubseteq> chaos" using chaos_nil
    using seq_mono_left seq_nil_left by fastforce 
qed
  
lemma seq_bot_conj: "c;\<bottom> \<iinter> d \<sqsubseteq> (c \<iinter> d);\<bottom>"
   by (metis (no_types) conj_bot_left seq_nil_right sequential_interchange) 

lemma conj_seq_bot_right [simp]: "c;\<bottom> \<iinter> c =  c;\<bottom>"
proof (rule antisym)
  show lr: "c;\<bottom> \<iinter> c \<sqsubseteq>  c;\<bottom>" by (metis seq_bot_conj conj_idem) 
next
  show rl: "c;\<bottom> \<sqsubseteq> c;\<bottom> \<iinter> c" 
    by (metis conj_idem conj_mono_right seq_bot_right)
qed

lemma conj_distrib3: "c \<sqsubseteq> c;c \<Longrightarrow> c \<iinter> (d\<^sub>0 ; d\<^sub>1) \<sqsubseteq> (c \<iinter> d\<^sub>0);(c \<iinter> d\<^sub>1)"
proof -
  assume "c \<sqsubseteq> c;c"
  then have "c \<iinter> (d\<^sub>0;d\<^sub>1) \<sqsubseteq> (c;c) \<iinter> (d\<^sub>0;d\<^sub>1)" by (metis conj_mono order.refl) 
  thus ?thesis by (metis sequential_interchange refine_trans) 
qed

(*
lemma iter_conj_distrib:
  assumes nil: "c \<sqsubseteq> nil"
    and repeat: "c \<sqsubseteq> c ; c"
  shows "c \<iinter> d\<^sup>\<omega> \<sqsubseteq> (c \<iinter> d)\<^sup>\<omega>"
proof (unfold iter_def)
  def F \<equiv> "(\<lambda> x. c \<iinter> x)"
  def G \<equiv> "(\<lambda> x. nil \<sqinter> d;x)"
  def H \<equiv> "(\<lambda> x. nil \<sqinter> ((c \<iinter> d);x))"

  have FG: "F \<circ> G = (\<lambda> x. c \<iinter> (nil \<sqinter> d;x))"  by (metis comp_def F_def G_def) 
  have HF: "H \<circ> F = (\<lambda> x. (nil \<sqinter> (c \<iinter> d);(c \<iinter> x)))" by (metis comp_def H_def F_def) 

  have "F (lfp G) \<sqsubseteq> lfp H"
  proof (rule fusion_lfp_leq)
    show "mono H" by (simp add: H_def iter_step_mono)
  next
    show "dist_over_sup F" by (simp add: F_def conj_Sup_distrib)
  next
    fix x
    have "c \<iinter> (nil \<sqinter> d;x) = (c \<iinter> nil) \<sqinter> (c \<iinter> d;x)" by (metis inf_conj_distrib conj_commute)
    also have "... \<sqsubseteq> nil \<sqinter> (c \<iinter> d;x)" by (metis conjunction_sup inf_mono_left le_iff_sup nil)
    also have "... \<sqsubseteq> nil \<sqinter> (c;c \<iinter> d;x)" by (metis inf_conj_distrib inf.absorb_iff2 inf_mono_right repeat)
    also have "... \<sqsubseteq> nil \<sqinter> (c \<iinter> d);(c \<iinter> x)" by (meson inf_mono_right sequential_interchange)
    finally show "(F \<circ> G) x \<sqsubseteq> (H \<circ> F) x" by (simp add: FG HF)
  qed

  then show "c \<iinter> lfp(\<lambda>x. nil \<sqinter> d ; x) \<sqsubseteq> lfp (\<lambda>x. nil \<sqinter> (c \<iinter> d) ; x)" using F_def G_def H_def by simp
qed

lemma iter_conj_distrib1: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<sqsubseteq> (c\<^sup>\<omega> \<iinter> d)\<^sup>\<omega>"
  by (simp add: iter0 iter_conj_distrib)

lemma iter_conj_distrib2: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<sqsubseteq> (c \<iinter> d)\<^sup>\<omega>"
proof -
  have a: "c\<^sup>\<omega> \<sqsubseteq> c" by (metis iter1)
  have b: "c\<^sup>\<omega> \<iinter> d\<^sup>\<omega> \<sqsubseteq> (c\<^sup>\<omega> \<iinter> d)\<^sup>\<omega>" by (metis iter_conj_distrib1)
  have "c\<^sup>\<omega> \<iinter> d \<sqsubseteq> c \<iinter> d" by (metis a conj_mono order.refl) 
  thus ?thesis using a b by (metis refine_trans iter_mono) 
qed
*)

end

text \<open>
  Locale cra brings together sequential, parallel and weak conjunction.
\<close>

locale cra = sequential_parallel + conjunction_parallel + conjunction_sequential

end
