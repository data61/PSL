(*  Title:       Formalization of Schneider's generalized clock synchronization protocol.
    Author:      Alwen Tiu, LORIA, June 11, 2005
    Maintainer:  Alwen Tiu <Alwen.Tiu at loria.fr>
*)

theory GenClock imports Complex_Main begin

subsection\<open>Types and constants definitions\<close>

text\<open>Process is represented by natural numbers. The type 'event' corresponds
to synchronization rounds.\<close>

type_synonym process = nat
type_synonym event = nat      (* synchronization rounds *)
type_synonym time = real
type_synonym Clocktime = real

axiomatization
  \<delta> :: real and
  \<mu> :: real and
  \<rho> :: real and
  rmin :: real and
  rmax :: real and
  \<beta> :: real and
  \<Lambda> :: real and
  (* Number of processes *)
  np :: process and
  maxfaults :: process and
  (* Physical clocks *)
  PC :: "[process, time] \<Rightarrow> Clocktime" and
  (* Virtual / Logical clocks *)
  VC :: "[process, time] \<Rightarrow> Clocktime" and
  (* Starting (real) time of synchronization rounds *)
  te :: "[process, event] \<Rightarrow> time" and
  (* Clock readings at each round *)
  \<theta> :: "[process, event] \<Rightarrow> (process \<Rightarrow> Clocktime)" and
  (* Logical clock in-effect at a time interval *)
  IC :: "[process, event, time] \<Rightarrow> Clocktime" and
  (* Correct clocks *)
  correct :: "[process, time] \<Rightarrow> bool" and
  (* The averaging function to calculate clock adjustment *)
  cfn :: "[process, (process \<Rightarrow> Clocktime)] \<Rightarrow> Clocktime" and

  \<pi> :: "[Clocktime, Clocktime] \<Rightarrow> Clocktime" and

  \<alpha> :: "Clocktime \<Rightarrow> Clocktime"

definition
  count :: "[process \<Rightarrow> bool, process] \<Rightarrow> nat" where
  "count f n = card {p. p < n \<and> f p}"

definition
  (* Adjustment to a clock *)
  Adj :: "[process, event] \<Rightarrow> Clocktime" where
  "Adj = (\<lambda> p i. if 0 < i then cfn p (\<theta> p i) - PC p (te p i)
                 else 0)" 

definition
  (* Auxilary predicates used in the definition of precision enhancement *)
  okRead1 :: "[process \<Rightarrow> Clocktime, Clocktime, process \<Rightarrow> bool] \<Rightarrow> bool" where
  "okRead1 f x ppred \<longleftrightarrow> (\<forall> l m. ppred l \<and> ppred m \<longrightarrow> \<bar>f l - f m\<bar> \<le> x)"

definition
  okRead2 :: "[process \<Rightarrow> Clocktime, process \<Rightarrow> Clocktime, Clocktime, 
               process \<Rightarrow> bool] \<Rightarrow> bool" where
  "okRead2 f g x ppred \<longleftrightarrow> (\<forall> p. ppred p \<longrightarrow> \<bar>f p - g p\<bar> \<le> x)"

definition
  rho_bound1 :: "[[process, time] \<Rightarrow> Clocktime] \<Rightarrow> bool" where
  "rho_bound1 C \<longleftrightarrow> (\<forall> p s t. correct p t \<and> s \<le> t \<longrightarrow> C p t - C p s \<le> (t - s)*(1 + \<rho>))"
definition
  rho_bound2 :: "[[process, time] \<Rightarrow> Clocktime] \<Rightarrow> bool" where
  "rho_bound2 C \<longleftrightarrow> (\<forall> p s t. correct p t \<and> s \<le> t \<longrightarrow> (t - s)*(1 - \<rho>) \<le> C p t - C p s)"

subsection\<open>Clock conditions\<close>

text\<open>Some general assumptions\<close>
axiomatization where
  constants_ax: "0 < \<beta> \<and> 0 < \<mu> \<and> 0 < rmin 
  \<and> rmin \<le> rmax \<and> 0 < \<rho> \<and> 0 < np \<and> maxfaults \<le> np"

axiomatization where
  PC_monotone: "\<forall> p s t. correct p t \<and> s \<le> t \<longrightarrow> PC p s \<le> PC p t"

axiomatization where
  VClock: "\<forall> p t i. correct p t \<and> te p i \<le> t \<and> t < te p (i + 1) \<longrightarrow> VC p t = IC p i t"

axiomatization where
  IClock: "\<forall> p t i. correct p t \<longrightarrow> IC p i t = PC p t + Adj p i"

text\<open>Condition 1: initial skew\<close>
axiomatization where
  init: "\<forall> p. correct p 0 \<longrightarrow> 0 \<le> PC p 0 \<and> PC p 0 \<le> \<mu>"

text\<open>Condition 2: bounded drift\<close>
axiomatization where
  rate_1: "\<forall> p s t. correct p t \<and> s \<le> t \<longrightarrow> PC p t - PC p s \<le> (t - s)*(1 + \<rho>)" and
  rate_2: "\<forall> p s t. correct p t \<and> s \<le> t \<longrightarrow> (t - s)*(1 - \<rho>) \<le> PC p t - PC p s"

text\<open>Condition 3: bounded interval\<close>
axiomatization where
  rts0: "\<forall> p t i. correct p t \<and> t \<le> te p (i+1) \<longrightarrow> t - te p i \<le> rmax" and
  rts1: "\<forall> p t i. correct p t \<and> te p (i+1) \<le> t \<longrightarrow> rmin \<le> t - te p i"

text\<open>Condition 4 : bounded delay\<close>
axiomatization where
  rts2a: "\<forall> p q t i. correct p t \<and> correct q t \<and> te q i + \<beta> \<le> t \<longrightarrow> te p i \<le> t"  and
  rts2b: "\<forall> p q i. correct p (te p i) \<and> correct q (te q i) \<longrightarrow> abs(te p i - te q i) \<le> \<beta>"

text\<open>Condition 5: initial synchronization\<close>
axiomatization where
  synch0: "\<forall> p. te p 0 = 0"

text\<open>Condition 6: nonoverlap\<close>
axiomatization where
  nonoverlap: "\<beta> \<le> rmin"

text\<open>Condition 7: reading errors\<close>
axiomatization where
  readerror: "\<forall> p q i. correct p (te p (i+1)) \<and> correct q (te p (i+1)) \<longrightarrow> 
              abs(\<theta> p (i+1) q - IC q i (te p (i+1))) \<le> \<Lambda>"

text\<open>Condition 8: bounded faults\<close>
axiomatization where
  correct_closed: "\<forall> p s t. s \<le> t \<and> correct p t \<longrightarrow> correct p s" and
  correct_count:  "\<forall> t. np - maxfaults \<le> count (\<lambda> p. correct p t) np"

text\<open>Condition 9: Translation invariance\<close>
axiomatization where
  trans_inv: "\<forall> p f x. 0 \<le> x \<longrightarrow> cfn p (\<lambda> y. f y + x) = cfn p f + x"

text\<open>Condition 10: precision enhancement\<close>
axiomatization where
  prec_enh: 
  "\<forall> ppred p q f g x y. 
          np - maxfaults \<le> count ppred np \<and> 
          okRead1 f y ppred \<and> okRead1 g y ppred \<and> 
          okRead2 f g x ppred \<and> ppred p \<and> ppred q 
      \<longrightarrow> abs(cfn p f - cfn q g) \<le> \<pi> x y"

text\<open>Condition 11: accuracy preservation\<close>
axiomatization where
  acc_prsv:
  "\<forall> ppred p q f x. okRead1 f x ppred \<and> np - maxfaults \<le> count ppred np
          \<and> ppred p \<and> ppred q \<longrightarrow> abs(cfn p f - f q) \<le> \<alpha> x"


subsubsection\<open>Some derived properties of clocks\<close>

lemma rts0d: 
assumes cp: "correct p (te p (i+1))"
shows "te p (i+1) - te p i \<le> rmax"
using cp rts0 by simp

lemma rts1d:
assumes cp: "correct p (te p (i+1))"
shows "rmin \<le> te p (i+1) - te p i"
using cp rts1 by simp

lemma rte: 
assumes cp: "correct p (te p (i+1))"
shows "te p i \<le> te p (i+1)"
proof-
  from cp rts1d have "rmin \<le> te p (i+1) - te p i"
    by simp
  from this constants_ax show ?thesis by arith
qed

lemma beta_bound1:
assumes corr_p: "correct p (te p (i+1))"
and corr_q: "correct q (te p (i+1))"
shows "0 \<le> te p (i+1) - te q i"
proof-
  from corr_p rte have "te p i \<le> te p (i+1)"
    by simp
  from this corr_p correct_closed have corr_pi: "correct p (te p i)"
    by blast
  from corr_p rts1d nonoverlap have "rmin \<le> te p (i+1) - te p i"
    by simp
  from this nonoverlap have "\<beta> \<le> te p (i+1) - te p i" by simp
  hence "te p i + \<beta> \<le> te p (i+1)" by simp

  from this corr_p corr_q rts2a 
  have "te q i \<le> te p (i+1)"
    by blast
  thus ?thesis by simp
qed

lemma beta_bound2:
assumes corr_p: "correct p (te p (i+1))"
and corr_q: "correct q (te q i)"
shows "te p (i+1) - te q i \<le> rmax + \<beta>"
proof-
  from corr_p rte have "te p i \<le> te p (i+1)"
    by simp
  from this corr_p correct_closed have corr_pi: "correct p (te p i)"
    by blast

  have split: "te p (i+1) - te q i =
    (te p (i+1) - te p i) + (te p i - te q i)"
    by (simp)

  from corr_q corr_pi rts2b have Eq1: "abs(te p i - te q i) \<le> \<beta>"
    by simp
  have Eq2: "te p i - te q i \<le> \<beta>"
  proof cases
    assume "te q i \<le> te p i"
    from this Eq1 show ?thesis
      by (simp add: abs_if)
  next
    assume "\<not> (te q i \<le> te p i)"
    from this Eq1 show ?thesis
      by (simp add: abs_if)
  qed

  from corr_p rts0d have "te p (i+1) - te p i \<le> rmax"
    by simp
  from this split Eq2 show ?thesis by simp
qed

subsubsection\<open>Bounded-drift for logical clocks (IC)\<close>

lemma bd: 
  assumes ie: "s \<le> t"
  and rb1: "rho_bound1 C"
  and rb2: "rho_bound2 D"
  and PC_ie: "D q t - D q s \<le> C p t - C p s"
  and corr_p: "correct p t"
  and corr_q: "correct q t"
  shows "\<bar> C p t - D q t \<bar>  \<le> \<bar> C p s - D q s \<bar> + 2*\<rho>*(t - s)"
proof-
  let ?Dt = "C p t - D q t"
  let ?Ds = "C p s - D q s"
  let ?Bp = "C p t - C p s"
  let ?Bq = "D q t - D q s"
  let ?I = "t - s"

  have "\<bar> ?Bp - ?Bq \<bar> \<le> 2*\<rho>*(t - s)"
  proof-
    from PC_ie have Eq1: "\<bar> ?Bp - ?Bq \<bar> = ?Bp - ?Bq" by (simp add: abs_if)
    from corr_p ie rb1 have Eq2: "?Bp - ?Bq \<le> ?I*(1+\<rho>) - ?Bq" (is "?E1 \<le> ?E2")
      by(simp add: rho_bound1_def)
    from corr_q ie rb2 have "?I*(1 - \<rho>) \<le> ?Bq"
      by(simp add: rho_bound2_def)
    from this have Eq3: "?E2 \<le> ?I*(1+\<rho>) - ?I*(1 - \<rho>)"
      by(simp)
    have Eq4: "?I*(1+\<rho>) - ?I*(1 - \<rho>) = 2*\<rho>*?I"
      by(simp add: algebra_simps)
    from Eq1 Eq2 Eq3 Eq4 show ?thesis by simp
  qed
  moreover
  have "\<bar>?Dt\<bar>  \<le> \<bar>?Bp - ?Bq\<bar>  + \<bar>?Ds\<bar>"
    by(simp add: abs_if)
  ultimately show ?thesis by simp
qed

lemma bounded_drift: 
  assumes ie: "s \<le> t"
  and rb1: "rho_bound1 C"
  and rb2: "rho_bound2 C"
  and rb3: "rho_bound1 D"
  and rb4: "rho_bound2 D"
  and corr_p: "correct p t"
  and corr_q: "correct q t"
  shows "\<bar>C p t - D q t\<bar> \<le> \<bar>C p s - D q s\<bar>  + 2*\<rho>*(t - s)"
proof-
  let ?Bp = "C p t - C p s"
  let ?Bq = "D q t - D q s"

  show ?thesis
  proof cases
    assume "?Bq \<le> ?Bp"
    from this ie rb1 rb4 corr_p corr_q bd show ?thesis by simp
  next
    assume "\<not> (?Bq \<le> ?Bp)"
    hence "?Bp \<le> ?Bq" by simp
    from this ie rb2 rb3 corr_p corr_q bd 
    have "\<bar>D q t - C p t\<bar>  \<le> \<bar>D q s - C p s\<bar> + 2*\<rho>*(t - s)"
      by simp
    from this show ?thesis by (simp add: abs_minus_commute)
  qed
qed

text\<open>Drift rate of logical clocks\<close>

lemma IC_rate1:
"rho_bound1 (\<lambda> p t. IC p i t)"
proof-
  {
    fix p::process
    fix s::time
    fix t::time
    assume cp: "correct p t"
    assume ie: "s \<le> t"
    from cp ie correct_closed have cps: "correct p s"
      by blast
    have "IC p i t - IC p i s \<le> (t - s)*(1+\<rho>)"
    proof-
      from cp IClock have "IC p i t = PC p t + Adj p i"
        by simp
      moreover
      from cps IClock have "IC p i s = PC p s + Adj p i"
        by simp
      moreover
      from cp ie rate_1 have "PC p t - PC p s \<le> (t - s)*(1+\<rho>)"
        by simp
      ultimately show ?thesis by simp
    qed
  }
  thus ?thesis by (simp add: rho_bound1_def)
qed

lemma IC_rate2:
"rho_bound2 (\<lambda> p t. IC p i t)"
proof-
  {
    fix p::process
    fix s::time
    fix t::time
    assume cp: "correct p t"
    assume ie: "s \<le> t"
    from cp ie correct_closed have cps: "correct p s"
      by blast
    have "(t - s)*(1 - \<rho>) \<le> IC p i t - IC p i s"
    proof-
      from cp IClock have "IC p i t = PC p t + Adj p i"
        by simp
      moreover
      from cps IClock have "IC p i s = PC p s + Adj p i"
        by simp
      moreover
      from cp ie rate_2 have "(t - s)*(1-\<rho>) \<le> PC p t - PC p s"
        by simp
      ultimately show ?thesis by simp
    qed
  }
  thus ?thesis by (simp add: rho_bound2_def)
qed

text\<open>Auxilary function \<open>ICf\<close>: we introduce this to avoid some
unification problem in some tactic of isabelle.\<close>

definition
  ICf :: "nat \<Rightarrow> (process \<Rightarrow> time \<Rightarrow> Clocktime)" where
  "ICf i = (\<lambda> p t. IC p i t)"

lemma IC_bd: 
  assumes ie: "s \<le> t"
  and corr_p: "correct p t"
  and corr_q: "correct q t"
  shows "\<bar>IC p i t - IC q j t\<bar> \<le> \<bar>IC p i s - IC q j s\<bar> + 2*\<rho>*(t - s)" 
proof-
  let ?C = "ICf i"
  let ?D = "ICf j"
  let ?G = "\<bar>?C p t - ?D q t\<bar> \<le> \<bar>?C p s - ?D q s\<bar> + 2*\<rho>*(t - s)"

  from IC_rate1 have rb1: "rho_bound1 (ICf i) \<and> rho_bound1 (ICf j)" 
    by (simp add: ICf_def)

  from IC_rate2 have rb2: "rho_bound2 (ICf i) \<and> rho_bound2 (ICf j)" 
    by (simp add: ICf_def)

  from ie rb1 rb2 corr_p corr_q bounded_drift
  have ?G by simp

  from this show ?thesis by (simp add: ICf_def)
qed

lemma event_bound: 
assumes ie1: "0 \<le> (t::real)"
and corr_p: "correct p t"
and corr_q: "correct q t"
shows "\<exists> i. t < max (te p i) (te q i)"
proof (rule ccontr)
  assume A: "\<not> (\<exists> i. t < max (te p i) (te q i))"
  show False 
  proof-
    have F1: "\<forall> i. te p i \<le> t"
    proof 
      fix i :: nat
      from A have "\<not> (t < max (te p i) (te q i))"
        by simp
      hence Eq1: "max (te p i) (te q i) \<le> t" by arith
      have Eq2: "te p i \<le> max (te p i) (te q i)"
        by (simp add: max_def)
      from Eq1 Eq2 show "te p i \<le> t" by simp
    qed
    
    have F2: "\<forall> (i :: nat). correct p (te p i)"
    proof
      fix i :: nat
      from F1 have "te p i \<le> t" by simp
      from this corr_p correct_closed 
      show "correct p (te p i)" by blast
    qed
     
    have F3: "\<forall> (i :: nat). real i * rmin \<le> te p i"
    proof
      fix i :: nat
      show "real i * rmin \<le> te p i"
      proof (induct i)
        from synch0 show "real (0::nat) * rmin \<le> te p 0" by simp
      next
        fix i :: nat assume ind_hyp: "real i * rmin \<le> te p i"
        
        show "real (Suc i) * rmin \<le> te p (Suc i)"
        proof-

          have Eq1: "real i * rmin + rmin = (real i + 1)*rmin" 
            by (simp add: distrib_right) 
          have Eq2: "real i + 1 = real (i+1)" by simp
          from Eq1 Eq2 
          have Eq3: "real i * rmin + rmin = real (i+1) * rmin"
            by presburger

          from F2 have cp1: "correct p (te p (i+1))"
            by simp
          from F2 have cp2: "correct p (te p i)"
            by simp
          from cp1 rts1d have "rmin \<le> te p (i+1) - te p i"
            by simp
          hence Eq4: "te p i + rmin \<le> te p (i+1)" by simp
          from ind_hyp have "real i * rmin + rmin \<le> te p i + rmin"
            by (simp)
          from this Eq4 have "real i * rmin + rmin \<le> te p (i+1)"
            by simp
          from this Eq3 show ?thesis by simp
        qed
      qed
    qed
    
    have F4: "\<forall> (i::nat). real i * rmin \<le> t"
    proof
      fix i::nat
      from F1 have "te p i \<le> t" by simp
      moreover
      from F3 have "real i * rmin \<le> te p i" by simp
      ultimately show "real i * rmin \<le> t" by simp
    qed

    from constants_ax have "0 < rmin" by simp

    from this reals_Archimedean3 
    have Archi: "\<exists> (k::nat). t < real k * rmin"
      by blast
    
    from Archi obtain k::nat where C: "t < real k * rmin" ..
    
    from F4 have "real k * rmin \<le> t" by simp 
    hence notC: "\<not> (t < real k * rmin)" by simp
    
    from C notC show False by simp
  qed
qed

subsection\<open>Agreement property\<close>

definition "\<gamma>1 x = \<pi> (2*\<rho>*\<beta> + 2*\<Lambda>) (2*\<Lambda> + x + 2*\<rho>*(rmax + \<beta>))"
definition "\<gamma>2 x = x + 2*\<rho>*rmax"
definition "\<gamma>3 x = \<alpha> (2*\<Lambda> + x + 2*\<rho>*(rmax + \<beta>)) + \<Lambda> + 2*\<rho>*\<beta>"

definition
  okmaxsync :: "[nat, Clocktime] \<Rightarrow> bool" where
  "okmaxsync i x \<longleftrightarrow> (\<forall> p q. correct p (max (te p i) (te q i))
     \<and> correct q (max (te p i) (te q i)) \<longrightarrow> 
       \<bar>IC p i (max (te p i) (te q i)) - IC q i (max (te p i) (te q i))\<bar> \<le> x)"

definition
  okClocks :: "[process, process, nat] \<Rightarrow> bool" where
  "okClocks p q i \<longleftrightarrow> (\<forall> t. 0 \<le> t \<and> t < max (te p i) (te q i)
        \<and> correct p t \<and> correct q t 
     \<longrightarrow> \<bar>VC p t - VC q t\<bar> \<le> \<delta>)"

lemma okClocks_sym:
assumes ok_pq: "okClocks p q i"
shows "okClocks q p i"
proof-
  {
    fix t :: time
    assume ie1: "0 \<le> t"
    assume ie2: "t < max (te q i) (te p i)"
    assume corr_q: "correct q t"
    assume corr_p: "correct p t"

    have "max (te q i) (te p i) = max (te p i) (te q i)"
      by (simp add: max_def)
    from this ok_pq ie1 ie2 corr_p corr_q 
    have "\<bar>VC q t - VC p t\<bar> \<le> \<delta>"
      by(simp add: abs_minus_commute okClocks_def)
  }
  thus ?thesis by (simp add: okClocks_def)
qed

lemma ICp_Suc: 
assumes corr_p: "correct p (te p (i+1))"
shows "IC p (i+1) (te p (i+1)) = cfn p (\<theta> p (i+1)) "
using corr_p IClock by(simp add: Adj_def)

lemma IC_trans_inv:
assumes ie1: "te q (i+1) \<le> te p (i+1)" 
and corr_p: "correct p (te p (i+1))"
and corr_q: "correct q (te p (i+1))"
shows 
"IC q (i+1) (te p (i+1)) =  
  cfn q (\<lambda> n. \<theta> q (i+1) n + (PC q (te p (i+1)) - PC q (te q (i+1))))"
(is "?T1 = ?T2")
proof-
  let ?X = "PC q (te p (i+1)) - PC q (te q (i+1))"


  from corr_q ie1 PC_monotone have posX: "0 \<le> ?X"
    by (simp add: le_diff_eq)
  from IClock corr_q have "?T1 = cfn q (\<theta> q (i+1)) + ?X"
    by(simp add: Adj_def)

  from this posX trans_inv show ?thesis by simp
qed

lemma beta_rho: 
assumes ie: "te q (i+1) \<le> te p (i+1)"
and corr_p: "correct p (te p (i+1))"
and corr_q: "correct q (te p (i+1))"
and corr_l: "correct l (te p (i+1))"
shows "\<bar>(PC l (te p (i+1)) - PC l (te q (i+1))) - (te p (i+1) - te q (i+1))\<bar> \<le> \<beta>*\<rho>"
proof-
  let ?X = "(PC l (te p (i+1)) - PC l (te q (i+1)))"
  let ?D = "te p (i+1) - te q (i+1)" 

  from ie have posD: "0 \<le> ?D" by simp

  from ie PC_monotone corr_l have posX: "0 \<le> ?X" 
    by (simp add: le_diff_eq)
  from ie corr_l rate_1 have bound1: "?X \<le> ?D * (1 + \<rho>)" by simp
  from ie corr_l correct_closed have corr_l_tq: "correct l (te q (i+1))"
    by(blast)
  from ie corr_q correct_closed have corr_q_tq: "correct q (te q (i+1))"
    by blast
  from corr_q_tq corr_p rts2b have "\<bar>?D\<bar> \<le> \<beta>"
    by(simp)
  from this constants_ax posD have D_beta: "?D*\<rho> \<le> \<beta>*\<rho>"
    by(simp add: abs_if)

  show ?thesis 
  proof cases
    assume A: "?D \<le> ?X"
    from posX posD A have absEq: "\<bar>?X - ?D\<bar> = ?X - ?D"
      by(simp add: abs_if)
    from bound1 have bound2: "?X - ?D \<le> ?D*\<rho>" 
      by(simp add: mult.commute distrib_right)
    from D_beta absEq bound2 show ?thesis by simp
  next
    assume notA: "\<not> (?D \<le> ?X)"
    from this have absEq2: "\<bar>?X - ?D\<bar> = ?D - ?X"
      by(simp add: abs_if)
    from ie corr_l rate_2 have bound3: "?D*(1 - \<rho>) \<le> ?X" by simp
    from this have "?D - ?X \<le> ?D*\<rho>" by (simp add: algebra_simps)
    from this absEq2 D_beta show ?thesis by simp
  qed
qed

text\<open>This lemma (and the next one pe-cond2) proves an assumption used 
in the precision enhancement.\<close>

lemma pe_cond1: 
assumes ie: "te q (i+1) \<le> te p (i+1)" 
and corr_p: "correct p (te p (i+1))"
and corr_q: "correct q (te p (i + 1))"
and corr_l: "correct l (te p (i+1))"
shows "\<bar>\<theta> q (i+1) l + (PC q (te p (i+1)) - PC q (te q (i+1))) - 
           \<theta> p (i+1) l\<bar> \<le> 2* \<rho> * \<beta> + 2*\<Lambda>"
(is "?M \<le> ?N")
proof-
  let ?Xl = "(PC l (te p (i+1)) - PC l (te q (i+1)))"
  let ?Xq = "(PC q (te p (i+1)) - PC q (te q (i+1)))"
  let ?D = "te p (i+1) - te q (i+1)" 
  let ?T = "\<theta> p (i+1) l - \<theta> q (i+1) l"
  let ?RE1 = "\<theta> p (i+1) l - IC l i (te p (i+1))"
  let ?RE2 = "\<theta> q (i+1) l - IC l i (te q (i+1))"
  let ?ICT = "IC l i (te p (i+1)) - IC l i (te q (i+1))"

  have "?M = \<bar>(?Xq - ?D) - (?T - ?D)\<bar>"
  by(simp add: abs_if)

  hence Split: "?M \<le> \<bar>?Xq - ?D\<bar> + \<bar>?T - ?D\<bar>"
    by(simp add: abs_if)

  from ie corr_q correct_closed have corr_q_tq: "correct q (te q (i+1))"
    by(blast)
  from ie corr_l correct_closed have corr_l_tq: "correct l (te q (i+1))"
    by blast

  from corr_p corr_q corr_l ie beta_rho 
  have XlD: "\<bar>?Xl - ?D\<bar> \<le> \<beta>*\<rho>"
    by simp
  
  from corr_p corr_q ie beta_rho 
  have XqD: "\<bar>?Xq - ?D\<bar> \<le> \<beta>*\<rho>" by simp

  have TD: "\<bar>?T - ?D\<bar> \<le> 2*\<Lambda> + \<beta>*\<rho>" 
  proof-
    have Eq1: "\<bar>?T - ?D\<bar> = \<bar>(?T - ?ICT) + (?ICT - ?D)\<bar>" (is "?E1 = ?E2")
      by (simp add: abs_if)
  
    have Eq2: "?E2 \<le> \<bar>?T - ?ICT\<bar> + \<bar>?ICT - ?D\<bar>" 
      by(simp add: abs_if)

    have Eq3: "\<bar>?T - ?ICT\<bar> \<le>  \<bar>?RE1\<bar> + \<bar>?RE2\<bar>"
      by(simp add: abs_if)

    from readerror corr_p corr_l 
    have Eq4: "\<bar>?RE1\<bar> \<le> \<Lambda>" by simp
     

    from corr_l_tq corr_q_tq this readerror 
    have Eq5: "\<bar>?RE2\<bar> \<le> \<Lambda>" by simp
    
    from Eq3 Eq4 Eq5 have Eq6: "\<bar>?T - ?ICT\<bar> \<le> 2*\<Lambda>"
      by simp

    have Eq7: "?ICT - ?D = ?Xl - ?D"
    proof-
      from corr_p rte have "te p i \<le> te p (i+1)"
        by(simp)
      from this corr_l correct_closed have corr_l_tpi: "correct l (te p i)"
        by blast
      from corr_q_tq rte have "te q i \<le> te q (i+1)"
        by simp
      from this corr_l_tq correct_closed have corr_l_tqi: "correct l (te q i)"
        by blast

      from IClock corr_l
      have F1: "IC l i (te p (i+1)) = PC l (te p (i+1)) + Adj l i"
        by(simp)
      from IClock corr_l_tq 
      have F2: "IC l i (te q (i+1)) = PC l (te q (i+1)) + Adj l i"
        by simp
      from F1 F2 show ?thesis by(simp)
    qed

    from this XlD have Eq8: "\<bar>?ICT - ?D\<bar> \<le> \<beta>*\<rho>"
      by arith
    from Eq1 Eq2 Eq6 Eq8 show ?thesis 
      by(simp)
  qed

  from Split XqD TD have F1: "?M \<le> 2* \<beta> * \<rho> + 2*\<Lambda>"
    by(simp)
  have F2: "2 * \<rho> * \<beta> + 2*\<Lambda> = 2* \<beta> * \<rho> + 2*\<Lambda>" 
    by simp
  from F1 show ?thesis by (simp only: F2)

qed

lemma pe_cond2: 
assumes ie: "te m i \<le> te l i"
and corr_k: "correct k (te k (i+1))"
and corr_l_tk: "correct l (te k (i+1))"
and corr_m_tk: "correct m (te k (i+1))"
and ind_hyp: "\<bar>IC l i (te l i) - IC m i (te l i)\<bar> \<le> \<delta>S"
shows "\<bar>\<theta> k (i+1) l - \<theta> k (i+1) m\<bar> \<le> 2*\<Lambda> + \<delta>S + 2*\<rho>*(rmax + \<beta>)"
proof-
  let ?X = "\<theta> k (i+1) l - \<theta> k (i+1) m"
  let ?N = "2*\<Lambda> + \<delta>S + 2*\<rho>*(rmax + \<beta>)"
  let ?D1 = "\<theta> k (i+1) l - IC l i (te k (i+1))"
  let ?D2 = "\<theta> k (i+1) m - IC m i (te k (i+1))"
  let ?ICS = "IC l i (te k (i+1)) - IC m i (te k (i+1))"
  let ?tlm = "te l i"
  let ?IC = "IC l i ?tlm - IC m i ?tlm"

  have Eq1: "\<bar>?X\<bar> = \<bar>(?D1 - ?D2) + ?ICS\<bar>" (is "?E1 = ?E2") 
    by (simp add: abs_if)

  have Eq2: "?E2 \<le> \<bar>?D1 - ?D2\<bar> + \<bar>?ICS\<bar>" by (simp add: abs_if)

  from corr_l_tk corr_k beta_bound1 have ie_lk: "te l i \<le> te k (i+1)" 
    by (simp add: le_diff_eq)
  
  from this corr_l_tk correct_closed have corr_l: "correct l (te l i)"
    by blast

  from ie_lk corr_l_tk corr_m_tk IC_bd
  have Eq3: "\<bar>?ICS\<bar> \<le> \<bar>?IC\<bar> + 2*\<rho>*(te k (i+1) - ?tlm)"
    by simp
  from this ind_hyp have Eq4: "\<bar>?ICS\<bar> \<le> \<delta>S + 2*\<rho>*(te k (i+1) - ?tlm)"
    by simp

  from corr_l corr_k beta_bound2 have "te k (i+1) - ?tlm \<le> rmax + \<beta>"
    by simp
  from this constants_ax have "2*\<rho>*(te k (i+1) - ?tlm) \<le> 2*\<rho>*(rmax + \<beta>)"
    by (simp add: real_mult_le_cancel_iff2)
  from this Eq4 have Eq4a: "\<bar>?ICS\<bar> \<le> \<delta>S + 2*\<rho>*(rmax + \<beta>)"
    by (simp)

  from corr_k corr_l_tk readerror 
  have Eq5: "\<bar>?D1\<bar> \<le> \<Lambda>" by simp
  from corr_k corr_m_tk readerror 
  have Eq6: "\<bar>?D2\<bar> \<le> \<Lambda>" by simp
  have "\<bar>?D1 - ?D2\<bar> \<le> \<bar>?D1\<bar> + \<bar>?D2\<bar>" by (simp add: abs_if)
  from this Eq5 Eq6 have Eq7: "\<bar>?D1 - ?D2\<bar> \<le> 2*\<Lambda>"
    by (simp)

  from Eq1 Eq2 Eq4a Eq7 split show ?thesis by (simp)
qed

lemma theta_bound:
assumes corr_l: "correct l (te p (i+1))"
and corr_m: "correct m (te p (i+1))"
and corr_p: "correct p (te p (i+1))"
and IC_bound: 
    "\<bar>IC l i (max (te l i) (te m i)) - IC m i (max (te l i) (te m i))\<bar>
      \<le> \<delta>S"
shows "\<bar>\<theta> p (i+1) l - \<theta> p (i+1) m\<bar>
       \<le>  2*\<Lambda> + \<delta>S + 2*\<rho>*(rmax + \<beta>)"
proof-
  from corr_p corr_l beta_bound1 have tli_le_tp: "te l i \<le> te p (i+1)"
    by (simp add: le_diff_eq)
  from corr_p corr_m beta_bound1 have tmi_le_tp: "te m i \<le> te p (i+1)"
    by (simp add: le_diff_eq)
  
  let ?tml = "max (te l i) (te m i)"
  from tli_le_tp tmi_le_tp have tml_le_tp: "?tml \<le> te p (i+1)"
    by simp

  from tml_le_tp corr_l correct_closed have corr_l_tml: "correct l ?tml"
    by blast
  from tml_le_tp corr_m correct_closed have corr_m_tml: "correct m ?tml"
    by blast

  let ?Y = "2*\<Lambda> + \<delta>S + 2*\<rho>*(rmax + \<beta>)"
  show "\<bar>\<theta> p (i+1) l - \<theta> p (i+1) m\<bar> \<le> ?Y"
  proof cases
    assume A: "te m i < te l i"

    from this IC_bound 
    have "\<bar>IC l i (te l i) - IC m i (te l i)\<bar> \<le> \<delta>S"
      by(simp add: max_def)
    from this A corr_p corr_l corr_m pe_cond2 
    show ?thesis by(simp) 
  next
    assume "\<not> (te m i < te l i)"
    hence Eq1: "te l i \<le> te m i" by simp
    from this IC_bound 
    have Eq2: "\<bar>IC l i (te m i) - IC m i (te m i)\<bar> \<le> \<delta>S"
      by(simp add: max_def)

    hence "\<bar>IC m i (te m i) - IC l i (te m i)\<bar> \<le> \<delta>S"
      by (simp add: abs_minus_commute)
    from this Eq1 corr_p corr_l corr_m pe_cond2 
    have "\<bar>\<theta> p (i+1) m - \<theta> p (i+1) l\<bar> \<le> ?Y"
      by(simp)
    thus ?thesis by (simp add: abs_minus_commute)
  qed
qed

lemma four_one_ind_half: 
  assumes ie1: "\<beta> \<le> rmin"
  and ie2: "\<mu> \<le> \<delta>S"
  and ie3: "\<gamma>1 \<delta>S \<le> \<delta>S"
  and ind_hyp: "okmaxsync i \<delta>S"
  and ie4: "te q (i+1) \<le> te p (i+1)"
  and corr_p: "correct p (te p (i+1))"
  and corr_q: "correct q (te p (i+1))"
shows "\<bar>IC p (i+1) (te p (i+1)) - IC q (i+1) (te p (i+1))\<bar> \<le> \<delta>S"
proof-
  let ?tpq = "te p (i+1)"

  let ?f = "\<lambda> n. \<theta> q (i+1) n + (PC q (te p (i+1)) - PC q (te q (i+1)))"
  let ?g = "\<theta> p (i+1)"

  from ie4 corr_q correct_closed have corr_q_tq: "correct q (te q (i+1))"
    by blast
  
  have Eq_IC_cfn: "\<bar>IC p (i+1) ?tpq - IC q (i+1) ?tpq\<bar> = 
    \<bar>cfn q ?f - cfn p ?g\<bar>"
  proof-
    from corr_p ICp_Suc have Eq1: "IC p (i+1) ?tpq = cfn p ?g" by simp 
    
    from ie4 corr_p corr_q IC_trans_inv 
    have Eq2: "IC q (i+1) ?tpq = cfn q ?f" by simp
      
    from Eq1 Eq2 show ?thesis by(simp add: abs_if)
  qed

  let ?ppred = "\<lambda> l. correct l (te p (i+1))"
    
  let ?X = "2*\<rho>*\<beta> + 2*\<Lambda>"
  have "\<forall> l. ?ppred l \<longrightarrow> \<bar>?f l - ?g l\<bar> \<le> ?X"
  proof -
    {
      fix l
      assume "?ppred l"
      from ie4 corr_p corr_q this pe_cond1
      have "\<bar>?f l - ?g l\<bar> \<le> (2*\<rho>*\<beta> + 2*\<Lambda>)"
        by(auto)
    }
    thus ?thesis by blast
  qed
  hence cond1: "okRead2 ?f ?g ?X ?ppred" 
    by(simp add: okRead2_def)
    
  let ?Y = "2*\<Lambda> + \<delta>S + 2*\<rho>*(rmax + \<beta>)"

  have "\<forall> l m. ?ppred l \<and> ?ppred m \<longrightarrow> \<bar>?f l - ?f m\<bar> \<le> ?Y"
  proof-
    {
      fix l m
      assume corr_l: "?ppred l"
      assume corr_m: "?ppred m"

      from corr_p corr_l beta_bound1 have tli_le_tp: "te l i \<le> te p (i+1)"
        by (simp add: le_diff_eq)
      from corr_p corr_m beta_bound1 have tmi_le_tp: "te m i \<le> te p (i+1)"
        by (simp add: le_diff_eq)

      let ?tlm = "max (te l i) (te m i)"

      from tli_le_tp tmi_le_tp have tlm_le_tp: "?tlm \<le> te p (i+1)"
        by simp

      from ie4 corr_l correct_closed have corr_l_tq: "correct l (te q (i+1))"
        by blast
      from ie4 corr_m correct_closed have corr_m_tq: "correct m (te q (i+1))"
        by blast
      from tlm_le_tp corr_l correct_closed have corr_l_tlm: "correct l ?tlm"
        by blast
      from tlm_le_tp corr_m correct_closed have corr_m_tlm: "correct m ?tlm"
        by blast

      from ind_hyp corr_l_tlm corr_m_tlm 
      have EqAbs1: "\<bar>IC l i ?tlm - IC m i ?tlm\<bar> \<le> \<delta>S"
        by(auto simp add: okmaxsync_def)

      have EqAbs3: "\<bar>?f l - ?f m\<bar> = \<bar>\<theta> q (i+1) l - \<theta> q (i+1) m\<bar>"
        by (simp add: abs_if)

      from EqAbs1 corr_q_tq corr_l_tq corr_m_tq theta_bound
      have "\<bar>\<theta> q (i+1) l - \<theta> q (i+1) m\<bar> \<le> ?Y"
        by simp
      from this EqAbs3  have "\<bar>?f l - ?f m\<bar> \<le> ?Y"
        by simp
    }
    thus ?thesis by simp
  qed
  hence cond2a: "okRead1 ?f ?Y ?ppred" by (simp add: okRead1_def) 

  have "\<forall> l m. ?ppred l \<and> ?ppred m \<longrightarrow> \<bar>?g l - ?g m\<bar> \<le> ?Y"
  proof-
    {
      fix l m
      assume corr_l: "?ppred l"
      assume corr_m: "?ppred m"

      from corr_p corr_l beta_bound1 have tli_le_tp: "te l i \<le> te p (i+1)"
        by (simp add: le_diff_eq)
      from corr_p corr_m beta_bound1 have tmi_le_tp: "te m i \<le> te p (i+1)"
        by (simp add: le_diff_eq)

      let ?tlm = "max (te l i) (te m i)"
      from tli_le_tp tmi_le_tp have tlm_le_tp: "?tlm \<le> te p (i+1)"
        by simp

      from tlm_le_tp corr_l correct_closed have corr_l_tlm: "correct l ?tlm"
        by blast
      from tlm_le_tp corr_m correct_closed have corr_m_tlm: "correct m ?tlm"
        by blast

      from ind_hyp corr_l_tlm corr_m_tlm 
      have EqAbs1: "\<bar>IC l i ?tlm - IC m i ?tlm\<bar> \<le> \<delta>S"
        by(auto simp add: okmaxsync_def)

      from EqAbs1 corr_p corr_l corr_m theta_bound
      have "\<bar>?g l - ?g m\<bar> \<le> ?Y" by simp
    }
    thus ?thesis by simp
  qed
  hence cond2b: "okRead1 ?g ?Y ?ppred" by (simp add: okRead1_def) 

  from correct_count have "np - maxfaults \<le> count ?ppred np"
    by simp
  from this corr_p corr_q cond1 cond2a cond2b prec_enh 
  have "\<bar>cfn q ?f - cfn p ?g\<bar> \<le> \<pi> ?X ?Y" 
    by blast

  from ie3 this have "\<bar>cfn q ?f - cfn p ?g\<bar> \<le> \<delta>S"
    by (simp add: \<gamma>1_def)

  from this Eq_IC_cfn show ?thesis by (simp)
qed

text\<open>Theorem 4.1 in Shankar's paper.\<close>

theorem four_one: 
  assumes ie1: "\<beta> \<le> rmin"
  and ie2: "\<mu> \<le> \<delta>S"
  and ie3: "\<gamma>1 \<delta>S \<le> \<delta>S"
shows "okmaxsync i \<delta>S"
proof(induct i)
  show "okmaxsync 0 \<delta>S"
  proof-
    {
      fix p q 
      assume corr_p: "correct p (max (te p 0) (te q 0))"
      assume corr_q: "correct q (max (te p 0) (te q 0))"

      from corr_p synch0 have cp0: "correct p 0" by simp
      from corr_q synch0 have cq0: "correct q 0" by simp

      from synch0 cp0 cq0 IClock 
      have IC_eq_PC: 
        "\<bar>IC p 0 (max (te p 0) (te q 0)) - IC q 0 (max (te p 0) (te q 0))\<bar>
         = \<bar>PC p 0 - PC q 0\<bar>" (is "?T1 = ?T2")
        by(simp add: Adj_def)

      from ie2 init synch0 cp0 have range1: "0 \<le> PC p 0 \<and> PC p 0 \<le> \<delta>S"  
        by auto
      from ie2 init synch0 cq0 have range2: "0 \<le> PC q 0 \<and> PC q 0 \<le> \<delta>S"
        by auto
      have "?T2 \<le> \<delta>S"
      proof cases
        assume A:"PC p 0 < PC q 0"
        from A range1 range2 show ?thesis 
          by(auto simp add: abs_if)
      next
        assume notA: "\<not> (PC p 0 < PC q 0)"
        from notA range1 range2 show ?thesis
          by(auto simp add: abs_if)
      qed
      from this IC_eq_PC have "?T1 \<le> \<delta>S" by simp
    }
    thus ?thesis by (simp add: okmaxsync_def)
  qed
next
  fix i assume ind_hyp: "okmaxsync i \<delta>S"
  show "okmaxsync (Suc i) \<delta>S"
  proof-
    {
      fix p q
      assume corr_p: "correct p (max (te p (i + 1)) (te q (i + 1)))"
      assume corr_q: "correct q (max (te p (i + 1)) (te q (i + 1)))"
      let ?tp = "te p (i + 1)"
      let ?tq = "te q (i + 1)"
      let ?tpq = "max ?tp ?tq"

      have "\<bar>IC p (i+1) ?tpq - IC q (i+1) ?tpq\<bar> \<le> \<delta>S" (is "?E1 \<le> \<delta>S")
      proof cases
        assume A: "?tq < ?tp"
        from A corr_p have cp1: "correct p (te p (i+1))" 
          by (simp add: max_def)
        from A corr_q have cq1: "correct q (te p (i+1))" 
          by (simp add: max_def)
        from A 
        have Eq1: "?E1 = \<bar>IC p (i+1) (te p (i+1)) - IC q (i+1) (te p (i+1))\<bar>" 
                  (is "?E1 = ?E2")
          by (simp add: max_def)
        from A cp1 cq1 corr_p corr_q ind_hyp ie1 ie2 ie3 
          four_one_ind_half 
        have "?E2 \<le> \<delta>S" by (simp)
        from this Eq1 show ?thesis by simp
      next
        assume notA: "\<not> (?tq < ?tp)"
        from this corr_p have cp2: "correct p (te q (i+1))" 
          by (simp add: max_def)
        from notA corr_q have cq2: "correct q (te q (i+1))"
          by (simp add: max_def)
        from notA 
        have Eq2: "?E1 = \<bar>IC q (i+1) (te q (i+1)) - IC p (i+1) (te q (i+1))\<bar>" 
                  (is "?E1  = ?E3")
          by (simp add: max_def abs_minus_commute)
        from notA have "?tp \<le> ?tq" by simp
        from this cp2 cq2 ind_hyp ie1 ie2 ie3 four_one_ind_half
        have "?E3 \<le> \<delta>S"
          by simp
        from this Eq2 show ?thesis by (simp)
      qed
    }
    thus ?thesis by (simp add: okmaxsync_def)
  qed
qed

lemma VC_cfn: 
  assumes corr_p: "correct p (te p (i+1))"
  and ie: "te p (i+1) < te p (i+2)"
shows "VC p (te p (i+1)) = cfn p (\<theta> p (i+1))"
proof-
  from ie corr_p VClock have "VC p (te p (i+1)) = IC p (i+1) (te p (i+1))"
    by simp
  moreover
  from corr_p IClock 
  have "IC p (i+1) (te p (i+1)) = PC p (te p (i+1)) + Adj p (i+1)"
    by blast
  moreover
  have "PC p (te p (i+1)) + Adj p (i+1) = cfn p (\<theta> p (i+1))"
    by(simp add: Adj_def)
  ultimately show ?thesis by simp
qed

text\<open>Lemma for the inductive case in Theorem 4.2\<close>

lemma four_two_ind:
  assumes ie1: "\<beta> \<le> rmin"
  and ie2: "\<mu> \<le> \<delta>S"
  and ie3: "\<gamma>1 \<delta>S \<le> \<delta>S"
  and ie4: "\<gamma>2 \<delta>S \<le> \<delta>"
  and ie5: "\<gamma>3 \<delta>S \<le> \<delta>"
  and ie6: "te q (i+1) \<le> te p (i+1)"
  and ind_hyp: "okClocks p q i"
  and t_bound1: "0 \<le> t"
  and t_bound2: "t < max (te p (i+1)) (te q (i+1))"
  and t_bound3: "max (te p i) (te q i) \<le> t"
  and tpq_bound: "max (te p i) (te q i) < max (te p (i+1)) (te q (i+1))"
  and corr_p: "correct p t"
  and corr_q: "correct q t"
shows "\<bar>VC p t - VC q t\<bar> \<le> \<delta>"
proof cases
  assume A: "t < te q (i+1)"
  
  let ?tpq = "max (te p i) (te q i)"
  
  have Eq1: "te p i \<le> t \<and> te q i \<le> t" 
  proof cases
    assume "te p i \<le> te q i"
    from this  t_bound3 show ?thesis by (simp add: max_def)
  next
    assume "\<not> (te p i \<le> te q i)"
    from this t_bound3 show ?thesis by (simp add: max_def)
  qed
  
  from ie6 have tp_max: "max (te p (i+1)) (te q (i+1)) = te p (i+1)"
    by(simp add: max_def)
  from this t_bound2 have Eq2: "t < te p (i+1)" by simp

  from VClock Eq1 Eq2 corr_p have Eq3: "VC p t = IC p i t" by simp
    
  from VClock Eq1 A corr_q have Eq4: "VC q t = IC q i t" by simp
  from Eq3 Eq4 have Eq5: "\<bar>VC p t - VC q t\<bar> = \<bar>IC p i t - IC q i t\<bar>"
    by simp

  from t_bound3 corr_p corr_q correct_closed
  have corr_tpq: "correct p ?tpq \<and> correct q ?tpq"
    by(blast)

  from t_bound3 IC_bd corr_p corr_q
  have Eq6: "\<bar>IC p i t - IC q i t\<bar>  \<le> \<bar>IC p i ?tpq - IC q i ?tpq\<bar>
    + 2*\<rho>*(t - ?tpq)" (is "?E1 \<le> ?E2")
    by(blast)
  
  from ie1 ie2 ie3 four_one have "okmaxsync i \<delta>S" by simp

  from this corr_tpq have "\<bar>IC p i ?tpq - IC q i ?tpq\<bar> \<le> \<delta>S"
    by(simp add: okmaxsync_def)
  
  from Eq6 this  have Eq7: "?E1 \<le> \<delta>S + 2*\<rho>*(t - ?tpq)" by simp

  from corr_p Eq2 rts0 have "t - te p i \<le> rmax" by simp
  from this have "t - ?tpq \<le> rmax" by (simp add: max_def)
  from this constants_ax have "2*\<rho>*(t - ?tpq) \<le> 2*\<rho>*rmax" 
    by (simp add: real_mult_le_cancel_iff1) 
  hence "\<delta>S + 2*\<rho>*(t - ?tpq) \<le> \<delta>S + 2*\<rho>*rmax"
    by simp
  from this Eq7 have "?E1 \<le> \<delta>S + 2*\<rho>*rmax" by simp
  from this Eq5 ie4 show ?thesis by(simp add: \<gamma>2_def)
next
  assume "\<not> (t < te q (i+1))"
  hence  B: "te q (i+1) \<le> t" by simp

  from ie6 t_bound2 
  have tp_max: "max (te p (i+1)) (te q (i+1)) = te p (i+1)"
    by(simp add: max_def)

  have "te p i \<le> max (te p i) (te q i)"
    by(simp add: max_def)

  from this t_bound3 have tp_bound1: "te p i \<le> t" by simp

  from tp_max t_bound2 have tp_bound2: "t < te p (i+1)" by simp

  have tq_bound1: "t < te q (i+2)"
  proof (rule ccontr)
    assume "\<not> (t < te q (i+2))"
    hence C: "te q (i+2) \<le> t" by simp

    from C corr_q correct_closed 
    have corr_q_t2: "correct q (te q (i+2))" by blast

    have "te q (i+1) + \<beta> \<le> t"
    proof-
      from corr_q_t2 rts1d have "rmin \<le> te q (i+2) - te q (i+1)"
        by simp
      from this ie1 have "\<beta> \<le> te q (i+2) - te q (i+1)"
        by simp
      hence "te q (i+1) + \<beta> \<le> te q (i+2)" by simp
      from this C show ?thesis by simp
    qed
    from this corr_p corr_q rts2a have "te p (i+1) \<le> t"
      by blast
    hence "\<not> (t < te p (i+1))" by simp
    from this tp_bound2 show False by simp
  qed

  from tq_bound1 B have tq_bound2: "te q (i+1) < te q (i+2)" by simp
  from B tp_bound2 have tq_bound3: "te q (i+1) < te p (i+1)"
    by simp
  from B corr_p correct_closed 
  have corr_p_tq1: "correct p (te q (i+1))" by blast

  from B correct_closed corr_q 
  have corr_q_tq1: "correct q (te q (i+1))" by blast

  from corr_p_tq1 corr_q_tq1 beta_bound1 
  have tq_bound4: "te p i \<le> te q (i+1)" 
    by(simp add: le_diff_eq)

  from tq_bound1 VClock B corr_q 
  have Eq1: "VC q t = IC q (i+1) t" by simp
  
  from VClock tp_bound1 tp_bound2 corr_p
  have Eq2: "VC p t = IC p i t" by simp
  
  from Eq1 Eq2 have Eq3: "\<bar>VC p t - VC q t\<bar> = \<bar>IC p i t - IC q (i+1) t\<bar>"
    by simp
  
  from B corr_p corr_q IC_bd 
  have "\<bar>IC p i t - IC q (i+1) t\<bar> \<le> 
     \<bar>IC p i (te q (i+1)) - IC q (i+1) (te q (i+1))\<bar> + 2*\<rho>*(t - te q (i+1))" 
    by simp

  from this Eq3 
  have VC_split: "\<bar>VC p t - VC q t\<bar> \<le> 
    \<bar>IC p i (te q (i+1)) - IC q (i+1) (te q (i+1))\<bar> + 2*\<rho>*(t - te q (i+1))" 
    by simp

  from tq_bound2 VClock corr_q_tq1
  have Eq4: "VC q (te q (i+1)) = IC q (i+1) (te q (i+1))" by simp

  from this tq_bound2 VC_cfn corr_q_tq1 
  have Eq5: "IC q (i+1) (te q (i+1)) = cfn q (\<theta> q (i+1))" by simp
    
  hence IC_eq_cfn: "IC p i (te q (i+1)) - IC q (i+1) (te q (i+1)) = 
    IC p i (te q (i+1)) - cfn q (\<theta> q (i+1))"
    (is "?E1 = ?E2") 
    by simp

  let ?f = "\<theta> q (i+1)"
  let ?ppred = "\<lambda> l. correct l (te q (i+1))"
  let ?X = "2*\<Lambda> + \<delta>S + 2*\<rho>*(rmax + \<beta>)"

  have "\<forall> l m. ?ppred l \<and> ?ppred m \<longrightarrow> \<bar>\<theta> q (i+1) l - \<theta> q (i+1) m\<bar> \<le> ?X"
  proof-
    {
      fix l :: process
      fix m :: process
      assume corr_l: "?ppred l"
      assume corr_m: "?ppred m"
      
      let ?tlm = "max (te l i) (te m i)"
      have tlm_bound: "?tlm \<le> te q (i+1)"
      proof-
        from corr_l corr_q_tq1 beta_bound1 have "te l i \<le> te q (i+1)"
          by (simp add: le_diff_eq)
        moreover
        from corr_m corr_q_tq1 beta_bound1 have "te m i \<le> te q (i+1)"
          by (simp add: le_diff_eq)
        ultimately show ?thesis by simp
      qed
        
      from tlm_bound corr_l corr_m correct_closed 
      have corr_tlm: "correct l ?tlm \<and> correct m ?tlm"
        by blast

      have "\<bar>IC l i ?tlm - IC m i ?tlm\<bar> \<le> \<delta>S"
      proof-
        from ie1 ie2 ie3 four_one  have "okmaxsync i \<delta>S"
          by simp
        from this corr_tlm show ?thesis by(simp add: okmaxsync_def)
      qed

      from this corr_l corr_m corr_q_tq1 theta_bound
      have "\<bar>\<theta> q (i+1) l - \<theta> q (i+1) m\<bar> \<le> ?X" by simp
    }
    thus ?thesis by blast
  qed
  hence readOK: "okRead1 (\<theta> q (i+1)) ?X ?ppred"
    by(simp add: okRead1_def)

  let ?E3 = "cfn q (\<theta> q (i+1)) - \<theta> q (i+1) p"
  let ?E4 = "\<theta> q (i+1) p - IC p i (te q (i+1))"

  have "\<bar>?E2\<bar> = \<bar>?E3 + ?E4\<bar>" by (simp add: abs_if)
  hence Eq8: "\<bar>?E2\<bar> \<le> \<bar>?E3\<bar> + \<bar>?E4\<bar>" by (simp add: abs_if)
 
  from correct_count have ppredOK: "np - maxfaults \<le> count ?ppred np"
    by simp
  from readOK ppredOK corr_p_tq1 corr_q_tq1 acc_prsv
  have "\<bar>?E3\<bar> \<le> \<alpha> ?X"
    by blast
  from this Eq8 have Eq9: "\<bar>?E2\<bar> \<le> \<alpha> ?X + \<bar>?E4\<bar>" by simp

  from corr_p_tq1 corr_q_tq1 readerror
  have "\<bar>?E4\<bar> \<le> \<Lambda>" by simp
    
  from this Eq9 have Eq10: "\<bar>?E2\<bar> \<le> \<alpha> ?X + \<Lambda>" by simp
  
  from this VC_split IC_eq_cfn 
  have almost_right: 
    "\<bar>VC p t - VC q t\<bar> \<le> 
     \<alpha> ?X + \<Lambda> + 2*\<rho>*(t - te q (i+1))" 
    by simp

  have "t - te q (i+1) \<le> \<beta>"
  proof (rule ccontr)
    assume "\<not> (t - te q (i+1) \<le> \<beta>)"
    hence "te q (i+1) + \<beta> \<le> t" by simp
    from this corr_p corr_q rts2a have "te p (i+1) \<le> t"
      by auto
    hence "\<not> (t < te p (i+1))" by simp
    from this tp_bound2 show False
      by simp
  qed

  from this constants_ax 
  have "\<alpha> ?X + \<Lambda> + 2*\<rho>*(t - te q (i+1)) 
        \<le> \<alpha> ?X + \<Lambda> + 2*\<rho>*\<beta>"
    by (simp)

  from this almost_right 
  have "\<bar>VC p t - VC q t\<bar> \<le> \<alpha> ?X + \<Lambda> + 2*\<rho>*\<beta>" 
    by arith

  from this ie5 show ?thesis by (simp add: \<gamma>3_def)
qed

text\<open>Theorem 4.2 in Shankar's paper.\<close>

theorem four_two: 
  assumes ie1: "\<beta> \<le> rmin"
  and ie2: "\<mu> \<le> \<delta>S"
  and ie3: "\<gamma>1 \<delta>S \<le> \<delta>S"
  and ie4: "\<gamma>2 \<delta>S \<le> \<delta>"
  and ie5: "\<gamma>3 \<delta>S \<le> \<delta>"
shows "okClocks p q i"
proof (induct i)
  show "okClocks p q 0"
  proof-
    {
      fix t :: time
      assume t_bound1: "0 \<le> t"
      assume t_bound2: "t < max (te p 0) (te q 0)"
      assume corr_p: "correct p t"
      assume corr_q: "correct q t"
      from t_bound2 synch0 have "t < 0"
        by(simp add: max_def)
      from this t_bound1 have False by simp
      hence "\<bar>VC p t - VC q t\<bar> \<le> \<delta>" by simp
    }
    thus ?thesis by (simp add: okClocks_def)
  qed
next
  fix i::nat assume ind_hyp: "okClocks p q i"
  show "okClocks p q (Suc i)"
  proof -
    {
      fix t :: time
      assume t_bound1: "0 \<le> t"
      assume t_bound2: "t < max (te p (i+1)) (te q (i+1))"
      assume corr_p: "correct p t"
      assume corr_q: "correct q t"
      
      let ?tpq1 = "max (te p i) (te q i)"
      let ?tpq2 = "max (te p (i+1)) (te q (i+1))"

      have "\<bar>VC p t - VC q t\<bar> \<le> \<delta>"
      proof cases
        assume tpq_bound: "?tpq1 < ?tpq2"
        show ?thesis 
        proof cases
          assume "t < ?tpq1"
          from t_bound1 this  corr_p corr_q ind_hyp
          show ?thesis by(simp add: okClocks_def)
        next
          assume "\<not> (t < ?tpq1)"
          hence tpq_le_t: "?tpq1 \<le> t" by arith

          show ?thesis 
          proof cases
            assume A: "te q (i+1) \<le> te p (i+1)"

            from this tpq_le_t tpq_bound ie1 ie2 ie3 ie4 ie5 
              ind_hyp t_bound1 t_bound2 
              corr_p corr_q tpq_bound four_two_ind
            show ?thesis by(simp)
          next
            assume "\<not> (te q (i+1) \<le> te p (i+1))"
            hence B: "te p (i+1) \<le> te q (i+1)" by simp
            
            from ind_hyp okClocks_sym have ind_hyp1: "okClocks q p i" 
              by blast

            have maxsym1: "max (te p (i+1)) (te q (i+1)) = max (te q (i+1)) (te p (i+1))"
              by (simp add: max_def)
            have maxsym2: "max (te p i) (te q i) = max (te q i) (te p i)" 
              by (simp add: max_def)

            from maxsym1 t_bound2 
            have t_bound21: "t < max (te q (i+1)) (te p (i+1))"
              by simp
            
            from maxsym1 maxsym2 tpq_bound 
            have tpq_bound1: "max (te q i) (te p i) < max (te q (i+1)) (te p (i+1))"
              by simp
            from maxsym2 tpq_le_t 
            have tpq_le_t1: "max (te q i) (te p i) \<le> t" by simp

            from B tpq_le_t1 tpq_bound1 ie1 ie2 ie3 ie4 ie5 
              ind_hyp1 t_bound1 t_bound21 
              corr_p corr_q tpq_bound four_two_ind
            have "\<bar>VC q t - VC p t\<bar> \<le> \<delta>" by(simp)
            thus ?thesis by (simp add: abs_minus_commute)
          qed

        qed
      next
        assume "\<not> (?tpq1 < ?tpq2)"
        hence "?tpq2 \<le> ?tpq1" by arith
        from t_bound2 this have "t < ?tpq1" by arith
        from t_bound1 this corr_p corr_q ind_hyp
        show ?thesis by(simp add: okClocks_def)
      qed
    }
    thus ?thesis by (simp add: okClocks_def)
  qed
qed
    
text\<open>The main theorem: all correct clocks are synchronized within the
bound delta.\<close>

theorem agreement: 
  assumes ie1: "\<beta> \<le> rmin"
  and ie2: "\<mu> \<le> \<delta>S"
  and ie3: "\<gamma>1 \<delta>S \<le> \<delta>S"
  and ie4: "\<gamma>2 \<delta>S \<le> \<delta>"
  and ie5: "\<gamma>3 \<delta>S \<le> \<delta>"
  and ie6: "0 \<le> t"
  and cpq: "correct p t \<and> correct q t"
shows "\<bar>VC p t - VC q t\<bar> \<le> \<delta>"
proof-
  from ie6 cpq event_bound have "\<exists> i :: nat. t < max (te p i) (te q i)"
    by simp
  from this obtain i  :: nat where t_bound: "t < max (te p i) (te q i)" ..
  
  from t_bound ie1 ie2 ie3 ie4 ie5 four_two have "okClocks p q i"
    by simp

  from ie6 this t_bound cpq show ?thesis 
    by (simp add: okClocks_def)
qed

end
