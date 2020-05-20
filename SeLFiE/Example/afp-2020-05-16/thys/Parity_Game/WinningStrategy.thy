section \<open>Winning Strategies\<close>

theory WinningStrategy
imports
  Main
  Strategy
begin

context ParityGame begin

text \<open>
  Here we define winning strategies.

  A strategy is winning for player @{term p} from @{term v0} if every maximal @{term \<sigma>}-path
  starting in @{term v0} is winning.
\<close>
definition winning_strategy :: "Player \<Rightarrow> 'a Strategy \<Rightarrow> 'a \<Rightarrow> bool" where
  "winning_strategy p \<sigma> v0 \<equiv> \<forall>P. vmc_path G P v0 p \<sigma> \<longrightarrow> winning_path p P"

lemma winning_strategyI [intro]:
  assumes "\<And>P. vmc_path G P v0 p \<sigma> \<Longrightarrow> winning_path p P"
  shows "winning_strategy p \<sigma> v0"
  unfolding winning_strategy_def using assms by blast

lemma (in vmc_path) paths_hits_winning_strategy_is_winning:
  assumes \<sigma>: "winning_strategy p \<sigma> v"
    and v: "v \<in> lset P"
  shows "winning_path p P"
proof-
  obtain n where n: "enat n < llength P" "P $ n = v" using v by (meson in_lset_conv_lnth)
  interpret P': vmc_path G "ldropn n P" v p \<sigma> using n vmc_path_ldropn by blast
  have "winning_path p (ldropn n P)" using \<sigma> by (simp add: winning_strategy_def P'.vmc_path_axioms)
  thus ?thesis using winning_path_drop_add P_valid n(1) by blast
qed

text \<open>There cannot exist winning strategies for both players for the same node.\<close>

lemma winning_strategy_only_for_one_player:
  assumes \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> v"
    and \<sigma>': "strategy p** \<sigma>'" "winning_strategy p** \<sigma>' v"
    and v: "v \<in> V"
  shows "False"
proof-
  obtain P where "vmc2_path G P v p \<sigma> \<sigma>'" using assms strategy_conforming_path_exists by blast
  then interpret vmc2_path G P v p \<sigma> \<sigma>' .
  have "winning_path p P"
    using paths_hits_winning_strategy_is_winning \<sigma>(2) v0_lset_P by blast
  moreover have "winning_path p** P"
    using comp.paths_hits_winning_strategy_is_winning \<sigma>'(2) v0_lset_P by blast
  ultimately show False using P_valid paths_are_winning_for_one_player by blast
qed

subsection \<open>Deadends\<close>

lemma no_winning_strategy_on_deadends:
  assumes "v \<in> VV p" "deadend v" "strategy p \<sigma>"
  shows "\<not>winning_strategy p \<sigma> v"
proof-
  obtain P where "vmc_path G P v p \<sigma>" using strategy_conforming_path_exists_single assms by blast
  then interpret vmc_path G P v p \<sigma> .
  have "P = LCons v LNil" using P_deadend_v0_LCons \<open>deadend v\<close> by blast
  hence "\<not>winning_path p P" unfolding winning_path_def using \<open>v \<in> VV p\<close> by auto
  thus ?thesis using winning_strategy_def vmc_path_axioms by blast
qed

lemma winning_strategy_on_deadends:
  assumes "v \<in> VV p" "deadend v" "strategy p \<sigma>"
  shows "winning_strategy p** \<sigma> v"
proof
  fix P assume "vmc_path G P v p** \<sigma>"
  then interpret vmc_path G P v "p**" \<sigma> .
  have "P = LCons v LNil" using P_deadend_v0_LCons \<open>deadend v\<close> by blast
  thus "winning_path p** P" unfolding winning_path_def
    using \<open>v \<in> VV p\<close> P_valid paths_are_winning_for_one_player by auto
qed

subsection \<open>Extension Theorems\<close>

lemma strategy_extends_VVp:
  assumes v0: "v0 \<in> VV p" "\<not>deadend v0"
  and \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> v0"
  shows "winning_strategy p \<sigma> (\<sigma> v0)"
proof
  fix P assume "vmc_path G P (\<sigma> v0) p \<sigma>"
  then interpret vmc_path G P "\<sigma> v0" p \<sigma> .
  have "v0\<rightarrow>\<sigma> v0" using v0 \<sigma>(1) strategy_def by blast
  hence "winning_path p (LCons v0 P)"
    using \<sigma>(2) extension_valid_maximal_conforming winning_strategy_def by blast
  thus "winning_path p P" using winning_path_ltl[of p "LCons v0 P"] by simp
qed

lemma strategy_extends_VVpstar:
  assumes v0: "v0 \<in> VV p**" "v0\<rightarrow>w0"
  and \<sigma>: "winning_strategy p \<sigma> v0"
  shows "winning_strategy p \<sigma> w0"
proof
  fix P assume "vmc_path G P w0 p \<sigma>"
  then interpret vmc_path G P w0 p \<sigma> .
  have "winning_path p (LCons v0 P)"
    using extension_valid_maximal_conforming VV_impl1 \<sigma> v0 winning_strategy_def
    by auto
  thus "winning_path p P" using winning_path_ltl[of p "LCons v0 P"] by auto
qed

lemma strategy_extends_backwards_VVpstar:
  assumes v0: "v0 \<in> VV p**"
    and \<sigma>: "strategy p \<sigma>" "\<And>w. v0\<rightarrow>w \<Longrightarrow> winning_strategy p \<sigma> w"
  shows "winning_strategy p \<sigma> v0"
proof
  fix P assume "vmc_path G P v0 p \<sigma>"
  then interpret vmc_path G P v0 p \<sigma> .
  show "winning_path p P" proof (cases)
    assume "deadend v0"
    thus ?thesis using P_deadend_v0_LCons winning_path_def v0 by auto
  next
    assume "\<not>deadend v0"
    then interpret vmc_path_no_deadend G P v0 p \<sigma> by unfold_locales
    interpret ltlP: vmc_path G "ltl P" w0 p \<sigma> using vmc_path_ltl .
    have "winning_path p (ltl P)"
      using \<sigma>(2) v0_edge_w0 vmc_path_ltl winning_strategy_def by blast
    thus "winning_path p P"
      using winning_path_LCons by (metis P_LCons' ltlP.P_LCons ltlP.P_not_null)
  qed
qed

lemma strategy_extends_backwards_VVp:
  assumes v0: "v0 \<in> VV p" "\<sigma> v0 = w" "v0\<rightarrow>w"
    and \<sigma>: "strategy p \<sigma>" "winning_strategy p \<sigma> w"
  shows "winning_strategy p \<sigma> v0"
proof
  fix P assume "vmc_path G P v0 p \<sigma>"
  then interpret vmc_path G P v0 p \<sigma> .
  have "\<not>deadend v0" using \<open>v0\<rightarrow>w\<close> by blast
  then interpret vmc_path_no_deadend G P v0 p \<sigma> by unfold_locales
  have "winning_path p (ltl P)"
    using \<sigma>(2)[unfolded winning_strategy_def] v0(1,2) v0_conforms vmc_path_ltl by presburger
  thus "winning_path p P" using winning_path_LCons by (metis P_LCons Ptl_not_null)
qed

end \<comment> \<open>context ParityGame\<close>

end
