section "LTL integration"
theory PromelaLTL
imports
  Promela
  LTL.LTL
begin

text \<open>We have a semantic engine for Promela. But we need to have 
an integration with LTL -- more specificly, we must know when a proposition
is true in a global state. This is achieved in this theory.\<close>

subsection \<open>LTL optimization\<close>

text \<open>For efficiency reasons, we do not store the whole @{typ expr} on the labels
of a system automaton, but @{typ nat} instead. This index then is used to look up the
corresponding @{typ expr}.\<close>

type_synonym APs = "expr iarray"

primrec ltlc_aps_list' :: "'a ltlc \<Rightarrow> 'a list \<Rightarrow> 'a list"
where
  "ltlc_aps_list' True_ltlc l = l"
| "ltlc_aps_list' False_ltlc l = l"
| "ltlc_aps_list' (Prop_ltlc p) l = (if List.member l p then l else p#l)"
| "ltlc_aps_list' (Not_ltlc x) l = ltlc_aps_list' x l"
| "ltlc_aps_list' (Next_ltlc x) l = ltlc_aps_list' x l"
| "ltlc_aps_list' (Final_ltlc x) l = ltlc_aps_list' x l"
| "ltlc_aps_list' (Global_ltlc x) l = ltlc_aps_list' x l"
| "ltlc_aps_list' (And_ltlc x y) l = ltlc_aps_list' y (ltlc_aps_list' x l)"
| "ltlc_aps_list' (Or_ltlc x y) l = ltlc_aps_list' y (ltlc_aps_list' x l)"
| "ltlc_aps_list' (Implies_ltlc x y) l = ltlc_aps_list' y (ltlc_aps_list' x l)"
| "ltlc_aps_list' (Until_ltlc x y) l = ltlc_aps_list' y (ltlc_aps_list' x l)"
| "ltlc_aps_list' (Release_ltlc x y) l = ltlc_aps_list' y (ltlc_aps_list' x l)"
| "ltlc_aps_list' (WeakUntil_ltlc x y) l = ltlc_aps_list' y (ltlc_aps_list' x l)"
| "ltlc_aps_list' (StrongRelease_ltlc x y) l = ltlc_aps_list' y (ltlc_aps_list' x l)"

lemma ltlc_aps_list'_correct:
  "set (ltlc_aps_list' \<phi> l) = atoms_ltlc \<phi> \<union> set l"
  by (induct \<phi> arbitrary: l) (auto simp add: in_set_member)

lemma ltlc_aps_list'_distinct:
  "distinct l \<Longrightarrow> distinct (ltlc_aps_list' \<phi> l)"
  by (induct \<phi> arbitrary: l) (auto simp add: in_set_member)

definition ltlc_aps_list :: "'a ltlc \<Rightarrow> 'a list"
where
  "ltlc_aps_list \<phi> = ltlc_aps_list' \<phi> []"

lemma ltlc_aps_list_correct:
  "set (ltlc_aps_list \<phi>) = atoms_ltlc \<phi>"
  unfolding ltlc_aps_list_def
  by (force simp: ltlc_aps_list'_correct)

lemma ltlc_aps_list_distinct:
  "distinct (ltlc_aps_list \<phi>)"
  unfolding ltlc_aps_list_def
  by (auto intro: ltlc_aps_list'_distinct)

primrec idx' :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
  "idx' _ [] _ = None"
| "idx' ctr (x#xs) y = (if x = y then Some ctr else idx' (ctr+1) xs y)"

definition "idx = idx' 0"

lemma idx'_correct:
  assumes "distinct xs"
  shows "idx' ctr xs y = Some n \<longleftrightarrow> n \<ge> ctr \<and> n < length xs + ctr \<and> xs ! (n-ctr) = y"
using assms
proof (induction xs arbitrary: n ctr)
  case (Cons x xs)
  show ?case
  proof (cases "x=y")
    case True with Cons.prems have *: "y \<notin> set xs" by auto
    {
      assume A: "(y#xs)!(n-ctr) = y"
      and less: "ctr \<le> n"
      and length: "n < length (y#xs) + ctr"
      have "n = ctr"
      proof (rule ccontr)
        assume "n \<noteq> ctr" with less have "n-ctr > 0" by auto
        moreover from \<open>n\<noteq>ctr\<close> length have "n-ctr < length(y#xs)" by auto
        ultimately have "(y#xs)!(n-ctr) \<in> set xs" by simp
        with A * show False by auto
      qed
    }
    with True Cons show ?thesis by auto
  next
    case False 
    from Cons have "distinct xs" by simp
    with Cons.IH False have "idx' (Suc ctr) xs y = Some n \<longleftrightarrow> Suc ctr \<le> n \<and> n < length xs + Suc ctr \<and> xs ! (n - Suc ctr) = y"
      by simp
    with False show ?thesis
      apply -
      apply (rule iffI)
      apply clarsimp_all
      done
  qed
qed simp

lemma idx_correct:
  assumes "distinct xs"
  shows "idx xs y = Some n \<longleftrightarrow> n < length xs \<and> xs ! n = y"
  using idx'_correct[OF assms]
  by (simp add: idx_def)

lemma idx_dom:
  assumes "distinct xs"
  shows "dom (idx xs) = set xs"
  by (auto simp add: idx_correct assms in_set_conv_nth)

lemma idx_image_self:
  assumes "distinct xs"
  shows "(the \<circ> idx xs) ` set xs = {..<length xs}"
proof (safe)
  fix x
  assume "x \<in> set xs" with in_set_conv_nth obtain n where n: "n < length xs" "xs ! n = x" by metis
  with idx_correct[OF assms] have "idx xs x = Some n" by simp
  hence "the (idx xs x) = n" by simp
  with n show "(the \<circ> idx xs) x < length xs" by simp
next
  fix n
  assume "n < length xs" 
  moreover with nth_mem have "xs ! n \<in> set xs" by simp
  then obtain x where "xs ! n = x" "x \<in> set xs" by simp_all
  ultimately have "idx xs x = Some n" by (simp add: idx_correct[OF assms])
  hence "the (idx xs x) = n" by simp
  thus "n \<in> (the \<circ> idx xs) ` set xs" 
    using \<open>x \<in> set xs\<close> 
    by auto
qed

lemma idx_ran:
  assumes "distinct xs"
  shows "ran (idx xs) = {..<length xs}"
  using ran_is_image[where M="idx xs"]
  using idx_image_self[OF assms] idx_dom[OF assms]
  by simp

lemma idx_inj_on_dom:
  assumes "distinct xs"
  shows "inj_on (idx xs) (dom (idx xs))"
  by (fastforce simp add: idx_dom assms in_set_conv_nth idx_correct
                intro!: inj_onI)

definition ltl_convert :: "expr ltlc \<Rightarrow> APs \<times> nat ltlc" where
  "ltl_convert \<phi> = (
      let APs = ltlc_aps_list \<phi>;
          \<phi>\<^sub>i = map_ltlc (the \<circ> idx APs) \<phi>
      in (IArray APs, \<phi>\<^sub>i))"

lemma ltl_convert_correct:
  assumes "ltl_convert \<phi> = (APs, \<phi>\<^sub>i)"
  shows "atoms_ltlc \<phi> = set (IArray.list_of APs)" (is "?P1")
  and "atoms_ltlc \<phi>\<^sub>i = {..<IArray.length APs}" (is "?P2")
  and "\<phi>\<^sub>i = map_ltlc (the \<circ> idx (IArray.list_of APs)) \<phi>" (is "?P3")
  and "distinct (IArray.list_of APs)"
proof -
  let ?APs = "IArray.list_of APs"

  from assms have APs_def: "?APs = ltlc_aps_list \<phi>"
    unfolding ltl_convert_def by auto

  with ltlc_aps_list_correct show APs_set: ?P1 by metis

  from assms show ?P3
    unfolding ltl_convert_def
    by auto

  from assms have "atoms_ltlc \<phi>\<^sub>i = (the \<circ> idx ?APs) ` atoms_ltlc \<phi>"
    unfolding ltl_convert_def
    by (auto simp add: ltlc.set_map)
  moreover from APs_def ltlc_aps_list_distinct show "distinct ?APs" by simp
  note idx_image_self[OF this]
  moreover note APs_set
  ultimately show ?P2 by simp
qed

definition prepare 
  :: "_ \<times> (program \<Rightarrow> unit) \<Rightarrow> ast \<Rightarrow> expr ltlc \<Rightarrow> (program \<times> APs \<times> gState) \<times> nat ltlc" 
  where
  "prepare cfg ast \<phi> \<equiv>
      let 
         (prog,g\<^sub>0) = Promela.setUp ast;
         (APs,\<phi>\<^sub>i) = PromelaLTL.ltl_convert \<phi>
      in 
         ((prog, APs, g\<^sub>0), \<phi>\<^sub>i)"

lemma prepare_instrument[code]:
  "prepare cfg ast \<phi> \<equiv> 
    let
         (_,printF) = cfg;
         _ = PromelaStatistics.start (); 
         (prog,g\<^sub>0) = Promela.setUp ast;
         _ = printF prog;
         (APs,\<phi>\<^sub>i) = PromelaLTL.ltl_convert \<phi>;
         _ = PromelaStatistics.stop_timer ()
      in 
         ((prog, APs, g\<^sub>0), \<phi>\<^sub>i)"
  by (simp add: prepare_def)

export_code prepare checking SML

subsection \<open>Language of a Promela program\<close>

definition propValid :: "APs \<Rightarrow> gState \<Rightarrow> nat \<Rightarrow> bool" where
  "propValid APs g i \<longleftrightarrow> i < IArray.length APs \<and> exprArith g emptyProc (APs!!i) \<noteq> 0"

definition promela_E :: "program \<Rightarrow> (gState \<times> gState) set"
  \<comment> \<open>Transition relation of a promela program\<close>
where
  "promela_E prog \<equiv> {(g,g'). g' \<in> ls.\<alpha> (nexts_code prog g)}"

definition promela_E_ltl :: "program \<times> APs \<Rightarrow> (gState \<times> gState) set" where
  "promela_E_ltl = promela_E \<circ> fst"

definition promela_is_run' :: "program \<times> gState \<Rightarrow> gState word \<Rightarrow> bool"
  \<comment> \<open>Predicate defining runs of promela programs\<close>
where
  "promela_is_run' progg r \<equiv> 
      let (prog,g\<^sub>0)=progg in 
           r 0 = g\<^sub>0 
        \<and> (\<forall>i. r (Suc i) \<in> ls.\<alpha> (nexts_code prog (r i)))"

abbreviation "promela_is_run \<equiv> promela_is_run' \<circ> setUp"

definition promela_is_run_ltl :: "program \<times> APs \<times> gState \<Rightarrow> gState word \<Rightarrow> bool"
where 
  "promela_is_run_ltl promg r \<equiv> let (prog,APs,g) = promg in promela_is_run' (prog,g) r"

definition promela_props :: "gState \<Rightarrow> expr set" 
where
  "promela_props g = {e. exprArith g emptyProc e \<noteq> 0}"

definition promela_props_ltl :: "APs \<Rightarrow> gState \<Rightarrow> nat set"
where
  "promela_props_ltl APs g \<equiv> Collect (propValid APs g)"

definition promela_language :: "ast \<Rightarrow> expr set word set" where
  "promela_language ast \<equiv> {promela_props \<circ> r | r. promela_is_run ast r}"

definition promela_language_ltl :: "program \<times> APs \<times> gState \<Rightarrow> nat set word set" where
  "promela_language_ltl promg \<equiv> let (prog,APs,g) = promg in 
                    {promela_props_ltl APs \<circ> r | r. promela_is_run_ltl promg r}"

lemma promela_props_ltl_map_aprops:
  assumes "ltl_convert \<phi> = (APs,\<phi>\<^sub>i)"
  shows "promela_props_ltl APs = 
          map_props (idx (IArray.list_of APs)) \<circ> promela_props"
proof -
  let ?APs = "IArray.list_of APs"
  let ?idx = "idx ?APs"

  from ltl_convert_correct assms have D: "distinct ?APs" by simp

  show ?thesis
  proof (intro ext set_eqI iffI)
    fix g i
    assume "i \<in> promela_props_ltl APs g"
    hence "propValid APs g i" by (simp add: promela_props_ltl_def)
    hence l: "i < IArray.length APs" "exprArith g emptyProc (APs!!i) \<noteq> 0" 
      by (simp_all add: propValid_def)
    hence "APs!!i \<in> promela_props g" by (simp add: promela_props_def)
    moreover from idx_correct l D have "?idx (APs!!i) = Some i" by fastforce
    ultimately show "i \<in> (map_props ?idx \<circ> promela_props) g"
      unfolding o_def map_props_def
      by blast
  next
    fix g i
    assume "i \<in> (map_props ?idx \<circ> promela_props) g"
    then obtain p where p_def: "p \<in> promela_props g" "?idx p = Some i" 
      unfolding map_props_def o_def 
      by auto
    hence expr: "exprArith g emptyProc p \<noteq> 0" by (simp add: promela_props_def)
  
    from D p_def have "i < IArray.length APs" "APs !! i = p"
      using idx_correct by fastforce+
    with expr have "propValid APs g i" by (simp add: propValid_def)
    thus "i \<in> promela_props_ltl APs g"
      by (simp add: promela_props_ltl_def)
  qed
qed

lemma promela_run_in_language_iff:
  assumes conv: "ltl_convert \<phi> = (APs,\<phi>\<^sub>i)"
  shows "promela_props \<circ> \<xi> \<in> language_ltlc \<phi> 
          \<longleftrightarrow> promela_props_ltl APs \<circ> \<xi> \<in> language_ltlc \<phi>\<^sub>i" (is "?L \<longleftrightarrow> ?R")
proof -
  let ?APs = "IArray.list_of APs"

  from conv have D: "distinct ?APs"
    by (simp add: ltl_convert_correct)
  with conv have APs: "atoms_ltlc \<phi> \<subseteq> dom (idx ?APs)"
    by (simp add: idx_dom ltl_convert_correct)

  note map_semantics = map_semantics_ltlc[OF idx_inj_on_dom[OF D] APs]
                       promela_props_ltl_map_aprops[OF conv]
                       ltl_convert_correct[OF conv]

  have "?L \<longleftrightarrow> (promela_props \<circ> \<xi>) \<Turnstile>\<^sub>c \<phi>" by (simp add: language_ltlc_def)
  also have "... \<longleftrightarrow> (promela_props_ltl APs \<circ> \<xi>) \<Turnstile>\<^sub>c \<phi>\<^sub>i"
    using map_semantics
    by (simp add: o_assoc)
  also have "... \<longleftrightarrow> ?R"
    by (simp add: language_ltlc_def)
  finally show ?thesis .
qed

lemma promela_language_sub_iff:
  assumes conv: "ltl_convert \<phi> = (APs,\<phi>\<^sub>i)"
  and setUp: "setUp ast = (prog,g)"
  shows "promela_language_ltl (prog,APs,g) \<subseteq> language_ltlc \<phi>\<^sub>i \<longleftrightarrow> promela_language ast \<subseteq> language_ltlc \<phi>"
  using promela_run_in_language_iff[OF conv] setUp
  by (auto simp add: promela_language_ltl_def promela_language_def promela_is_run_ltl_def)


(* from PromelaDatastructures *)
hide_const (open) abort abortv 
                  err errv
                  usc
                  warn the_warn with_warn

hide_const (open) idx idx'
end
